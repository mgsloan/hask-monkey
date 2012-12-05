{-# LANGUAGE TupleSections, LambdaCase, Rank2Types #-}
import ActiveHs.Simple
import Control.Applicative (Applicative, (<$>))
import Control.Comonad     (extract)
import Control.Lens
import Control.Monad       (replicateM)
import Data.Data           (Data, Typeable)
import Data.Data.Lens
import Data.Function       (on)
import Data.IORef
import Data.Generics       (extT, gmapT)
import Data.List           (sort, group, subsequences)
import Data.Maybe          (fromMaybe)
import System.Directory    (removeFile)
import Language.Haskell.Exts
import qualified Language.Haskell.Interpreter as Hint
import System.FilePath     (takeBaseName)
import System.IO           (openTempFile, hPutStr, hFlush, stdout, hClose)
import qualified Data.Map as M
import Debug.Trace (trace)

debug x = trace (show x) x

type TypeCache = M.Map (Type, Type) (Either String Type)

main = do
-- Get file for temporary module
  (monkeyHsFile, monkeyHandle) <- openTempFile "." "Monkey.hs"
  let monkeyModule = takeBaseName monkeyHsFile
  hPutStr monkeyHandle $ monkeyCode monkeyModule
  hClose monkeyHandle

-- Run ActiveHs server
  chan <- startGHCiServer ["."] putStrLn (return . const ())
  let interp = interpret chan monkeyModule
  interp setExts

  putStrLn "hask-monkey, version 0.0.1"
  putStrLn ""
  putStrLn "Enter expressions to speculate on"
  putStrLn "---------------------------------"
  putStrLn ""

  let loop = prompt ":t " >>= \case

        "" -> return []

        expr -> do
          result <- interp $ exprType expr
          case result of

            Right ty -> do
              let ty' = cannonAlpha ty
              putStrLn $ prettyPrint ty
              ((expr, ty') :) <$> loop

            Left m -> do
              print m
              loop
  
  seeds <- loop

-- Use information available to Template Haskell to see if there's a chance of
-- the constraints being inhabited.
  checkConstraints <- memoizeIO $ \t -> (t,) $ do
    let thCode = "$(checkConstraints =<< [t| " ++ prettyPrint t ++ " |] )"
    check <- interp $ Hint.interpret thCode ""
    return $ case check of
      (Left err) -> Left . ("While checking constraints "++) $ show err
      (Right "") -> Right t
      (Right err) -> Left $ "" ++ err

-- Gets the type and checks that it might be inhabited.
  getType <- memoizeIO $ \(ts, e) -> (ts,) $ do
    resultType <- interp $ exprType e
    case resultType of
      (Left err) -> return . Left $ show err
      (Right t) -> checkConstraints t

  putStrLn ""
  putStrLn "Results of speculation:"

  let process exprs = mapM (\i@(_,e) -> (e,) <$> getType i)
                    . map (\[(le, lt), (re, rt)] -> ((lt, rt), "(" ++ le ++ ") (" ++ re ++ ")"))
                    $ sequence [exprs, exprs]

  results <- process seeds

  mapM_ (\(e, t) -> print $ e ++ "\n :: " ++ either id prettyPrint t) results

  removeFile monkeyHsFile


prompt :: String -> IO String
prompt str = do
  putStr ":t "
  hFlush stdout
  getLine

-- Goes in the "monkey.hs" tempfile
monkeyCode :: String -> String
monkeyCode monkeyModule = unlines
  [ "module " ++ monkeyModule ++ " where"
  , "import Prelude"
  , "import Control.Applicative"
  , "import Control.Lens"
  , "import THCode"
  ]

memoizeIO :: Ord k => (a -> (k, IO b)) -> IO (a -> IO b)
memoizeIO f = do
  ref <- newIORef M.empty
  return $ \a -> do
    let (k, v) = f a
    mp <- readIORef ref
    case M.lookup k mp of
      Just x -> return x
      Nothing -> do
        x <- v
        writeIORef ref (M.insert k x mp)
        return x

-------------------------------------------------------------------------------
-- haskell-src-exts utilities
-------------------------------------------------------------------------------

cannonAlpha :: Type -> Type
cannonAlpha = substitute isVar (flip zip $ map (TyVar . Ident) alphas) . cannonTy
 where
  isVar (TyVar _) = True
  isVar _ = False

  -- Excel column names
  alphas = tail $ [0..] >>= flip replicateM ['a'..'z']

cannonTy (TyForall tvs ctx t) = TyForall (sort <$> tvs) (sort $ map cannonAsst ctx) $ cannonTy t
cannonTy (TyTuple b ts) = TyTuple b (cannonTy <$> ts)
cannonTy x = gmapT (id `extT` cannonTy) x

cannonAsst :: Asst -> Asst
cannonAsst (ClassA n ts) = ClassA n $ map cannonTy ts
cannonAsst (InfixA l n r) = InfixA (cannonTy l) n (cannonTy r)
cannonAsst (IParam n t) = IParam n $ cannonTy t
cannonAsst (EqualP l r)
  | l > r     = EqualP (cannonTy r) (cannonTy l)
  | otherwise = EqualP (cannonTy l) (cannonTy r)

parseType' :: String -> Type
parseType' = fromParseResult . parseTypeWithMode parseMode

-- | Parse mode with all extensions and no fixities.
parseMode :: ParseMode
parseMode = ParseMode
  { parseFilename = ""
  , extensions = glasgowExts
                   ++ [TupleSections, BangPatterns, ViewPatterns]
  , ignoreLinePragmas = False
  , ignoreLanguagePragmas = False
  , fixities = Nothing
  }

-------------------------------------------------------------------------------
-- data / lens utilities
-------------------------------------------------------------------------------

substitute :: (Data a, Data b, Ord b) => (b -> Bool) -> ([b] -> [(b, b)]) -> a -> a
substitute p lf x = over (descendents p) (\v -> fromMaybe v $ M.lookup v rewrites) x
  where
    rewrites = M.fromList . lf . map head . group $ sort (x ^.. descendents p)

descendents :: (Applicative f, Data a, Data b) => (b -> Bool) -> SimpleLensLike f a b 
descendents p f = biplate go
 where
  go x
    | p x = f x
    | otherwise = uniplate go x

-------------------------------------------------------------------------------
-- hint utilities
-------------------------------------------------------------------------------
exprType :: String -> Hint.Interpreter Type
exprType expr = parseType' <$> Hint.typeOf expr

setExts :: Hint.Interpreter ()
setExts = Hint.set [(Hint.:=) Hint.languageExtensions $ filter extFilter Hint.availableExtensions]
 where
  extFilter (Hint.UnknownExtension _) = False
  extFilter x = x `notElem` [Hint.NoImplicitPrelude, Hint.RebindableSyntax]

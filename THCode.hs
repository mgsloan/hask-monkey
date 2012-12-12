module THCode where
import Control.Applicative
import Control.Lens
import Language.Haskell.TH
import Language.Haskell.TH.Lift
import Debug.Trace (trace)

debug x = trace (show x) x

checkConstraints :: Type -> ExpQ
checkConstraints = (lift =<<) . fmap concat . mapM checkCxts . universe
  where
    checkCxts (ForallT _ cxt _) = concat <$> mapM checkCxt cxt
    checkCxts _ = return []

    checkCxt (ClassP n ts) = do
      info <- reify n
      return $ case info of
        (ClassI _ is) | not $ any (checkInstance ts) is -> pprint n ++ " is not implementable; "
        _ -> []
    checkCxt _ = return []

    checkInstance ts (InstanceD _ t _) = all (uncurry checkType) $ zip (tail $ deApps t) ts

    checkType l r = eqOrVar (head (deApps l)) (head (deApps r))

    eqOrVar l r        | l == r = True
    eqOrVar l (VarT _)          = True
    eqOrVar l _                 = False

    deApps = go
      where
        go (AppT l r) = r : deApps l
        go t = [t]

{-
    checkType (AppT a b) (AppT c d) = checkType a c && checkType b d
    checkType (SigT l _) r = checkType l r
    checkType l (SigT r _) = checkType l r
    checkType l@(TupleT _) r@(TupleT _) = l == r
    checkType   (TupleT _) _            = False
    checkType l@(UnboxedTupleT _) r@(UnboxedTupleT _) = l == r
    checkType l@(ConT _)          r@(ConT _) = l == r
    checkType ArrowT 
    checkType _ _ = True
-}

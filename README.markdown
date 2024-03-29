This is an early version of hask-monkey.  Hask-monkey is a tool for exploring
which types are reachable from just using function application with a user-
provided set of functions.  As the name "*-monkey" suggests, this is done
quite stupidly by just repeatedly asking GHC for types.  Currently, this
search only consists of one iteration.

A practical example of this would be figuring out if you can derive
"unsafeCoerce" from a library that implements some of its functions in terms of
it.  In other words, attempting to see if your usage of "unsafeCoerce" was
valid or not.  This use-case was the inspiration for this, however a good
implementation would also be useful for type-driven code completion.


TODO:

  * Improve ruling out types due to clearly uninhabited constraints
    (will always just be sound and not complete)

  * Replace expressions with single variables, that use "undefined :: T"

  * See if tupling the entire generation yields a faster result

  * Options to disable ruling out types based on uninhabited constraints

  * Options for an upper bound on the size of the resulting types


Current output looks like:
```
hask-monkey, version 0.0.1

Enter expressions to speculate on
---------------------------------

:t (+)
  (Num a) => a -> a -> a
:t 1
  (Num a) => a
:t 

Results of speculation:

((+)) ((+))
  :: GHC.Num.Num is not implementable;

((+)) (1))
  ::   (Num a) => a -> a

(1) ((+))
  ::   (Num ((a -> a -> a) -> t), Num a) => t

(1) (1)
  ::   (Num (a -> t), Num a) => t

```

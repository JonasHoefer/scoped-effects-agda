module Free.Instances where

open import Free using (monad; functor)

instance
  freeFunctor = functor
  freeMonad = monad

module Prog.Instances where

open import Prog using (functor; monad)

instance
  progFunctor = functor
  progMonad   = monad

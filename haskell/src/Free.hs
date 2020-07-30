module Free where

import           Control.Monad (ap)
import           Syntax

data Free h a = Pure a
              | Impure (h (Free h) a)

instance (Syntax h) => Functor (Free h) where
  fmap f = (>>= pure . f)

instance (Syntax h) => Applicative (Free h) where
  pure = return

  (<*>) = ap

instance (Syntax h) => Monad (Free h) where
  return = Pure

  Pure x >>= k = k x
  Impure ha >>= k = Impure (emap (>>= k) ha)

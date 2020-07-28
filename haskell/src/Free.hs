{-# LANGUAGE DeriveFunctor #-}

module Free where

import Control.Monad (ap)

data Free f a = Pure a | Impure (f (Free f a)) deriving (Functor)

instance (Functor f) => Applicative (Free f) where
  pure = return

  (<*>) = ap

instance (Functor f) => Monad (Free f) where
  return = Pure

  Pure x    >>= k = k x
  Impure fa >>= k = Impure ((>>= k) <$> fa)

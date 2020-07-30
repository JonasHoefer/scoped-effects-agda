{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}

module Effect.Void where

import           Free
import           Injectable
import           Effect.HigherOrder.Lift

data Void a
  deriving (Functor)

type HVoid = Lift Void

run :: Free HVoid a -> a
run (Pure x) = x

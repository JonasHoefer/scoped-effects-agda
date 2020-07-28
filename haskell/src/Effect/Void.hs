{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}

module Effect.Void where

import Free
import Injectable

data Void a deriving (Functor)

run :: Free Void a -> a
run (Pure x)   = x

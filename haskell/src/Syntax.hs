{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}

module Syntax where

import Control.Monad

-- natural transformation
type f ~> g = forall x. f x -> g x

class HFunctor h where
  hmap :: (Functor f, Functor g) => f ~> g -> h f ~> h g

type Handler s m n = forall x. s (m x) -> n (s x)

class HFunctor h => Syntax h where
  emap :: (m a -> m b) -> h m a -> h m b
  weave :: (Monad m, Monad n, Functor s) => s () -> Handler s m n -> h m a -> h n (s a)

-- instance (Syntax h, Functor m) => Functor (h m) where
--   fmap = emap . fmap


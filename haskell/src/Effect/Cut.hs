{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}

module Effect.Cut where

import Free (Free(Pure, Impure))
import Injectable ((:<:), (:+:), pattern Other, project, inject)

import Effect.Nondet (Nondet, (?), pattern (:?:), fail, pattern Fail)

import Prelude hiding (fail)

data Cut a = Cutfail' deriving (Show, Eq, Functor)

pattern Cutfail <- (project -> Just Cutfail')
cutfail :: (Cut :<: f) => Free f a
cutfail = inject Cutfail'

cut :: (Nondet :<: f, Cut :<: f, Functor f) => Free f ()
cut = skip ? cutfail

skip :: Monad m => m ()
skip = return ()

runCut :: (Nondet :<: f, Functor f) => Free (Cut :+: f) a -> Free f a
runCut p = go p fail where
  -- | r is the calculation containing the unexplored branches.
  go :: (Nondet :<: f, Functor f) => Free (Cut :+: f) a -> Free f a -> Free f a
  go (Pure x)  r = return x ? r
  go (Fail)    r = r
  go (Cutfail) r = fail
  go (p :?: q) r = go p (go q r)
  go (Other p) r = Impure (flip go r <$> p)

once :: (Nondet :<: f, Functor f) => Free (Cut :+: f) a -> Free f a
once p = runCut $ p >>= \x -> cut >> return x

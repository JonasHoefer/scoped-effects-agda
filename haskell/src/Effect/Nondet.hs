{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}

module Effect.Nondet where

import Free (Free(Pure, Impure))
import Injectable ((:<:), (:+:), pattern Other, project, inject)
import Syntax

import Effect.HigherOrder.Lift

import Prelude hiding (fail)
import Control.Monad (join)

data Nondet a = Fail' | Choice' a a deriving (Show, Eq, Functor)

type HNondet = Lift Nondet

pattern Fail <- (project -> Just (Lift Fail'))
fail :: (HNondet :<: f) => Free f a
fail = inject (Lift Fail')

pattern p :?: q <- (project -> Just (Lift (Choice' p q)))
(?) :: (HNondet :<: f) => Free f a -> Free f a -> Free f a
p ? q = inject (Lift (Choice' p q))

runNondet :: Syntax f => Free (HNondet :+: f) a -> Free f [a]
runNondet (Pure x)   = return [x]
runNondet Fail       = return []
runNondet (p :?: q)  = (++) <$> runNondet p <*> runNondet q
runNondet (Other op) = Impure (weave [()] hdl op)
  where hdl :: (Syntax f) => Handler [] (Free (HNondet :+: f)) (Free f)
        hdl = fmap join . mapM runNondet -- correct?

select :: (HNondet :<: f) => [a] -> Free f a
select = foldr ((?) . Pure) fail

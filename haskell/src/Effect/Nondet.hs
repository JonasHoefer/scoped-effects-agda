{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}

module Effect.Nondet where

import Free (Free(Pure, Impure))
import Injectable ((:<:), (:+:), pattern Other, project, inject)

import Prelude hiding (fail)

data Nondet a = Fail' | Choice' a a deriving (Show, Eq, Functor)

pattern Fail <- (project -> Just Fail')
fail :: (Nondet :<: f) => Free f a
fail = inject Fail'

pattern p :?: q <- (project -> Just (Choice' p q))
(?) :: (Nondet :<: f) => Free f a -> Free f a -> Free f a
p ? q = inject (Choice' p q)

runNondet :: Functor f => Free (Nondet :+: f) a -> Free f [a]
runNondet (Pure x)   = return [x]
runNondet (Fail)     = return []
runNondet (p :?: q)  = (++) <$> runNondet p <*> runNondet q
runNondet (Other fa) = Impure (runNondet <$> fa)

select :: (Nondet :<: f) => [a] -> Free f a
select = foldr (?) fail . map Pure

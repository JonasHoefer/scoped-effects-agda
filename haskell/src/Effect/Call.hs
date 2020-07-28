{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}

module Effect.Call where

import Free (Free(Pure, Impure))
import Injectable ((:<:), (:+:), pattern Other, project, inject, upcast)

import Effect.Cut (Cut, runCut)
import Effect.Nondet (Nondet, (?), pattern (:?:), fail, pattern Fail)

import Prelude hiding (fail)
import Debug.Trace

data Call a = BCall' a | ECall' a deriving (Functor)

pattern BCall p <- (project -> Just (BCall' p))
pattern ECall p <- (project -> Just (ECall' p))

call' :: (Call :<: f, Functor f) => Free f a -> Free f a
call' p = do begin ; x <- p ; end ; return x
  where
    begin = inject (BCall' $ return ())
    end   = inject (ECall' $ return ())

runCut' :: (Nondet :<: f, Functor f) => Free (Call :+: Cut :+: f) a -> Free f a
runCut' = runCut . bcall

bcall :: (Nondet :<: f, Functor f) => Free (Call :+: Cut :+: f) a -> Free (Cut :+: f) a
bcall (Pure x)  = return x
bcall (BCall p) = upcast (runCut (ecall p)) >>= bcall
bcall (ECall p) = error "Unexpected ECall!"
bcall (Other f) = Impure (bcall <$> f)

ecall :: (Functor f, Nondet :<: f) => Free (Call :+: Cut :+: f) a -> Free (Cut :+: f) (Free (Call :+: Cut :+: f) a)
ecall (Pure x)  = return $ Pure x
ecall (BCall p) = upcast (runCut (ecall p)) >>= ecall
ecall (ECall p) = return p
ecall (Other f) = Impure (ecall <$> f)

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}

module Effect.State where

import Free
import Syntax
import Injectable

import Effect.HigherOrder.Lift

data State s a = Get' (s -> a) | Put' s a deriving (Functor)

type HState s = Lift (State s)

pattern Get k <- (project -> Just (Lift (Get' k)))
get :: (HState s :<: sig) => Free sig s
get = inject (Lift (Get' return))

pattern Put s k <- (project -> Just (Lift (Put' s k)))
put :: (HState s :<: sig) => s -> Free sig ()
put s = inject (Lift (Put' s (return ())))

runState :: Syntax sig => s -> Free (HState s :+: sig) a -> Free sig (s, a)
runState s (Pure a)   = return (s, a)
runState s (Get k)    = runState s (k s)
runState s (Put s' k) = runState s' k
runState s (Other op) = Impure (weave (s, ()) (uncurry runState) op)

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Free
import Injectable

import Effect.State
import Effect.Void
import Effect.HigherOrder.HExc

decr :: (HState Int :<: sig, HExc () :<: sig) => Free sig ()
decr = get >>= \x -> if x > (0::Int) then put (pred x) else throw ()

tripleDecr :: (HState Int :<: sig, HExc () :<: sig) => Free sig ()
tripleDecr = decr >> catch (decr >> decr) return

globalUpdate :: Either () (Int, ())
globalUpdate = (run . runExc . runState 2) tripleDecr

localUpdate :: (Int, Either () ())
localUpdate = (run . runState 2 . runExc) tripleDecr

main :: IO ()
main = print globalUpdate >> print localUpdate

-- knapsack :: (Nondet :<: f, Functor f) => Integer -> [Integer] -> Free f [Integer]
-- knapsack w vs | w == 0 = return []
--               | w < 0  = fail
--               | w > 0  = do v <- select vs
--                             vs' <- knapsack (w - v) vs
--                             return (v : vs')
--
-- runKnapsack :: IO ()
-- runKnapsack = print . run . runNondet . once $ knapsack 3 [3, 2, 1]
--
-- -- simple Grammar
-- expr :: (Nondet :<: f, Symbol :<: f, Functor f) => Free f Int
-- expr = do i <- term ; symbol '+' ; j <- expr ; return $ i + j
--      ? do i <- term ; return i
--
-- term :: (Nondet :<: f, Symbol :<: f, Functor f) => Free f Int
-- term = do i <- factor ; symbol '*' ; j <- term ; return $ i * j
--      ? do i <- factor ; return i
--
-- factor :: (Nondet :<: f, Symbol :<: f, Functor f) => Free f Int
-- factor = do ds <- some digit ; return $ read ds
--        ? do symbol '(' ; i <- expr ; symbol ')' ; return i
--
-- runSimpleGrammar :: IO ()
-- runSimpleGrammar = print . run . runNondet . parse "2+8*5" $ expr
--
-- -- left factored expr
-- expr1 :: (Nondet :<: f, Symbol :<: f, Functor f) => Free f Int
-- expr1 = do i <- term ; runCut ( do symbol '+' ; cut ; j <- expr ; return $ i + j
--                               ? do return i
--                               )
--
-- -- does not work, because call's scope is not accounted for
-- runOpimizedGrammar :: IO ()
-- runOpimizedGrammar = print . run . runNondet . parse "1" $ expr1
--
-- -- with scope syntax
-- expr2 :: (Nondet :<: f, Symbol :<: f, Functor f, Cut :<: f, Call :<: f) => Free f Int
-- expr2 = do i <- term ; call' ( do symbol '+' ; cut ; j <- expr ; return $ i + j
--                              ? do return i
--                              )
--
-- main :: IO ()
-- main = print . run . runNondet . runCut' . parse "1" $ expr2

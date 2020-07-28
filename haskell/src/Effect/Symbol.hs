{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}

module Effect.Symbol where

import Free (Free(Pure, Impure))
import Injectable ((:<:), (:+:), pattern Other, project, inject)

import Effect.Nondet (Nondet, (?), pattern (:?:), fail, pattern Fail)

import Prelude hiding (fail)

data Symbol a = Symbol' Char (Char -> a) deriving (Functor)

pattern Symbol c k <- (project -> Just (Symbol' c k))
symbol :: (Symbol :<: f, Functor f) => Char -> Free f Char
symbol c = inject (Symbol' c return)

digit :: (Nondet :<: f, Symbol :<: f, Functor f) => Free f Char
digit = foldr (?) fail $ symbol <$> ['0' .. '9']

some, many :: (Nondet :<: f, Functor f) => Free f a -> Free f [a]
many p = some p ? return []
some p = (:) <$> p <*> many p

parse :: (Nondet :<: f, Functor f) => String -> Free (Symbol :+: f) a -> Free f a
parse []     (Pure a)     = return a
parse (x:xs) (Pure a)     = fail
parse []     (Symbol c k) = fail
parse (x:xs) (Symbol c k) | x == c    = parse xs (k x)
                          | otherwise = fail
parse xs     (Other f)    = Impure (parse xs <$> f)

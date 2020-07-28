{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}

module Injectable ((:+:), pattern Other, (:<:), inject, project, upcast) where

import Free (Free(Pure, Impure))

infixr :+:
data (f :+: g) a = Inl (f a) | Inr (g a)

pattern Other s = Impure (Inr s)

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (Inl fa) = Inl $ fmap f fa
  fmap f (Inr ga) = Inr $ fmap f ga

class sub :<: sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance {-# OVERLAPPABLE #-} (Functor f, Functor g) => f :<: (f :+: g) where
  inj = Inl

  prj (Inl a) = Just a
  prj _       = Nothing

instance {-# OVERLAPPABLE #-} (Functor h, f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj

  prj (Inr ga) = prj ga
  prj _        = Nothing

inject :: (f :<: g) => f (Free g a) -> Free g a
inject = Impure . inj

project :: (f :<: g) => Free g a -> Maybe (f (Free g a))
project (Impure x) = prj x
project _          = Nothing

upcast :: (Functor f, Functor g) => Free g a -> Free (f :+: g) a
upcast (Pure x)   = return x
upcast (Impure g) = Impure (Inr $ upcast <$> g)

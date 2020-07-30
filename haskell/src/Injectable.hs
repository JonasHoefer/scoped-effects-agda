{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}

module Injectable ((:+:), pattern Other, (:<:), inject, project, upcast) where

import           Free (Free(Pure, Impure))
import           Syntax

--------------------------------------------------------------------------------
-- Functor Coproduct                                                          --
--------------------------------------------------------------------------------
infixr :+:

data (f :+:  g) (m :: * -> *) a = Inl (f m a)
                                | Inr (g m a)

pattern Other s = Impure (Inr s)

instance (HFunctor f, HFunctor g) => HFunctor (f :+: g) where
  hmap t (Inl op) = Inl (hmap t op)
  hmap t (Inr op) = Inr (hmap t op)

instance (Syntax f, Syntax g) => Syntax (f :+: g) where
  emap f (Inl op) = Inl (emap f op)
  emap f (Inr op) = Inr (emap f op)

  weave s hdl (Inl op) = Inl (weave s hdl op)
  weave s hdl (Inr op) = Inr (weave s hdl op)

--------------------------------------------------------------------------------
-- Injectable                                                                 --
--------------------------------------------------------------------------------
class (Syntax sub, Syntax sup) => sub :<:  sup where
  inj :: sub m a -> sup m a
  prj :: sup m a -> Maybe (sub m a)

instance {-# OVERLAPPABLE #-}(Syntax f, Syntax g) => f :<: (f :+: g) where
  inj = Inl

  prj (Inl a) = Just a
  prj _ = Nothing

instance {-# OVERLAPPABLE #-}(Syntax h, f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj

  prj (Inr ga) = prj ga
  prj _ = Nothing

inject :: (f :<: g) => f (Free g) a -> Free g a
inject = Impure . inj

project :: (f :<: g) => Free g a -> Maybe (f (Free g) a)
project (Impure x) = prj x
project _ = Nothing

upcast :: (Syntax f, Syntax g) => Free g a -> Free (f :+: g) a
upcast (Pure x) = return x
upcast (Impure g) = Impure (Inr $ hmap upcast g)

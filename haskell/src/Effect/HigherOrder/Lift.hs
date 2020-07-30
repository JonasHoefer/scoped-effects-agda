module Effect.HigherOrder.Lift where

import           Data.Functor
import           Syntax

newtype Lift sig m a = Lift (sig (m a))

instance Functor sig => HFunctor (Lift sig) where
  hmap t (Lift op) = Lift (fmap t op)

instance Functor sig => Syntax (Lift sig) where
  emap f (Lift op) = Lift (fmap f op)

  weave s hdl (Lift op) = Lift (fmap (\p -> hdl (p <$ s)) op)

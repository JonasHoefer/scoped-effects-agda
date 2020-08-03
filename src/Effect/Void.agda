module Effect.Void where

open import Data.Empty using (⊥)

open import Container  using (Container; _▷_)
open import Free       using (Free; pure)

-- The empty effect.
Void : Container
Void = ⊥ ▷ λ()

run : {A : Set} → Free Void A → A
run (pure x) = x

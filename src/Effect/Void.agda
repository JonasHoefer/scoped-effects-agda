module Effect.Void where

open import Data.Empty using (⊥)

open import Container  using (Container; _▷_)
open import Free       using (Free; pure)

-- The empty effect.
void : Container
void = ⊥ ▷ λ()

run : {A : Set} → Free void A → A
run (pure x) = x
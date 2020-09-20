module Effect.Exc where

open import Function     using (_∘_)
open import Level        using (Level)

open import Data.Unit    using (⊤; tt)
open import Data.Empty   using (⊥)
open import Data.List    using (List; _∷_)
open import Data.Product using (_,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)

open import Container    using (Container; _▷_)
open import Free

private
  variable
    A : Set
    ops : List Container

data Shape (E : Set) : Set where
  throwˢ : E → Shape E

pattern Throw e pf = impure (inj₁ (throwˢ e) , pf)

Exc : Set → Container
Exc E = Shape E ▷ λ _ → ⊥

runExc : ∀ {E} → Free (Exc E ∷ ops) A → Free ops (E ⊎ A)
runExc (pure x)       = pure (inj₂ x)
runExc (Throw e pf)   = pure (inj₁ e)
runExc (Other s pf) = impure (s , runExc ∘ pf)

throw : ∀ {E} → {@(tactic eff) _ : Exc E ∈ ops } → E → Free ops A
throw e = op (throwˢ e , λ())

module Effect.Reader where

open import Function     using (_∘_; _$_)
open import Size         using (Size; ↑_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ using (_>>=_; _>>_)

open import Data.List      using (List; _∷_; [])
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)

open import Container    using (Container; ⟦_⟧; _▷_; _⊕_)
open import Free
open import Free.Instances

Reader : Set → Container
Reader Γ = ⊤ ▷ λ tt → Γ

private
  variable
    F : List Container
    A Γ : Set

runReader : Γ → Free (Reader Γ ∷ F) A → Free F A
runReader γ (pure x)                = pure x
runReader γ (impure (inj₁ tt , pf)) = runReader γ (pf γ)
runReader γ (impure (inj₂ s  , pf)) = impure (s , runReader γ ∘ pf)

ask : {@(tactic eff) _ : Reader Γ ∈ F} → Free F Γ
ask = op (tt , pure)

local : {i : Size} {@(tactic eff) _ : Reader Γ ∈ F} → (Γ → Γ) → Free F A {i} → Free F A
local f (pure x)     = op (tt , (λ γ → pure x))
local f c@(impure _) with prj {Reader _} c
... | nothing        = c
... | just (tt , pf) = op (tt , λ γ → local f $ pf (f γ))

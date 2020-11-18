{-# OPTIONS --overlapping-instances #-}

module Knapsack where

open import Function                              using (_$_)
open import Size                                  using (Size; ↑_; Size<_)

open import Category.Monad                        using (RawMonad)
open        RawMonad ⦃...⦄                        using (_>>=_; _>>_)

open import Data.Bool                             using (Bool; true; false; if_then_else_)
open import Data.List                             using (List; _∷_; [])

open import Container                             using (Container)
open import Free
open import Free.Instances

open import Effect.Cut                            using (once)
open import Effect.Nondet                         using (Nondet; solutions; select; fail)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-----------------------------------
-- Knapsack example by Wu et al. --
-----------------------------------

-- The function terminates because the weight of the knapsack increases.
-- To convince Agda we have to define a type of non-zero weights.

data ℕ₀ : Size → Set where
  zero : ∀ {i} → ℕ₀ i
  suc₀ : {i : Size} → ℕ₀ i → ℕ₀ (↑ i)

data ℕ : Set where
  one : ℕ
  suc : ℕ → ℕ

_∸_ : {i : Size} → ℕ₀ (↑ i) → ℕ → ℕ₀ i
zero   ∸ y     = zero
suc₀ x ∸ one   = x
suc₀ x ∸ suc y = x ∸ y

_<_ : ∀ {i} → ℕ₀ i → ℕ → Bool
zero   < _     = true
suc₀ x < one   = false
suc₀ x < suc y = x < y

private
  variable
    F : List Container

knapsack : ∀ {i} {@(tactic eff) _ : Nondet ∈ F} → ℕ₀ i → List ℕ → Free F (List ℕ)
knapsack zero       vs = pure []
knapsack w@(suc₀ _) vs = do
    v ← select vs
    vs′ ← if w < v then fail else knapsack (w ∸ v) vs
    pure (v ∷ vs′)

knapsackExample : {@(tactic eff) _ : Nondet ∈ F} → Free F (List ℕ)
knapsackExample = knapsack (suc₀ $ suc₀ $ suc₀ $ zero) (one ∷ suc one ∷ [])

runKnapsack : List (List ℕ)
runKnapsack = run $ solutions $ knapsackExample

knapsackOnce : (run $ solutions $ once knapsackExample) ≡ (one ∷ one ∷ one ∷ []) ∷ []
knapsackOnce = refl

{-# OPTIONS --overlapping-instances #-}

module Knapsack where

open import Function      using (_$_)
open import Size          using (Size; ↑_; Size<_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Bool     using (Bool; true; false; if_then_else_)
open import Data.List     using (List; _∷_; [])

open import Container     using (Container)
open import Free
open import Injectable    using (_⊂_)

open import Effect.Cut    using (once)
open import Effect.Nondet using (nondet; solutions; select; fail)
open import Effect.Void   using (run)

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

knapsack : {F : Container} {i : Size} → ⦃ nondet ⊂ F ⦄ → ℕ₀ i → List ℕ → Free F (List ℕ)
knapsack zero       vs = pure []
knapsack w@(suc₀ _) vs = do
    v ← select vs
    vs′ ← if w < v then fail else knapsack (w ∸ v) vs
    pure (v ∷ vs′)
  where open RawMonad freeMonad hiding (pure)

knapsackExample : {F : Container} → ⦃ nondet ⊂ F ⦄ → Free F (List ℕ)
knapsackExample = knapsack (suc₀ $ suc₀ $ suc₀ $ zero) (one ∷ suc one ∷ [])

runKnapsack : List (List ℕ)
runKnapsack = run $ solutions $ knapsackExample

knapsackOnce : (run $ solutions $ once knapsackExample) ≡ (one ∷ one ∷ one ∷ []) ∷ []
knapsackOnce = refl

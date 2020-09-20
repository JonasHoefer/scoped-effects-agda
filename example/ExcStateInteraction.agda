{-# OPTIONS --overlapping-instances #-}

module ExcStateInteraction where

open import Function using (_$_; flip)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (⊤; tt)

open import Variables
open import Effect
open import Effect.Exc
open import Effect.State
open import Prog
open import Prog.Instances

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)


decr : ⦃ State ℕ ∈ effs ⦄ → ⦃ Exc ⊤ ∈ effs ⦄ → Prog effs ⊤
decr = get >>= λ where
  0       → throw tt
  (suc n) → put n

tripleDecr : ⦃ State ℕ ∈ effs ⦄ → ⦃ Exc ⊤ ∈ effs ⦄ → Prog effs ⊤
tripleDecr = decr >> (decr >> decr catch pure)

localUpdate : (run $ runExc $ flip runState 2 tripleDecr) ≡ inj₂ (1 , tt)
localUpdate = refl

globalUpdate : (run $ flip runState 2 $ runExc tripleDecr) ≡ (0 , inj₂ tt)
globalUpdate = refl

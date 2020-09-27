{-# OPTIONS --overlapping-instances #-}

module NondetStateInteraction where

open import Function using (_$_; _∘_; flip)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (⊤; tt)

open import Variables
open import Effect
open import Effect.Exc
open import Effect.State
open import Effect.Nondet
open import Prog
open import Prog.Instances

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)


incr : ⦃ State ℕ ∈ effs ⦄ → Prog effs ⊤
incr = get >>= put ∘ suc

foo : ⦃ State ℕ ∈ effs ⦄ → ⦃ Exc ⊤ ∈ effs ⦄ → ⦃ Nondet ∈ effs ⦄ → Prog effs ℕ
foo = ((var tt ⁇ var tt) catch λ _ → throw tt) >>= λ (tt) → (get ⁇ incr >> get)

runFoo : ⊤ ⊎ (List (ℕ × ℕ))
runFoo = run $ runExc $ runNondet $ runState foo 0

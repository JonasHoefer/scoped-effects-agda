module State where

open import Function using (_$_; _∘_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (⊤; tt)

open import Variables
open import Effect
open import Effect.State
open import Prog
open import Prog.Instances

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)


tick : ⦃ State ℕ ∈ effs ⦄ → Prog effs ⊤
tick = get >>= put ∘ suc

testTick : (run $ runState (tick >> tick) 0) ≡ (2 , tt)
testTick = refl

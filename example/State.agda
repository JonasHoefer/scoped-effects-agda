module State where

open import Function using (_$_; _∘_; const)

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

testLocal : ⦃ State ℕ ∈ effs ⦄ → Prog effs ℕ
testLocal = do
  put 1
  tick
  localX ← local (const 41) (get >>= put ∘ suc >> get)
  tick
  var localX

runTestLocal : (run $ runState testLocal 0) ≡ (3 , 42)
runTestLocal = refl

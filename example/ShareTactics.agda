module ShareTactics where

open import Function using (_$_; flip; _∘_; case_of_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.MList
open import Data.Nat using (ℕ; _+_; _≤?_)
open import Data.Normalform

open import Variables
open import Effect.Nondet renaming (_⁇_ to _⁇′_)
open import Effect.Share renaming (share to share′)
open import Effect.Share.Shareable
open import Effect.State
open import Prog
open import Prog.Instances

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Tactic.Eff

share :
  { @(tactic eff) state : State SID ∈ effs } →
  { @(tactic eff) share : Share     ∈ effs } →
  ⦃ Shareable effs A ⦄ → Prog effs A → Prog effs (Prog effs A)
share {state = state} {share = share} p = share′ ⦃ state ⦄ ⦃ share ⦄ p

_⁇_ : { @(tactic eff) nondet : Nondet ∈ effs } → Prog effs A → Prog effs A → Prog effs A
_⁇_ {nondet = nondet} p q = _⁇′_ ⦃ nondet ⦄ p q

doubleShare :
  { @(tactic eff) _ : State SID ∈ effs } →
  { @(tactic eff) _ : Share ∈ effs     } →
  { @(tactic eff) _ : Nondet ∈ effs    } → Prog effs ℕ
doubleShare = do
  x ← share  (pure 0 ⁇ pure 1)
  y ← share (x ⁇ pure 1)
  ⦇ y + y ⦈

runDoubleShare : runCTC doubleShare ≡ 0 ∷ 2 ∷ 2 ∷ []
runDoubleShare = refl

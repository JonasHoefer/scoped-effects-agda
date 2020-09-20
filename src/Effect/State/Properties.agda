{-# OPTIONS --overlapping-instances #-}

module Effect.State.Properties where

open import Function using (_$_; _∘_; id; const)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Variables
open import Effect
open import Effect.State
open import Prog
open import Prog.Instances
open import Prog.Properties

import      Relation.Binary.PropositionalEquality as Eq
open        Eq using (_≡_; refl; cong; sym; trans)
open        Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

----------------------------------
-- The 4 laws that govern state --
----------------------------------

get-get : ∀ {S A} (k : S → S → Prog (State S ∷ effs) A) →
  runState (get >>= λ s → get >>= λ s′ → k s s′) ≡ runState (get >>= λ s → k s s)
get-get _ = extensionality λ _ → refl

get-put : ∀ {S A} (k : Prog (State S ∷ effs) A) →
  runState (get >>= put >> k) ≡ runState k
get-put _ = extensionality λ _ → refl

put-put : ∀ {S A} {s : S} → (k : Prog (State S ∷ effs) A) →
  runState (put s >> put s >> k) ≡ runState (put s >> k)
put-put _ = extensionality λ _ → refl

put-get : ∀ {S A} {s : S} → (k : S → Prog (State S ∷ effs) A) →
  runState (put s >> get >>= k) ≡ runState (put s >> k s)
put-get _ = extensionality λ _ → refl

{-# OPTIONS --overlapping-instances #-}

module Effect.Share.Properties where

open import Function using (_$_; _∘_; id)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Empty using (⊥-elim)
open import Data.List  using (List; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Normalform
open import Data.Tree

open import Variables
open import Effect
open import Effect.Nondet
open import Effect.State
open import Effect.Share
open import Effect.Share.Shareable
open import Prog
open import Prog.Instances
open import Prog.Properties

import      Relation.Binary.PropositionalEquality as Eq
open        Eq using (_≡_; refl; _≢_; cong; sym; trans)
open        Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


CTC : List Effect
CTC = State SID ∷ Share ∷ Nondet ∷ []

----------------------------------------------------------------------------------------------
-- (unfinished) laws of sharing from "Purely Functional Lazy Non-deterministic Programming" --
----------------------------------------------------------------------------------------------

share-fail : ⦃ _ : Normalform CTC A B ⦄ → ⦃ _ : Shareable CTC A ⦄ →
  runCTC {A} {B} (share fail >>= id) ≡ runCTC fail
share-fail = refl

runCTC′ : ℕ × ℕ → Prog (State SID ∷ Share ∷ Nondet ∷ []) A → List A
runCTC′ id p = run $ runNondet $ runShare $ evalState p id -- normalfrom could produce arbitrary term!

-- It is not possible to prove the following law without extra ssumptions.
-- Because the share operator directly produces state code, it is not possible to differentiate
-- between user written and share code.
-- Complex approach: mark scope using syntax and add assumption that operations outside these scopes
-- are not put or get.
--
-- share-⁇ : ⦃ _ : Normalform CTC A B ⦄ → ⦃ _ : Shareable CTC A ⦄ → (p q : Prog CTC A) →
--   runCTC (share (p ⁇ q) >>= id) ≡ runCTC (share p >>= id ⁇ share q >>= id)
-- share-⁇ p q = begin
--   runCTC (share (p ⁇ q) >>= id)                     ≡⟨ {!!} ⟩
--   runCTC (share (p ⁇ q) >>= id)                     ≡⟨ {!!} ⟩
--   runCTC (share p >>= id ⁇ share q >>= id)          ∎

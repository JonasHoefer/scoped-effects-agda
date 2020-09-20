{-# OPTIONS --overlapping-instances #-}

module Effect.Share.Properties where

open import Function using (_$_; _∘_; id)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

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
open        Eq using (_≡_; refl; cong; sym; trans)
open        Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


CTC : List Effect
CTC = State SID ∷ Share ∷ Nondet ∷ []

share-fail : ⦃ _ : Normalform CTC A B ⦄ → ⦃ _ : Shareable CTC A ⦄ →
  runCurry {A} {B} (share fail >>= id) ≡ runCurry fail
share-fail = refl

-- TODO: Lemma for reasoning modulo ids (runCurry p ≡ runCurry (incrAllIDs p))
-- share-⁇ : ⦃ _ : Normalform CTC A B ⦄ → ⦃ _ : Shareable CTC A ⦄ → (p q : Prog CTC A) →
--   runCurry (share (p ⁇ q) >>= id) ≡ runCurry (share p >>= id ⁇ share q >>= id)
-- share-⁇ p q = begin
--   runCurry (share (p ⁇ q) >>= id)                     ≡⟨ {!!} ⟩
--   runCurry (share (p ⁇ q) >>= id)                     ≡⟨ {!!} ⟩
--   {!!} ∎

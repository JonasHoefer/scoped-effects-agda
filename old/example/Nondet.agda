{-# OPTIONS --overlapping-instances #-}

module Nondet where

open import Function                              using (_$_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ using (_>>=_; _>>_)

open import Data.List                             using (List; _∷_; [])
open import Data.Nat                              using (ℕ; _+_)

open import Container                             using (Container)
open import Free
open import Free.Instances

open import Effect.Nondet                         using (Nondet; solutions; select; _⁇_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

sumTwo : ∀ {F} → {@(tactic eff) _ : Nondet ∈ F} → List ℕ → Free F ℕ
sumTwo xs = do
    x ← select xs
    y ← select xs
    pure (x + y)

testNonDet : List ℕ
testNonDet = run $ solutions $ sumTwo $ 3 ∷ 4 ∷ 7 ∷ []


open import Effect.Catch   using (Catch; _catch_; runCatch)
open import Effect.Exc     using (Exc; throw)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)

test : ⊤ ⊎ List ℕ
test = run $ runCatch $ solutions ((pure 5 ⁇ throw tt) catch (λ _ → pure 42)) -- ??!?!?

{-# OPTIONS --overlapping-instances #-}

module Cut where

open import Function using (_$_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Nat using (ℕ; _+_)

open import Variables
open import Effect
open import Effect.Cut
open import Effect.Nondet
open import Prog
open import Prog.Instances

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)


cutTest : ⦃ Cut ∈ effs ⦄ → ⦃ Nondet ∈ effs ⦄ → Prog effs ℕ
cutTest = pure 1 ⁇ once (pure 2 ⁇ pure 3)

runCutTest : (run $ runNondet $ runCut cutTest) ≡ 1 ∷ 2 ∷ []
runCutTest = refl


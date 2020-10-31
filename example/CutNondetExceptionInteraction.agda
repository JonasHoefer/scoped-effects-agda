{-# OPTIONS --overlapping-instances #-}

module CutNondetExceptionInteraction where

open import Function using (_$_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (⊤; tt)

open import Variables
open import Effect
open import Effect.Cut
open import Effect.Exc
open import Effect.Nondet
open import Prog
open import Prog.Instances

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)


cutThrow : ⦃ Cut ∈ effs ⦄ → ⦃ Nondet ∈ effs ⦄ → ⦃ Exc ⊤ ∈ effs ⦄ → Prog effs ℕ
cutThrow =  pure 1 ⁇ (once (var 2 ⁇ throw tt) catch λ _ → pure 42)

runCutThrowGlobal : (run $ runExc $ runNondet $ runCut cutThrow) ≡ inj₂ (1 ∷ 2 ∷ [])
runCutThrowGlobal = refl

runCutThrowLocal : (run $ runNondet $ runExc $ runCut cutThrow) ≡ inj₂ 1 ∷ inj₂ 2 ∷ []
runCutThrowLocal = refl

runCutThrowGlobal2 : (run $ runExc $ runCut″ cutThrow) ≡ inj₂ (1 ∷ 2 ∷ [])
runCutThrowGlobal2 = refl

runCutThrowLocal2 : (run $ runCut″ $ runExc cutThrow) ≡ inj₂ 1 ∷ inj₂ 2 ∷ []
runCutThrowLocal2 = refl

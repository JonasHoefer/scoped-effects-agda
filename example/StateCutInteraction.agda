{-# OPTIONS --overlapping-instances #-}

module StateCutInteraction where

open import Function       using (id; _$_; flip; case_of_; _∘_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (_++_)
open import Data.Maybe using (Maybe; nothing; just; maybe′; fromMaybe)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (map₂) renaming (map to ⊎-map)
open import Data.Unit using (⊤; tt)

open import Variables
open import Effect
open import Effect.Cut
open import Effect.Nondet hiding (hdl)
open import Effect.State
open import Prog
open import Prog.Instances

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)


cutLocal cutLocal′ : ⦃ Nondet ∈ effs ⦄ → ⦃ Cut ∈ effs ⦄ → ⦃ State ℕ ∈ effs ⦄ → Prog effs ℕ
cutLocal = pure 1 ⁇ (once (local id (pure 3 ⁇ pure 4))) ⁇ pure 10
cutLocal′ = (local id (pure 3 ⁇ pure 4) ⁇ pure 5) >>= λ x → cut >> pure x

runCutLocal : (run $ flip evalState 0 $ runCut″ cutLocal) ≡ 1 ∷ 3 ∷ 10 ∷ []
runCutLocal = refl

runCutLocal′ : (run $ flip evalState 0 $ runCut″ cutLocal′) ≡ 3 ∷ []
runCutLocal′ = refl

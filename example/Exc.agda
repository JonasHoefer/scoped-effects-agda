{-# OPTIONS --overlapping-instances #-}

module Exc where

open import Function using (_$_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (⊤; tt)

open import Variables
open import Effect
open import Effect.Exc
open import Prog
open import Prog.Instances

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)


runThrow : (run $ runExc $ (var 21 >> throw {A = ℕ} tt)) ≡ inj₁ tt
runThrow = refl

catchTest : ⦃ Exc ⊤ ∈ effs ⦄ → Prog effs ℕ
catchTest = (throw {A = ℕ} tt >> var 41) catch λ _ → pure 42

runCatchTest : (run $ runExc catchTest) ≡ inj₂ 42
runCatchTest = refl

doubleCatch : ⦃ Exc ⊤ ∈ effs ⦄ → Prog effs ℕ
doubleCatch = (var 40 >> throw tt) catch (λ _ → pure 41 >> throw tt) catch (λ _ → pure 42)

runDoubleCatch : (run $ runExc doubleCatch) ≡ inj₂ 42
runDoubleCatch = refl

module Nondet where

open import Function using (_$_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Nat using (ℕ; _+_)

open import Variables
open import Effect
open import Effect.Nondet
open import Prog
open import Prog.Instances

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)


coin : ⦃ Nondet ∈ effs ⦄ → Prog effs ℕ
coin = pure 0 ⁇ pure 1

sumCoins : (run $ runNondet ⦇ coin + coin ⦈) ≡ (0 ∷ 1 ∷ 1 ∷ 2 ∷ [])
sumCoins = refl

-- more tests in Share.agda

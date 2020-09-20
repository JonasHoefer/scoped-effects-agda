module Data.Normalform where

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Bool      using (Bool)
open import Data.Nat       using (ℕ)
open import Data.Unit      using (⊤)

open import Variables
open import Effect
open import Prog
open import Prog.Instances


record Normalform (effs : List Effect) (A B : Set) : Set where
  field
    nf : A → Prog effs B

  infix 10 !_
  !_ : Prog effs A → Prog effs B
  !_ = _>>= nf
open Normalform ⦃...⦄ public

instance
  ℕ-Normalform : Normalform effs ℕ ℕ
  Normalform.nf ℕ-Normalform = var

  Bool-Normalform : Normalform effs Bool Bool
  Normalform.nf Bool-Normalform = var

  ⊤-Normalform : Normalform effs ⊤ ⊤
  Normalform.nf ⊤-Normalform = var

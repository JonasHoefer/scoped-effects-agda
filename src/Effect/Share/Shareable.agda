module Effect.Share.Shareable where

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Bool      using (Bool)
open import Data.Nat       using (ℕ)
open import Data.Unit      using (⊤)

open import Variables
open import Effect
open import Prog
open import Prog.Instances

record Shareable (effs : List Effect) (A : Set) : Set where
  field
    shareArgs : A → Prog effs A
open Shareable ⦃...⦄ public

instance
  ℕ-Shareable : Shareable effs ℕ
  Shareable.shareArgs ℕ-Shareable = var

  Bool-Shareable : Shareable effs Bool
  Shareable.shareArgs Bool-Shareable = var

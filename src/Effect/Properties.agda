{-# OPTIONS --overlapping-instances #-}

module Effect.Properties where

-- Collection of imports for  */properties.agda files

open import Function using (_$_; _∘_; id)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.List  using (List; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Tree

open import Variables
open import Effect
open import Effect.Nondet
open import Prog
open import Prog.Instances
open import Prog.Properties

import      Relation.Binary.PropositionalEquality as Eq
open        Eq using (_≡_; refl; cong; sym; trans)
open        Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

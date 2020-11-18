{-# OPTIONS --overlapping-instances #-}

module StateAndException where

open import Function       using (_$_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ using (_>>=_; _>>_; return)

open import Data.List      using (List; _∷_; [])
open import Data.Nat       using (ℕ; suc)
open import Data.Unit      using (⊤; tt)
open import Data.Product   using (_×_; _,_)
open import Data.Sum       using (_⊎_; inj₁; inj₂)

open import Container      using (Container)
open import Free
open import Free.Instances

open import Effect.Catch   using (Catch; _catch_; runCatch)
open import Effect.Exc     using (Exc; throw)
open import Effect.State   using (State; runState; get; put)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Tactic.FindIndex

----------------------------------------------------------------------
-- Tests for combination of State and Exception effect by Wu et al. --
----------------------------------------------------------------------

decr : ∀ {F} → {@(tactic eff) _ : State ℕ ∈ F} → {@(tactic eff) _ : Exc ⊤ ∈ F} → Free F ⊤
decr = get >>= λ where
    0       → throw tt
    (suc n) → put n >> pure tt

tripleDecr : ∀ {F} → {@(tactic eff) _ : State ℕ ∈ F} → {@(tactic eff) _ : Exc ⊤ ∈ F} → {@(tactic eff) _ : Catch ⊤ ∈ F} → Free F ⊤
tripleDecr = decr >> (decr >> decr catch pure)

local-update : (run $ runCatch $ runState 2 tripleDecr) ≡ inj₂ (1 , tt)
local-update = refl

global-update : (run $ runState 2 $ runCatch tripleDecr) ≡ (0 , inj₂ tt)
global-update = refl

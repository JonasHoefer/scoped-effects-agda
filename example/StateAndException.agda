{-# OPTIONS --overlapping-instances #-}

module StateAndException where

open import Function     using (_$_)

open import Data.Nat     using (ℕ; suc)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)

open import Container    using (Container)
open import Free
open import Injectable   using (_⊂_)

open import Effect.Catch using (Catch; _catch_; runCatch)
open import Effect.Exc   using (Exc; throw)
open import Effect.State using (State; runState; get; put)
open import Effect.Void  using (run)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

decr : ∀ {F} → ⦃ State ℕ ⊂ F ⦄ → ⦃ Exc ⊤ ⊂ F ⦄ → Free F ⊤
decr = get >>= λ where
    0       → throw tt
    (suc n) → put n >> pure tt
  where open RawMonad freeMonad using (_>>=_; _>>_)

tripleDecr : ∀ {F} → ⦃ State ℕ ⊂ F ⦄ → ⦃ Exc ⊤ ⊂ F ⦄ → ⦃ Catch ⊤ ⊂ F ⦄ → Free F ⊤
tripleDecr = decr >> (decr >> decr catch pure)
  where open RawMonad freeMonad using (_>>=_; _>>_)

local-update : (run $ runCatch $ runState 2 tripleDecr) ≡ inj₂ (1 , tt)
local-update = refl

global-update : (run $ runState 2 $ runCatch tripleDecr) ≡ (0 , inj₂ tt)
global-update = refl

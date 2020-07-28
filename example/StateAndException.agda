{-# OPTIONS --overlapping-instances #-}

module StateAndException where

open import Function     using (_$_)

open import Data.Nat     using (ℕ; suc)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)

open import Container    using (Container)
open import Free         using (Free; pure; _>>=_; _>>_)
open import Injectable   using (_⊂_)

open import Effect.Catch using (catch; _catchE_; runCatch)
open import Effect.Exc   using (exc; throw)
open import Effect.State using (state; runState; get; put)
open import Effect.Void  using (run)

decr : ∀ {F} → ⦃ state ℕ ⊂ F ⦄ → ⦃ exc ⊤ ⊂ F ⦄ → Free F ⊤
decr = get >>= λ where
  0       → throw tt
  (suc n) → put n >> pure tt

tripleDecr : ∀ {F} → ⦃ state ℕ ⊂ F ⦄ → ⦃ exc ⊤ ⊂ F ⦄ → ⦃ catch ⊤ ⊂ F ⦄ → Free F ⊤
tripleDecr = decr >> ((decr >> decr) catchE pure)

local-update : ⊤ ⊎ (ℕ × ⊤)
local-update = run $ runCatch $ runState 2 tripleDecr

global-update : ℕ × (⊤ ⊎ ⊤)
global-update = run $ runState 2 $ runCatch tripleDecr

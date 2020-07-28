{-# OPTIONS --overlapping-instances #-}

module Effect.Reader where

open import Function     using (_∘_; _$_)
open import Size         using (Size; ↑_)

open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)

open import Container    using (Container; ⟦_⟧; _▷_; _⊕_)
open import Free         using (Free; pure; impure)
open import Injectable   using (_⊂_; inject; project)

reader : Set → Container
reader Γ = ⊤ ▷ λ tt → Γ

runReader : {F : Container} {A Γ : Set} → Γ → Free (reader Γ ⊕ F) A → Free F A
runReader γ (pure x)                = pure x
runReader γ (impure (inj₁ tt , pf)) = runReader γ (pf γ)
runReader γ (impure (inj₂ s  , pf)) = impure (s , runReader γ ∘ pf)

ask : {F : Container} {Γ : Set} → ⦃ reader Γ ⊂ F ⦄ → Free F Γ
ask = inject (tt , pure)

local : {i : Size} {F : Container} {Γ A : Set} → ⦃ reader Γ ⊂ F ⦄ → (Γ → Γ) → Free F A {i} → Free F A
local f (pure x)     = inject (tt , (λ γ → pure x))
local f c@(impure _) with project c
... | nothing        = c
... | just (tt , pf) = inject (tt , λ γ → local f $ pf (f γ))

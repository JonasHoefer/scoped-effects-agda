module Effect.Reader where

open import Function     using (_∘_)

open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)

open import Container    using (Container; _▷_; _⊕_)
open import Free         using (Free; pure; impure)
open import Injectable   using (_⊂_; inject)

data Shape (Γ : Set) : Set where
  askˢ : Shape Γ
  localˢ : (Γ → Γ) → Shape Γ -- correct?

reader : Set → Container
reader Γ = Shape Γ ▷ λ { askˢ → Γ ; (localˢ x) → ⊤ }

runReader : {F : Container} {A Γ : Set} → Γ → Free (reader Γ ⊕ F) A → Free F A
runReader γ (pure x) = pure x
runReader γ (impure (inj₁ askˢ       , pf)) = runReader γ (pf γ)
runReader γ (impure (inj₁ (localˢ f) , pf)) = runReader (f γ) (pf tt)
runReader γ (impure (inj₂ s          , pf)) = impure (s , runReader γ ∘ pf)

ask : {F : Container} {Γ : Set} → ⦃ reader Γ ⊂ F ⦄ → Free F Γ
ask = inject (askˢ , pure)

local : {F : Container} {Γ A : Set} → ⦃ reader Γ ⊂ F ⦄ → (Γ → Γ) → Free F A → Free F A
local f ma = inject (localˢ f , λ tt → ma)

module Effect.Exc where

open import Function      using (_∘_)
open import Size          using (Size; ↑_)

open import Data.Bool     using (true; false)
open import Data.Unit     using (⊤; tt)
open import Data.Empty    using (⊥)
open import Data.Maybe    using (Maybe; nothing; just)
open import Data.Product  using (_,_)
open import Data.Sum      using (_⊎_; inj₁; inj₂)

open import Container     using (Container; _▷_; _⊕_)
open import Free
open import Injectable    using (_⊂_; inject; project; upcast)

data Shape (E : Set) : Set where
  throwˢ : E → Shape E

pattern Throw e pf = impure (inj₁ (throwˢ e) , pf)

Exc : Set → Container
Exc E = Shape E ▷ λ _ → ⊥

runExc : ∀ {F A E} → Free (Exc E ⊕ F) A → Free F (E ⊎ A)
runExc (pure x)               = pure (inj₂ x)
runExc (Throw e pf)           = pure (inj₁ e)
runExc (impure (inj₂ s , pf)) = impure (s , runExc ∘ pf)

throw : ∀ {A E F} → ⦃ Exc E ⊂ F ⦄ → E → Free F A
throw e = inject (throwˢ e , λ())

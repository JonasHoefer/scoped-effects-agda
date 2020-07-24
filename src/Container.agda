module Container where

open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])

open import Function     using (_∘_)

record Container : Set₁ where
  constructor
    _▷_
  field
    Shape : Set
    Pos : Shape → Set

-- | Extension of a container (lifitng of objects).
⟦_⟧ : Container → Set → Set
⟦ S ▷ P ⟧ A = Σ[ s ∈ S ] (P s → A)

-- | @fmap@ for the extension of a container (lifting of morphisms).
mapᶜ : {A B : Set} {C : Container} → (A → B) → ⟦ C ⟧ A → ⟦ C ⟧ B
mapᶜ f (s , pf) = s , f ∘ pf
{-# INLINE mapᶜ #-}

-- | Coproduct of containers.
infixr 1 _⊕_
_⊕_ : Container → Container → Container
(Shape₁ ▷ Pos₁) ⊕ (Shape₂ ▷ Pos₂) = (Shape₁ ⊎ Shape₂) ▷ [ Pos₁ , Pos₂ ]

injˡ : {F G : Container} {A : Set} → ⟦ F ⟧ A → ⟦ F ⊕ G ⟧ A
injˡ (s , pf) = inj₁ s , pf

injʳ : {F G : Container} {A : Set} → ⟦ G ⟧ A → ⟦ F ⊕ G ⟧ A
injʳ (s , pf) = inj₂ s , pf

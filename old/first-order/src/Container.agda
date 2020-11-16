module Container where

open import Function     using (_∘_)

open import Data.Empty   using (⊥)
open import Data.List    using (List; _∷_; []; foldr)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Tactic.Eff


record Container : Set₁ where
  constructor
    _▷_
  field
    Shape : Set
    Pos : Shape → Set

-- | Extension of a container (lifitng of objects).
⟦_⟧ : ∀ {ℓ} → Container → Set ℓ → Set ℓ
⟦ S ▷ P ⟧ A = Σ[ s ∈ S ] (P s → A)

-- | @fmap@ for the extension of a container (lifting of morphisms).
mapᶜ : ∀ {a b} {A : Set a} {B : Set b} {C : Container} → (A → B) → ⟦ C ⟧ A → ⟦ C ⟧ B
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

sum : List Container → Container
sum  = foldr (_⊕_) (⊥ ▷ λ())

inject : ∀ {c ops ℓ} {A : Set ℓ} → c ∈ ops → ⟦ c ⟧ A → ⟦ sum ops ⟧ A
inject (here refl) (s , pf) = inj₁ s , pf
inject (there p)   prog with inject p prog
... | s , pf = inj₂ s , pf

project : ∀ {c ops ℓ} {A : Set ℓ} → c ∈ ops → ⟦ sum ops ⟧ A → Maybe (⟦ c ⟧ A)
project (here refl) (inj₁ s , pf) = just (s , pf)
project (here refl) (inj₂ _ , _ ) = nothing
project (there _  ) (inj₁ _ , _ ) = nothing
project (there p  ) (inj₂ s , pf) = project p (s , pf)

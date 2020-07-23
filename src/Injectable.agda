module Injectable where

open import Level        using (Level; suc)

open import Function     using (id; _∘_)

open import Data.Bool    using (Bool; true; false)
open import Data.List    using (List; []; _∷_)
open import Data.Empty   using (⊥)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])

record Container : Set₁ where
  constructor
    _▶_
  field
    Shape : Set
    Pos : Shape → Set

⟦_⟧ : Container → Set → Set
⟦ S ▶ P ⟧ A = Σ[ s ∈ S ] (P s → A)

infixr 1 _⊕_
_⊕_ : Container → Container → Container
(Shape₁ ▶ Pos₁) ⊕ (Shape₂ ▶ Pos₂) = (Shape₁ ⊎ Shape₂) ▶ [ Pos₁ , Pos₂ ]

injˡ : {F G : Container} {A : Set} → ⟦ F ⟧ A → ⟦ F ⊕ G ⟧ A
injˡ (s , pf) = inj₁ s , pf

injʳ : {F G : Container} {A : Set} → ⟦ F ⟧ A → ⟦ G ⊕ F ⟧ A
injʳ (s , pf) = inj₂ s , pf

infix 4 _⊂_
record _⊂_ (F G : Container) : Set₁ where
  field
   inj : {A : Set} → ⟦ F ⟧ A → ⟦ G ⟧ A
   prj : {A : Set} → ⟦ G ⟧ A → Maybe (⟦ F ⟧ A)
open _⊂_ ⦃ ... ⦄ public

instance
  ⊂-⊕-left : {F G : Container} → F ⊂ (F ⊕ G)
  _⊂_.inj ⊂-⊕-left = injˡ
  _⊂_.prj ⊂-⊕-left (inj₁ s , pf) = just (s , pf) -- patterns for injˡ / injʳ ?
  _⊂_.prj ⊂-⊕-left (inj₂ _ , _ ) = nothing

  ⊂-⊕-trans : {F G H : Container} → ⦃ F ⊂ H ⦄ → F ⊂ (G ⊕ H)
  _⊂_.inj ⊂-⊕-trans = injʳ ∘ inj
  _⊂_.prj ⊂-⊕-trans (inj₁ _ , _ ) = nothing
  _⊂_.prj ⊂-⊕-trans (inj₂ s , pf) = prj (s , pf)

data Free (C : Container) (A : Set) : Set where
  pure : A → Free C A
  impure : ⟦ C ⟧ (Free C A) → Free C A

inject : {F G : Container} {A : Set} → ⦃ F ⊂ G ⦄ → ⟦ F ⟧ (Free G A) → Free G A
inject = impure ∘ inj

project : {F G : Container} {A : Set} → ⦃ F ⊂ G ⦄ → Free G A → Maybe (⟦ F ⟧ (Free G A))
project (pure   _) = nothing
project (impure x) = prj x

-- non determinism effect
module NonDet where
  data Shape : Set where
    failˢ   : Shape
    choiceˢ : Shape

  pos : Shape → Set
  pos failˢ   = ⊥
  pos choiceˢ = Bool

  nondet : Container
  nondet = Shape ▶ pos

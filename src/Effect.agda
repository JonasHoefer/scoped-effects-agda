module Effect where

open import Function using (const; _∘_)

open import Data.Empty                            using (⊥)
open import Data.List                             using (List; _∷_; []; foldr)
open import Data.List.Relation.Unary.Any          using (Any; here; there) renaming (map to map∈)           public
open import Data.Maybe                            using (Maybe; just; nothing)
open import Data.Product                          using (Σ-syntax; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.Sum                              using (_⊎_; inj₁; inj₂; [_,_])                            public

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


infix 3 _∈_
_∈_ : ∀ {a} {A : Set a} → A → List A → Set a
x ∈ xs = Any (_≡_ x) xs

instance
  ∈-head : ∀ {a} {A : Set a} {x : A} {xs} → x ∈ x ∷ xs
  ∈-head = here refl

  ∈-tail : ∀ {a} {A : Set a} {x y : A} {xs} → ⦃ x ∈ xs ⦄ → x ∈ y ∷ xs
  ∈-tail ⦃ p ⦄ = there p

record Container : Set₁ where
  constructor _▷_
  field
    Shape : Set
    Pos : Shape → Set
open Container public

private
  variable
    A B : Set
    C : Container
    Cs : List Container

_~>_ : Set → Set → Container
S ~> P = S ▷ const P

⟦_⟧ : Container → Set → Set
⟦ S ▷ P ⟧ A = Σ[ s ∈ S ] (P s → A)

map : (A → B) → ⟦ C ⟧ A → ⟦ C ⟧ B
map f c = π₁ c , f ∘ π₂ c
{-# INLINE map #-}

_⊕_ : Container → Container → Container
(S₁ ▷ P₁) ⊕ (S₂ ▷ P₂) = (S₁ ⊎ S₂) ▷ [ P₁ , P₂ ]

Void : Container
Void = ⊥ ▷ λ()

⨁ : List Container → Container
⨁ = foldr _⊕_ Void

record Effect : Set₁ where
  field
    Ops Scps : Container
open Effect public

ops : List Effect → Container
ops = ⨁ ∘ Data.List.map Ops

scps : List Effect → Container
scps = ⨁ ∘ Data.List.map Scps

inj : C ∈ Cs → ⟦ C ⟧ A → ⟦ ⨁ Cs ⟧ A
inj (here refl) (s , pf) = inj₁ s , pf
inj (there p  ) x with inj p x
... | s , pf = inj₂ s , pf

prj : C ∈ Cs → ⟦ ⨁ Cs ⟧ A → Maybe (⟦ C ⟧ A)
prj (here refl) (inj₁ s , pf) = just (s , pf)
prj (here refl) (inj₂ s , pf) = nothing
prj (there p)   (inj₁ s , pf) = nothing
prj (there p)   (inj₂ s , pf) = prj p (s , pf)

-- std lib!

ops-inj : ∀ {E effs} → (E ∈ effs) → Ops E ∈ Data.List.map Ops effs
ops-inj (here px) = here (cong Ops px)
ops-inj (there p) = there (ops-inj p)

scps-inj : ∀ {E effs} → (E ∈ effs) → Scps E ∈ Data.List.map Scps effs
scps-inj (here px) = here (cong Scps px)
scps-inj (there p) = there (scps-inj p)

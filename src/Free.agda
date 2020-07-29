module Free where

open import Function              using (_∘_; id)
open import Size                  using (Size; ↑_; _⊔ˢ_; Size<_)
open import Level                 using (Level)

open import Category.Monad public using (RawMonad; module RawMonad)

open import Data.Product          using (_,_)

open import Container             using (Container; ⟦_⟧)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

data Free (C : Container) (A : Set) : {Size} → Set where
  pure : ∀ {i : Size} → A → Free C A {i}
  impure : ∀ {i : Size} → ⟦ C ⟧ (Free C A {i}) → Free C A {↑ i}

-- typchecks only for Size ∞
-- _+_ for sized types would allow us to express a better upper bound.
bind : {A B : Set} {C : Container} → Free C A → (A → Free C B) → Free C B
bind (pure x)          k = k x
bind (impure (s , pf)) k = impure (s , λ z → bind (pf z) k)

map : {A B : Set} {C : Container} {i : Size} → (A → B) → Free C A {i} → Free C B {i}
map f (pure x)          = pure (f x)
map f (impure (s , pf)) = impure (s , map f ∘ pf)

module _ {C : Container} where
  freeMonad : RawMonad (λ x → Free C x)
  freeMonad = record
    { return = pure
    ; _>>=_  = bind
    }

-- postualting extensionality is consistent with agdas underlying theory
postulate
  ext : ∀ {ℓ ℓ′ : Level} {A : Set ℓ} {B : A → Set ℓ′} {f g : (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x) → f ≡ g

map-id : ∀ {A F i} → (mx : Free F A {i}) → map id mx ≡ mx
map-id (pure x)   = refl
map-id (impure (s , pf)) = cong (λ t → impure (s , t)) (ext λ p → map-id (pf p))

map-∘ : ∀ {A B C F i} → (mx : Free F A {i}) → (f : B → C) → (g : A → B) → map (f ∘ g) mx ≡ map f (map g mx)
map-∘ (pure x)          f g = refl
map-∘ (impure (s , pf)) f g = cong (λ t → impure (s , t)) (ext λ p → map-∘ (pf p) f g)

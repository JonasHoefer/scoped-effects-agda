module Free.Properties where

open import Function                              using (id; _∘_)
open import Level                                 using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Category.Functor                      using (RawFunctor)
open        RawFunctor ⦃...⦄

open import Data.Product                          using (_,_)
open import Free
open import Free.Instances

postulate
  ext : ∀ {ℓ ℓ′ : Level} {A : Set ℓ} {B : A → Set ℓ′} {f g : (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x) → f ≡ g

private
  variable
    A B C : Set

map-id : ∀ {F i} → (mx : Free F A {i}) → (id <$> mx) ≡ mx
map-id (pure x)   = refl
map-id (impure (s , pf)) = cong (λ t → impure (s , t)) (ext λ p → map-id (pf p))

map-∘ : ∀ {F i} → (mx : Free F A {i}) → (f : B → C) → (g : A → B) → ((f ∘ g) <$> mx) ≡ (f <$> (g <$> mx))
map-∘ (pure x)          f g = refl
map-∘ (impure (s , pf)) f g = cong (λ t → impure (s , t)) (ext λ p → map-∘ (pf p) f g)

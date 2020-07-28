{-# OPTIONS --overlapping-instances #-}

module Injectable where

open import Function     using (_∘_)
open import Size         using (Size; ↑_)

open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)

open import Container    using (Container; ⟦_⟧; _⊕_; injˡ; injʳ)
open import Free         using (Free; pure; impure)


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

inject : {F G : Container} {A : Set} → ⦃ F ⊂ G ⦄ → ⟦ F ⟧ (Free G A) → Free G A
inject = impure ∘ inj

project : {F G : Container} {A : Set} {i : Size} → ⦃ F ⊂ G ⦄ → Free G A {↑ i} → Maybe (⟦ F ⟧ (Free G A {i}))
project (pure   _) = nothing
project (impure x) = prj x

upcast : {i : Size} {F G : Container} {A : Set} → Free G A {i} → Free (F ⊕ G) A {i}
upcast (pure x) = pure x
upcast (impure (s , pf)) = impure ((inj₂ s) , upcast ∘ pf)

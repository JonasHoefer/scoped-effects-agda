module Free where

open import Function                              using (_∘_; id)
open import Size                                  using (Size; ↑_; _⊔ˢ_; Size<_; ∞)

open import Category.Functor                      using (RawFunctor; module RawFunctor)
open import Category.Monad                        using (RawMonad; module RawMonad)

open import Data.List                             using (List; []; _∷_; foldr)
open import Data.Maybe                            using (Maybe; just; nothing)
open import Data.Product                          using (_,_; _×_; proj₂)
open import Data.Sum                              using (inj₂)

open import Container                             using (Container; ⟦_⟧; sum; inject; project)

open import Tactic.Eff                            using (eff; _∈_; here; there) public
open import Relation.Binary.PropositionalEquality using (refl) public

data Free (ops : List Container) (A : Set) : {Size} → Set where
  pure : {i : Size} → A → Free ops A {i}
  impure : {i : Size} → ⟦ sum ops ⟧ (Free ops A {i}) → Free ops A {↑ i}

pattern Other s pf = impure (inj₂ s , pf)

op : ∀ {C ops A} {@(tactic eff) p : C ∈ ops} → ⟦ C ⟧ (Free ops A) → Free ops A
op {p = p} = impure ∘ inject p

prj : ∀ {C ops a i} {@(tactic eff) p : C ∈ ops} → Free ops a {↑ i} → Maybe (⟦ C ⟧ (Free ops a {i}))
prj (pure x)           = nothing
prj {p = p} (impure x) = project p x

upcast : ∀ {C ops A i} → Free ops A {i} → Free (C ∷ ops) A {i}
upcast (pure x)          = pure x
upcast (impure (s , pf)) = impure (inj₂ s , upcast ∘ pf)

run : {A : Set} → Free [] A → A
run (pure x) = x

private
  -- typchecks only for Size ∞
  -- _+_ for sized types would allow us to express a better upper bound.
  bind : ∀ {ops} {A : Set} {B : Set} → Free ops A → (A → Free ops B) → Free ops B
  bind (pure x)          k = k x
  bind (impure (s , pf)) k = impure (s , λ z → bind (pf z) k)

  map : ∀ {i ops} {A : Set} {B : Set} → (A → B) → Free ops A {i} → Free ops B {i}
  map f (pure x)          = pure (f x)
  map f (impure (s , pf)) = impure (s , map f ∘ pf)

monad : {ops : List Container} → RawMonad λ A → Free ops A
monad = record { return = pure ; _>>=_ = bind }

functor : {i : Size} {ops : List Container} → RawFunctor λ A → Free ops A {i}
functor = record { _<$>_ = map }


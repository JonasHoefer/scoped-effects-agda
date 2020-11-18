{-# OPTIONS --type-in-type #-} -- UNSAFE!

module HOTypeInType where

open import Size
open import Function using (_∘_; _$_; id)

open import Category.Functor using (RawFunctor)
open        RawFunctor ⦃...⦄ using (_<$>_; _<$_)

open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; Σ-syntax; uncurry)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; _∷_; []; foldr)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂; map₂)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

--------------------------------------------------------
-- First sketch of higher order scoped effect in Agda --
--------------------------------------------------------

-- Uses type-in-type -> UNSAFE

infix 3 _∈_
_∈_ : ∀ {a} {A : Set a} → A → List A → Set a
x ∈ xs = Any (_≡_ x) xs

instance
  -⊎_-RawFunctor : ∀ {E} → RawFunctor (E ⊎_)
  -⊎_-RawFunctor = record { _<$>_ = map₂ }

  -×_-RawFunctor : ∀ {E} → RawFunctor (E ×_)
  -×_-RawFunctor = record { _<$>_ = λ f (a , b) → a , f b }

record Container : Set where
  constructor _◁_/_
  field
    Shape : Set
    Pos : Shape → Set
    Ctx : (s : Shape) → Pos s → Set → Set
open Container public

variable
  A B E S : Set
  F G : Set → Set
  ops : List Container
  C : Container
  i : Size

_⊕_ : Container → Container → Container
(S₁ ◁ P₁ / C₁) ⊕ (S₂ ◁ P₂ / C₂) = (S₁ ⊎ S₂) ◁ [ P₁ , P₂ ] / [ C₁ , C₂ ]

Void : Container
Void = (⊥ ◁ (λ()) / (λ()))

sum : List Container → Container
sum = foldr _⊕_ Void

⟦_⟧ : Container → (Set → Set) → Set → Set
⟦ S ◁ P / C ⟧ F A = Σ[ s ∈ S ] ((p : P s) → F (C s p A))

inj : ∀ {F A C ops} → C ∈ ops → ⟦ C ⟧ F A → ⟦ sum ops ⟧ F A
inj         (here refl) (s , pf) = (inj₁ s) , pf
inj {F} {A} (there p)   prog     with inj {F} {A} p prog
... | s , pf = inj₂ s , pf

prj : ∀ {F A C ops} → C ∈ ops → ⟦ sum ops ⟧ F A → Maybe (⟦ C ⟧ F A)
prj         (here refl) (inj₁ s , pf) = just (s , pf)
prj         (here refl) (inj₂ _ , _ ) = nothing
prj         (there p  ) (inj₁ _ , _ ) = nothing
prj {F} {A} (there p  ) (inj₂ s , pf) = prj {F} {A} p (s , pf)

upcast : ∀ {C D F A} → ⟦ D ⟧ F A → ⟦ C ⊕ D ⟧ F A
upcast (s , pf) = (inj₂ s) , pf

data Free (C : List Container) (A : Set) : Size → Set

Free′ : List Container → Size → Set → Set
Free′ C i A = Free C A i

data Free C A where
  pure : ∀ {i} → A → Free C A i
  impure : ∀ {i} → ⟦ sum C ⟧ (Free′ C i) A → Free C A (↑ i)

pattern Other s pf = impure (inj₂ s , pf)

run : Free [] A _ → A
run (pure x) = x

inject : ⦃ C ∈ ops ⦄ → ⟦ C ⟧ (Free′ ops _) A → Free ops A _
inject ⦃ p ⦄ = impure ∘ inj {Free′ _ _} p

project : ⦃ C ∈ ops ⦄ → Free ops A (↑ i) → Maybe (⟦ C ⟧ (Free′ ops i) A)
project ⦃ p ⦄ (pure x)   = nothing
project ⦃ p ⦄ (impure x) = prj {Free′ _ _} p x

record Syntax (C : Container) : Set where
  field
    emap : {A B : Set} {F : Size → Set → Set} {i : Size} → (∀ {X i} → F i X → F ∞ X) →
      (F i A → F ∞ B) → ⟦ C ⟧ (F i) A → ⟦ C ⟧ (F ∞) B
    handle : {i : Size} {A : Set} {M N : Size → Set → Set} {F : Set → Set} → ⦃ RawFunctor F ⦄ →
      F ⊤ → (∀ {X} → F (M i X) → N ∞ (F X)) → ⟦ C ⟧ (M i) A → ⟦ C ⟧ (N ∞) (F A)
open Syntax ⦃...⦄ public

instance
  []-Syntax : Syntax (sum [])
  Syntax.emap   []-Syntax _ _ ()
  Syntax.handle []-Syntax _ _ ()

  ∷-Syntax : ∀ {C D} → ⦃ Syntax C ⦄ → ⦃ Syntax D ⦄ → Syntax (C ⊕ D)
  Syntax.emap ∷-Syntax {A} {B} {F} {i} d f         (inj₁ s , pf) with emap {_} {A} {B} {F} {i} d f (s , pf)
  ... | s′ , pf′ = inj₁ s′ , pf′
  Syntax.emap ∷-Syntax {A} {B} {F} {i} d f         (inj₂ s , pf) with emap {_} {A} {B} {F} {i} d f (s , pf)
  ... | s′ , pf′ = inj₂ s′ , pf′
  Syntax.handle ∷-Syntax {i} {A} {M} {N} {F} c hdl (inj₁ s , pf) with handle {_} {i} {A} {M} {N} {F} c hdl (s , pf)
  ... | s′ , pf′ = inj₁ s′ , pf′
  Syntax.handle ∷-Syntax {i} {A} {M} {N} {F} c hdl (inj₂ s , pf) with handle {_} {i} {A} {M} {N} {F} c hdl (s , pf)
  ... | s′ , pf′ = inj₂ s′ , pf′

up : Free ops A i → Free ops A ∞
up (pure x) = pure x
up (impure (s , pf)) = impure (s , up ∘ pf)

_>>=_ : ⦃ Syntax (sum ops) ⦄ → Free ops A i → (A → Free ops B _) → Free ops B _
pure x   >>= k = k x
impure x >>= k = impure (emap {F = Free′ _} up (_>>= k) x)

_>>_ : ⦃ Syntax (sum ops) ⦄ → Free ops A i → Free ops B _ → Free ops B _
ma >> mb = ma >>= λ _ → mb

module HExc where
  data HExcˢ (E : Set) : Set₁ where
    throwˢ : E → HExcˢ E
    catchˢ : (X : Set) → HExcˢ E

  data HExcCatchᵖ (X E : Set) : Set where
    mainᵖ : HExcCatchᵖ X E
    handleᵖ : E → HExcCatchᵖ X E
    contᵖ : X → HExcCatchᵖ X E

  HExcᵖ : (E : Set) → HExcˢ E → Set
  HExcᵖ E (throwˢ _) = ⊥
  HExcᵖ E (catchˢ X) = HExcCatchᵖ X E

  HExcᶜ : ∀ {E} (s : HExcˢ E) → HExcᵖ E s → Set → Set
  HExcᶜ (catchˢ X) mainᵖ       A = X
  HExcᶜ (catchˢ X) (handleᵖ x) A = X
  HExcᶜ (catchˢ X) (contᵖ x)   A = A

  HExc : Set → Container
  HExc E = HExcˢ E ◁ HExcᵖ E / HExcᶜ

  instance
    HExc-Syntax : Syntax (HExc E)
    Syntax.emap HExc-Syntax d f (throwˢ e , pf) = throwˢ e , λ()
    Syntax.emap HExc-Syntax d f (catchˢ X , pf) = catchˢ X , λ where
      mainᵖ       → d (pf mainᵖ)
      (handleᵖ h) → d (pf (handleᵖ h))
      (contᵖ x)   → f (pf (contᵖ x))
    Syntax.handle HExc-Syntax         c hdl (throwˢ e , pf) = throwˢ e , λ()
    Syntax.handle HExc-Syntax {F = F} c hdl (catchˢ X , pf) = catchˢ (F X) , λ where
      mainᵖ       → hdl (pf mainᵖ       <$  c)
      (handleᵖ h) → hdl (pf (handleᵖ h) <$  c)
      (contᵖ x)   → hdl (pf ∘ contᵖ     <$> x)

  pattern Throw e pf = impure (inj₁ (throwˢ e) , pf)
  pattern Catch X pf = impure (inj₁ (catchˢ X) , pf)

  runHExc : ⦃ Syntax (sum ops) ⦄ → Free (HExc E ∷ ops) A i → Free ops (E ⊎ A) ∞
  runHExc (pure x) = pure (inj₂ x)
  runHExc (Throw x κ) = pure (inj₁ x)
  runHExc (Catch X κ) = runHExc (κ mainᵖ) >>= λ where
    (inj₁ e) → runHExc (κ (handleᵖ e)) >>= λ where
      (inj₁ e) → pure (inj₁ e)
      (inj₂ a) → runHExc (κ (contᵖ a))
    (inj₂ a) → runHExc (κ (contᵖ a))
  runHExc (Other s κ) = impure (handle {M = Free′ _} {N = Free′ _} (inj₂ tt) [ (pure ∘ inj₁) , runHExc ] (s , κ))

  throw : ⦃ HExc E ∈ ops ⦄ → E → Free ops A _
  throw e = inject (throwˢ e , λ())

  infix 0 _catch_
  _catch_ : ⦃ HExc E ∈ ops ⦄ → Free ops A _ → (E → Free ops A _) → Free ops A _
  p catch h = inject (catchˢ _ , λ{ mainᵖ → p ; (handleᵖ x) → h x ; (contᵖ x) → pure x})
open HExc using (HExc; runHExc; throw; _catch_)

module Lift where
  _▷_ : (Shape : Set) → (Shape → Set) → Container
  _▷_ Shape Pos = Shape ◁ Pos / λ _ _ τ → τ

  instance
    FO-Syntax : ∀ {Shape Pos} → Syntax (Shape ▷ Pos)
    Syntax.emap   FO-Syntax _ f   (s , κ) = s , f ∘ κ
    Syntax.handle FO-Syntax c hdl (s , κ) = s , λ p → hdl (κ p <$ c)

  _▷_-emap-id : ∀ {F A S P i} → (x : ⟦ S ▷ P ⟧ (Free′ F i) A) → emap {S ▷ P} {A} {A} {Free′ F} up id x ≡ x
  _▷_-emap-id x = refl
open Lift using (_▷_)

module State where
  data Stateˢ (S : Set) : Set where
    putˢ : S → Stateˢ S
    getˢ : Stateˢ S

  State : Set → Container
  State S = Stateˢ S ▷ λ where
    (putˢ _) → ⊤
    getˢ     → S

  pattern Get pf = impure (inj₁ getˢ , pf)
  pattern Put s pf = impure (inj₁ (putˢ s) , pf)

  runState : S → ⦃ Syntax (sum ops) ⦄ → Free (State S ∷ ops) A i → Free ops (S × A) _
  runState s₀ (pure x)    = pure (s₀ , x)
  runState _  (Put s₁ κ)  = runState s₁ (κ tt)
  runState s₀ (Get κ)     = runState s₀ (κ s₀)
  runState s₀ (Other s κ) = impure (handle {M = Free′ _} {N = Free′ _} (s₀ , tt) (λ (s′ , x) → runState s′ x) (s , κ))

  put : ⦃ State S ∈ ops ⦄ → S → Free ops ⊤ _
  put s = inject ((putˢ s) , pure)

  get : ⦃ State S ∈ ops ⦄ → Free ops S _
  get = inject (getˢ , pure)
open State using (State; runState; put; get)

module TestExc where
  decr : ⦃ Syntax (sum ops) ⦄ → ⦃ HExc ⊤ ∈ ops ⦄ → ℕ → Free ops ℕ _
  decr n = pure n >>= λ where
    zero    → throw tt
    (suc x) → pure x

  catchDecr : ⦃ HExc ⊤ ∈ ops ⦄ → ⦃ Syntax (sum ops) ⦄ → ℕ → Free ops ℕ _
  catchDecr n = (decr n >>= decr) catch (λ _ → pure 42)

  runTest : (run $ runHExc $ catchDecr ⦃ here refl ⦄ 1) ≡ inj₂ 42
  runTest = refl

module TestStateExc where
  decr : ⦃ Syntax (sum ops) ⦄ → ⦃ HExc ⊤ ∈ ops ⦄ → ⦃ State ℕ ∈ ops ⦄ → Free ops ⊤ _
  decr = get >>= λ where
    zero    → throw tt
    (suc x) → put x

  tripleDecr : ⦃ HExc ⊤ ∈ ops ⦄ → ⦃ State ℕ ∈ ops ⦄ → ⦃ Syntax (sum ops) ⦄ → Free ops ⊤ _
  tripleDecr = decr >> (decr >> decr catch pure)

  globalUpdate : ℕ × (⊤ ⊎ ⊤)
  globalUpdate = run $ runState 2 $ runHExc $ tripleDecr ⦃ here refl ⦄ ⦃ there (here refl) ⦄

  localUpdate : ⊤ ⊎ (ℕ × ⊤)
  localUpdate = run $ runHExc $ runState 2 $ tripleDecr ⦃ there (here refl) ⦄ ⦃ here refl ⦄

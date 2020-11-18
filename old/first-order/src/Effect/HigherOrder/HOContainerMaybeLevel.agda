{-# OPTIONS --cumulativity #-}

module Effect.HigherOrder.HOContainerMaybeLevel where

open import Function using (_∘_; _$_)
open import Level using (Level; suc; _⊔_; 0ℓ; Setω)
open import Size using (Size; ↑_; ∞)

open import Category.Functor using (RawFunctor)
open        RawFunctor ⦃...⦄

open import Data.Empty using (⊥)
open import Data.List using (List; _∷_; []; foldr)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]; map₂)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

--------------------------------------------------
-- Second sketch of higher order scoped effects --
--------------------------------------------------

-- This second sketch corresponds to the one form the thesis.
-- It demostrates the size issues.

instance
  -⊎_-RawFunctor : ∀ {ℓ} {E : Set} → RawFunctor {ℓ} {ℓ} (E ⊎_)
  -⊎_-RawFunctor = record { _<$>_ = map₂ }

  -×_-RawFunctor : ∀ {ℓ} {E : Set ℓ} → RawFunctor {ℓ} {ℓ} (E ×_)
  -×_-RawFunctor = record { _<$>_ = λ f (a , b) → a , f b }

infix 3 _∈_
_∈_ : ∀ {ℓ} → {A : Set ℓ} → A → List A → Set ℓ
_∈_ {ℓ} x xs = Any {ℓ} {ℓ} (_≡_ x) xs

record Container : Set₂ where
  constructor _▷_/_
  field
    Shape : Set₁
    Pos : Shape → Set₁
    Ctx : (s : Shape) → Pos s → Maybe {suc (suc 0ℓ)} Set₁
open Container public

variable
  A B : Set
  i : Size
  ops : List Container
  C : Container

⟦_⟧ : Container → (Set₁ → Set₁) → Set₁ → Set₁
⟦ S ▷ P / C ⟧ F X = Σ[ s ∈ S ] ((p : P s) → F (fromMaybe X (C s p)))

Void : Container
Void = ⊥ ▷ (λ()) / λ()

_⊕_ : Container → Container → Container
(S₁ ▷ P₁ / C₁) ⊕ (S₂ ▷ P₂ / C₂) = (S₁ ⊎ S₂) ▷ [ P₁ , P₂ ] / [ C₁ , C₂ ]

sum : List Container → Container
sum = foldr _⊕_ Void

inj : ∀ {F : Set₁ → Set₁} → C ∈ ops → ⟦ C ⟧ F A → ⟦ sum ops ⟧ F A
inj         (here refl) (s , pf) = inj₁ s , pf
inj {F = F} (there p)   prog     with inj {F = F} p prog
... | s , pf = (inj₂ s) , pf

data Free (ops : List Container) (A : Set₁) : Size → Set₁ where
  pure : A → Free ops A i
  impure : ⟦ sum ops ⟧ (λ A → Free ops A i) A → Free ops A (↑ i)

Free′ : List Container → Size → Set₁ → Set₁
Free′ C i A = Free C A i

inject : ⦃ C ∈ ops ⦄ → ⟦ C ⟧ (Free′ ops _) A → Free′ ops _ A
inject ⦃ p ⦄ = impure ∘ inj {F = Free′ _ _} p

record Syntax (C : Container) : Setω where
  field
    emap : {F : Size → Set₁ → Set₁} →
      (∀ {X : Set} → F i X → F ∞ X) → (F i A → F ∞ B) → ⟦ C ⟧ (F i) A → ⟦ C ⟧ (F ∞) B
    handle : {M N : Size → Set₁ → Set₁} → {F : ∀ {ℓ} → Set ℓ → Set ℓ} → ⦃ RawFunctor {suc 0ℓ} {suc 0ℓ} F ⦄ →
      (∀ {X} → F {0ℓ} X → F {suc 0ℓ} X) → F {0ℓ} ⊤ → ({X : Set} →
      F {suc 0ℓ} (M i X) → N ∞ (F {0ℓ} X)) → ⟦ C ⟧ (M i) A → ⟦ C ⟧ (N ∞) (F {0ℓ} A)
open Syntax ⦃...⦄ public

run : Free [] A _ → A
run (pure x) = x

instance
  Void-Syntax : Syntax Void
  Syntax.emap   Void-Syntax _ _ ()
  Syntax.handle Void-Syntax _ _ _ ()

  ⊕-Syntax : ∀ {F G} → ⦃ Syntax F ⦄ → ⦃ Syntax G ⦄ → Syntax (F ⊕ G)
  Syntax.emap ⊕-Syntax {i} {A} {B} {F} d f (inj₁ s , pf) with emap {_} {i} {A} {B} {F} d f (s , pf)
  ... | s′ , pf′ = (inj₁ s′) , pf′
  Syntax.emap ⊕-Syntax {i} {A} {B} {F} d f (inj₂ s , pf) with emap {_} {i} {A} {B} {F} d f (s , pf)
  ... | s′ , pf′ = (inj₂ s′) , pf′
  Syntax.handle ⊕-Syntax {i} {A} {M} {N} {F} u c hdl (inj₁ s , pf) with handle {_} {i} {A} {M} {N} {λ {ℓ} X → F {ℓ} X} u c hdl (s , pf)
  ... | s′ , pf′ = inj₁ s′ , pf′
  Syntax.handle ⊕-Syntax {i} {A} {M} {N} {F} u c hdl (inj₂ s , pf) with handle {_} {i} {A} {M} {N} {λ {ℓ} X → F {ℓ} X} u c hdl (s , pf)
  ... | s′ , pf′ = inj₂ s′ , pf′

dropSize : {C : List Container} → Free C A i → Free C A ∞
dropSize (pure x)          = pure x
dropSize (impure (s , pf)) = impure (s , pf)

infixl 1 _>>=_ _>>_
_>>=_ : ⦃ Syntax (sum ops) ⦄ → Free ops A i → (A → Free ops B _) → Free ops B _
pure x   >>= k = k x
impure x >>= k = impure (emap {F = Free′ _} dropSize (_>>= k) x)

_>>_ : ⦃ Syntax (sum ops) ⦄ → Free ops A i → Free ops B _ → Free ops B _
ma >> mb = ma >>= λ _ → mb

module HExc where
  private
    variable
      E : Set

  data HExcˢ (E : Set) : Set₁ where
    catchˢ : (X : Set) → HExcˢ E
    throwˢ : (e : E) → HExcˢ E

  data HExcCatchᵖ (X E : Set) : Set where
    mainᵖ   : HExcCatchᵖ X E
    handleᵖ : E → HExcCatchᵖ X E
    contᵖ   : X → HExcCatchᵖ X E

  HExcᵖ : (E : Set) → HExcˢ E → Set
  HExcᵖ E (catchˢ X) = HExcCatchᵖ X E
  HExcᵖ _ (throwˢ e) = ⊥

  HExcᶜ : (s : HExcˢ E) → HExcᵖ E s → Maybe Set₁
  HExcᶜ (catchˢ X) mainᵖ       = just X
  HExcᶜ (catchˢ X) (handleᵖ x) = just X
  HExcᶜ (catchˢ _) (contᵖ x)   = nothing

  HExc : Set → Container
  HExc E = HExcˢ E ▷ HExcᵖ E / HExcᶜ

  instance
    HExc-Syntax : Syntax (HExc E)
    Syntax.emap HExc-Syntax d f (catchˢ X , pf) = catchˢ X , λ  where
      mainᵖ       → d (pf mainᵖ)
      (handleᵖ x) → d (pf (handleᵖ x))
      (contᵖ x)   → f (pf (contᵖ x))
    Syntax.emap HExc-Syntax d f (throwˢ e , pf) = throwˢ e , λ()
    Syntax.handle HExc-Syntax {F = F} up c hdl (catchˢ X , pf) = catchˢ (F X) , λ where
      mainᵖ       → hdl (pf mainᵖ       <$  up c)
      (handleᵖ e) → hdl (pf (handleᵖ e) <$  up c)
      (contᵖ x)   → hdl (pf ∘ contᵖ     <$> up x)
    Syntax.handle HExc-Syntax         up c hdl (throwˢ e , pf) = throwˢ e , λ()

  pattern Catch   pf = impure (inj₁ (catchˢ _) , pf)
  pattern Throw e pf = impure (inj₁ (throwˢ e) , pf)
  pattern Other s pf = impure (inj₂ s          , pf)

  up-E⊎- : ∀ {A : Set} → _⊎_ {0ℓ} {0ℓ} E A → _⊎_ {0ℓ} {suc 0ℓ} E A
  up-E⊎- (inj₁ e) = inj₁ e
  up-E⊎- (inj₂ a) = inj₂ a

  runHExc : ∀ {ops} → ⦃ Syntax (sum ops) ⦄ → Free (HExc E ∷ ops) A i → Free ops (E ⊎ A) _
  runHExc (pure x)    = pure (inj₂ x)
  runHExc (Catch   κ) = runHExc (κ mainᵖ) >>= λ where
    (inj₁ e) → runHExc (κ (handleᵖ e)) >>= λ where
      (inj₁ e) → pure (inj₁ e)
      (inj₂ x) → runHExc (κ (contᵖ x))
    (inj₂ x) → runHExc (κ (contᵖ x))
  runHExc (Throw e κ) = pure (inj₁ e)
  runHExc {E = E} (Other s κ) = impure (handle
    {M = Free′ _} {N = Free′ _} {F = λ {ℓ} A → _⊎_ {0ℓ} {ℓ} E A}
    up-E⊎-
    (inj₂ {0ℓ} {0ℓ} {E} {⊤} tt)
    [ pure ∘ inj₁ , runHExc ]
    (s , κ))

  throw : ⦃ HExc E ∈ ops ⦄ → E → Free ops A _
  throw e = inject (throwˢ e , λ())

  infix 0 _catch_
  _catch_ : ⦃ HExc E ∈ ops ⦄ → Free ops A _ → (E → Free ops A _) → Free ops A _
  a catch h = inject (catchˢ _ , λ{ mainᵖ → a ; (handleᵖ e) → h e ; (contᵖ x) → pure x})

  throw-bind : ⦃ _ : Syntax (sum ops) ⦄ → {k : A → Free (HExc E ∷ ops) B _} → {e : E} →
    runHExc (throw ⦃ here refl ⦄ e >>= k) ≡ runHExc (throw ⦃ here refl ⦄ e)
  throw-bind = refl
open HExc using (HExc; runHExc; throw; _catch_) public

-- -----------------------
-- --- Real Life Tests ---
-- -----------------------

testCatch : ⦃ HExc ⊤ ∈ ops ⦄ → ⦃ Syntax (sum ops) ⦄ → Free ops ℕ _
testCatch = throw {A = ⊤} tt >> pure 1 catch (λ _ → pure 42)

runTestCatch : ⊤ ⊎ ℕ
runTestCatch = run $ runHExc $ testCatch ⦃ here refl ⦄

data Listᴹ (ops : List Container) (A : Set) : Size → Set₁ where
  nil : Listᴹ ops A i
  cons : Free ops A _ → Free ops (Listᴹ ops A i) _ → Listᴹ ops A (↑ i)

pattern _∷ᴹ_ mx mxs = pure (cons mx mxs)
pattern []ᴹ         = pure nil

foo : Free ops (Listᴹ ops ℕ _) _
foo = (pure 42) ∷ᴹ []ᴹ

-- bar : Free ops (Listᴹ ops ℕ _) _ -- cannot return monadic list from scoped computation
-- bar = foo catch ?

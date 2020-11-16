{-# OPTIONS --cumulativity #-}

module LevelPolyEffects where

open import Level
open import Function     using (_∘_; _$_; const; case_of_)
open import Size         using (Size; ↑_; ∞)

open import Data.Empty   using (⊥)
open import Data.Maybe   using (Maybe; just; nothing; fromMaybe)
open import Data.Nat     using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit    using (⊤; tt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Container : Setω where
  constructor _◁_/_
  field
    Shape : (ℓ : Level) → Set (suc ℓ)
    Pos : ∀ {ℓ} → Shape ℓ → Set ℓ
    Ctx : ∀ {ℓ} → (s : Shape ℓ) → Pos s → Maybe (Set ℓ)
open Container public

_⊕_ : Container → Container → Container
Shape (F ⊕ G) = λ ℓ → Shape F ℓ ⊎ Shape G ℓ
Pos   (F ⊕ G) = [ Pos F , Pos G ]
Ctx (F ⊕ G) (inj₁ s) p = Ctx F s p
Ctx (F ⊕ G) (inj₂ s) p = Ctx G s p

fromMaybeℓ : ∀ {ℓ} → Set (suc ℓ) → Maybe (Set ℓ) → Set (suc ℓ)
fromMaybeℓ A nothing  = A
fromMaybeℓ A (just B) = B

⟦_⟧ : Container → {ℓ : Level} → (Set (suc ℓ) → Set (suc ℓ)) → Set (suc ℓ) → Set (suc ℓ)
⟦ C ⟧ {ℓ} F A = Σ[ s ∈ Shape C ℓ ] ((p : Pos C s) → F (fromMaybeℓ A (Ctx C s p)))

data Free (ℓ : Level) (C : Container) (A  : Set (suc ℓ)) : {Size} → Set (suc ℓ) where
  pure   : ∀ {i} → A → Free ℓ C A {i}
  impure : ∀ {i} → ⟦ C ⟧ {ℓ} (λ X → Free ℓ C X {i}) A → Free ℓ C A {↑ i}

Free′ : (ℓ : Level) → Container → Size → Set (suc ℓ) → Set (suc ℓ)
Free′ ℓ C i A = Free ℓ C A {i}

helper : ∀ {ℓ C i} {A B : Set (suc ℓ)} →
  (Free ℓ C A {i} → Free ℓ C B) → (s : Shape C ℓ) → (p : Pos C s) →
  Free ℓ C (fromMaybeℓ A (Ctx C s p)) {i} → Free ℓ C (fromMaybeℓ B (Ctx C s p))
helper {C = C} f s p v with Ctx C s p
... | nothing = f v
... | just _  = v

emap : ∀ {ℓ C i} {A : Set (suc ℓ)} {B : Set (suc ℓ)}
  → (Free ℓ C A {i} → Free ℓ C B) → ⟦ C ⟧ (Free′ ℓ C i) A → ⟦ C ⟧ (Free′ ℓ C ∞) B
emap {ℓ} {C} {F} f c = proj₁ c , λ p → helper {ℓ} {C} f (proj₁ c) p (proj₂ c p)

_>>=_ : ∀ {ℓ C i} {A B : Set (suc ℓ)} → Free ℓ C A {i} → (A → Free ℓ C B) → Free ℓ C B
pure x   >>= k = k x
impure x >>= k = impure (emap (_>>= k) x)

data Listᴹ (ℓ : Level) (C : Container) (A : Set (suc ℓ)) : Set (suc ℓ) where
  nil  : Listᴹ ℓ C A
  cons : Free ℓ C A → Free ℓ C (Listᴹ ℓ C A) → Listᴹ ℓ C A

infixr 5 _∷ᴹ_
pattern []ᴹ         = pure nil
pattern _∷ᴹ_ mx mxs = pure (cons mx mxs)

module Exc where
  data Excˢ (E : Set) (ℓ : Level) : Set (suc ℓ) where
    throwˢ : (e : E)           → Excˢ E ℓ
    catchˢ : (X : Set ℓ) → Excˢ E ℓ

  data ExcCatchᵖ (E : Set) {ℓ : Level} (X : Set ℓ) : Set ℓ where
    mainᵖ   : ExcCatchᵖ E X
    handleᵖ : (e : E) → ExcCatchᵖ E X
    contᵖ   : X → ExcCatchᵖ E X

  Excᵖ : ∀ {ℓ} → (E : Set) → Excˢ E ℓ → Set ℓ
  Excᵖ _ (throwˢ e) = ⊥
  Excᵖ E (catchˢ X) = ExcCatchᵖ E X

  Excᶜ : ∀ {E ℓ} → (s : Excˢ E ℓ) → Excᵖ E s → Maybe (Set ℓ)
  Excᶜ (catchˢ X) mainᵖ       = just X  -- the stored computation is of type Free ... X
  Excᶜ (catchˢ X) (handleᵖ e) = just X  -- the handler produces a value of type Free ... X
  Excᶜ (catchˢ X) (contᵖ x)   = nothing -- the continuation produces a Free ... A

  Exc : Set → Container
  Exc E = Excˢ E ◁ Excᵖ E / Excᶜ

  pattern Throw e = impure (throwˢ e , _)
  pattern Catch κ = impure (catchˢ _ , κ)

  throw : ∀ {ℓ E A} → E → Free ℓ (Exc E) A
  throw e = impure (throwˢ e , λ())

  _catch_ : ∀ {ℓ E} {A : Set ℓ} → Free ℓ (Exc E) A → (E → Free ℓ (Exc E) A) → Free ℓ (Exc E) A
  ma catch h = impure ((catchˢ _) , λ{ mainᵖ →  ma ; (handleᵖ e) → h e ; (contᵖ x) → pure x})

  -- Manually increase universe level ... (should be a type class or part of Container)
  -- --cumulativity simplifies this implementation quite a bit, but cannot help with this situation
  -- (see https://agda.readthedocs.io/en/latest/language/cumulativity.html#limitations)
  up : ∀ {E ℓ} {A : Set (suc ℓ)} → Free ℓ (Exc E) A → Free (suc ℓ) (Exc E) A
  up (pure x) = pure x
  up (impure (throwˢ e , pf)) = impure ((throwˢ e) , λ())
  up (impure (catchˢ X , pf)) = impure $ catchˢ X , λ where
    mainᵖ       → up (pf mainᵖ)
    (handleᵖ e) → up (pf (handleᵖ e))
    (contᵖ x)   → up (pf (contᵖ x))

  -- a second version of catch, that deals with "too large" values by increasing the level of Free
  _catch↑_ : ∀ {ℓ E} {A : Set (suc ℓ)} → Free ℓ (Exc E) A → (E → Free ℓ (Exc E) A) → Free (suc ℓ) (Exc E) A
  ma catch↑ h = impure ((catchˢ _) , λ{ mainᵖ → up ma ; (handleᵖ e) → up (h e) ; (contᵖ x) → pure x})

  runExc : ∀ {ℓ E} {A : Set (suc ℓ)} → Free ℓ (Exc E) A → E ⊎ A
  runExc (pure x)  = inj₂ x
  runExc (Throw e) = inj₁ e
  runExc (Catch κ) = case runExc (κ mainᵖ) of λ where
    (inj₁ e) → case runExc (κ (handleᵖ e)) of λ where
      (inj₁ e) → inj₁ e
      (inj₂ x) → runExc (κ (contᵖ x))
    (inj₂ x) → runExc (κ (contᵖ x))
open Exc using (Exc; runExc; throw; _catch_; _catch↑_; up)

-- corresponds to "42 : undefined" in Haskell
partialList : Free 0ℓ (Exc ⊤) (Listᴹ 0ℓ (Exc ⊤) ℕ)
partialList = pure 42 ∷ᴹ throw tt

-- We can capture a computation producing a Listᴹ for the price of increasing the level of the computation.
-- This probably hinders the composability of effectful programs, especially when dealing with different
-- levels forcing multiple @up@s.  :/
--                 ↓
checkHead : Free (suc 0ℓ) (Exc ⊤) (Listᴹ 0ℓ (Exc ⊤) ℕ)
checkHead = partialList catch↑ const []ᴹ

-- We can evaluate effects per constructor i.e. we can model deep effects :)
runCheckHead : runExc checkHead ≡ inj₂ (cons (pure 42) (throw tt))
runCheckHead = refl

-- Assumes that Listᴹ and Free have the same level. This is not the case if the list was passed to a scoped operation!
-- Dealing with these diverging levels could become quite complicated.
head : Free (0ℓ) (Exc ⊤) (Listᴹ 0ℓ (Exc ⊤) ℕ) → Free (0ℓ) (Exc ⊤) ℕ
head mxs = mxs >>= λ where
  nil         → throw tt
  (cons mx _) → mx

runHead : runExc (head partialList) ≡ inj₂ 42
runHead = refl

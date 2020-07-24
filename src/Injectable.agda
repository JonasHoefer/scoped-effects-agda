{-# OPTIONS --overlapping-instances #-}

module Injectable where

open import Function     using (id; _∘_; _$_)

open import Data.Bool    using (Bool; true; false)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.Empty   using (⊥)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ; _+_)
open import Data.Product using (Σ-syntax; _,_; _×_)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit    using (⊤; tt)

record Container : Set₁ where
  constructor
    _▶_
  field
    Shape : Set
    Pos : Shape → Set

⟦_⟧ : Container → Set → Set
⟦ S ▶ P ⟧ A = Σ[ s ∈ S ] (P s → A)

mapᶜ : {A B : Set} {C : Container} → (A → B) → ⟦ C ⟧ A → ⟦ C ⟧ B
mapᶜ f (s , pf) = s , f ∘ pf
{-# INLINE mapᶜ #-}

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

infixl 1 _>>=_
_>>=_ : {A B : Set} {C : Container} → Free C A → (A → Free C B) → Free C B
pure x          >>= k = k x
impure (s , pf) >>= k = impure (s , λ p → pf p >>= k)

infixl 1 _>>_
_>>_ : {A B : Set} {C : Container} → Free C A → Free C B → Free C B
ma >> mb = ma >>= λ _ → mb

infixl 4 _<$>_
_<$>_ : {A B : Set} {C : Container} → (A → B) → Free C A → Free C B
f <$> (pure x)          = pure (f x)
f <$> (impure (s , pf)) = impure (s ,  (f <$>_) ∘ pf )

infixl 4 _<*>_
_<*>_ : {A B : Set} {C : Container} → Free C (A → B) → Free C A → Free C B
mf <*> ma = mf >>= λ f → ma >>= λ a → pure (f a)

inject : {F G : Container} {A : Set} → ⦃ F ⊂ G ⦄ → ⟦ F ⟧ (Free G A) → Free G A
inject = impure ∘ inj

project : {F G : Container} {A : Set} → ⦃ F ⊂ G ⦄ → Free G A → Maybe (⟦ F ⟧ (Free G A))
project (pure   _) = nothing
project (impure x) = prj x

-- the empty effect
module Void where
  void : Container
  void = ⊥ ▶ λ()

  run : {A : Set} → Free void A → A
  run (pure x) = x
open Void using (void; run)

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

  solutions : {F : Container} {A : Set} → Free (nondet ⊕ F) A → Free F (List A)
  solutions (pure x) = pure (x ∷ [])
  solutions (impure (inj₁ failˢ   , pf)) = pure []
  solutions (impure (inj₁ choiceˢ , pf)) = _++_ <$> solutions (pf true) <*> solutions (pf false)
  solutions (impure (inj₂ s , pf)) = impure (s , solutions ∘ pf)

  fail : {A : Set} {F : Container} → ⦃ nondet ⊂ F ⦄ → Free F A
  fail = inject (failˢ , λ())

  _⁇_ : {A : Set} {F : Container} → ⦃ nondet ⊂ F ⦄ → Free F A → Free F A → Free F A
  p ⁇ q = inject (choiceˢ , λ{ false → p ; true → q})
open NonDet using (nondet; fail; _⁇_; solutions)

module Reader where
  data Shape (Γ : Set) : Set where
    askˢ : Shape Γ
    localˢ : (Γ → Γ) → Shape Γ -- correct?

  reader : Set → Container
  reader Γ = Shape Γ ▶ λ { askˢ → Γ ; (localˢ x) → ⊤ }

  runReader : {F : Container} {A Γ : Set} → Γ → Free (reader Γ ⊕ F) A → Free F A
  runReader γ (pure x) = pure x
  runReader γ (impure (inj₁ askˢ       , pf)) = runReader γ (pf γ)
  runReader γ (impure (inj₁ (localˢ f) , pf)) = runReader (f γ) (pf tt)
  runReader γ (impure (inj₂ s          , pf)) = impure (s , runReader γ ∘ pf)

  ask : {F : Container} {Γ : Set} → ⦃ reader Γ ⊂ F ⦄ → Free F Γ
  ask = inject (askˢ , pure)

  local : {F : Container} {Γ A : Set} → ⦃ reader Γ ⊂ F ⦄ → (Γ → Γ) → Free F A → Free F A
  local f ma = inject (localˢ f , λ tt → ma)
open Reader using (reader; runReader; local; ask)

module State where
  data Shape (S : Set) : Set where
    putˢ : S → Shape S
    getˢ : Shape S

  pos : (S : Set) → Shape S → Set
  pos S (putˢ _) = ⊤
  pos S getˢ     = S

  state : Set → Container
  state S = Shape S ▶ pos S

  runState : {F : Container} {A S : Set} → S → Free (state S ⊕ F) A → Free F (S × A)
  runState s₀ (pure x) = pure (s₀ , x)
  runState s₀ (impure (inj₁ (putˢ s) , pf)) = runState s (pf tt)
  runState s₀ (impure (inj₁ getˢ     , pf)) = runState s₀ (pf s₀)
  runState s₀ (impure (inj₂ s        , pf)) = impure (s , runState s₀ ∘ pf )

  get : {F : Container} {S : Set} → ⦃ state S ⊂ F ⦄ → Free F S
  get = inject (getˢ , pure)

  put : {F : Container} {S : Set} → ⦃ state S ⊂ F ⦄ → S → Free F ⊤
  put s = inject (putˢ s , λ tt → pure tt)
open State using (state; runState; get; put)

select : {A : Set} {F : Container} → ⦃ nondet ⊂ F ⦄ → List A → Free F A
select []       = fail
select (x ∷ xs) = pure x ⁇ select xs

sumTwo : {F : Container} → ⦃ nondet ⊂ F ⦄ → List ℕ → Free F ℕ
sumTwo xs = do
  x ← select xs
  y ← select xs
  pure (x + y)

testNonDet : List ℕ
testNonDet = run (solutions (sumTwo (3 ∷ 4 ∷ 7 ∷ [])))

tick : {F : Container} → ⦃ state ℕ ⊂ F ⦄ → Free F ⊤
tick = get >>= λ n → put (n + 1)

testState : ℕ × ⊤
testState = run (runState 0 (tick >> tick >> tick))

localComp : {F : Container} → ⦃ reader ℕ ⊂ F ⦄ → Free F ℕ
localComp = local (λ x → 1 + x) ask

testReader : ℕ
testReader = run $ runReader 1 $ do
  x ← ask
  y ← localComp
  z ← ask --wrong!
  pure $ x + y + z

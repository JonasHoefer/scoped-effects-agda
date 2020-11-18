module TypingEnv where

open import Level using (Level)

open import Function using (_∘_; _$_; case_of_)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; _∷_; []; _++_) renaming (map to mapᴸ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤; tt)

----------------------------------------------------
-- (unfinished) Sketch of typing environment idea --
----------------------------------------------------

-- By storing the captured types not directly, but indexing over an environment, it is possible to avoid the size issues.
-- Sadly, the resulting implementation is rather unusable because type cannot be infered automatically and writing helper
-- functions to infer environemnts is not feasable.
-- Furthermore, storing the whole structure of a programs in its type is not optimal because programs producing values of the
-- same type using different oeprations have different types.

variable
  ℓ : Level
  A B E X : Set

record Container : Set₁ where
  constructor _◁_
  field
    Shape : Set
    Pos : Shape → Set
open Container

_⊕_ : Container → Container → Container
(S₁ ◁ P₁) ⊕ (S₂ ◁ P₂) = (S₁ ⊎ S₂) ◁ [ P₁ , P₂ ]

⟦_⟧ : Container → Set ℓ → Set ℓ
⟦ S ◁ P ⟧ X = Σ[ s ∈ S ] (P s → X)

map : {A B : Set ℓ} {C : Container} → (A → B) → ⟦ C ⟧ A → ⟦ C ⟧ B
map f c = π₁ c , f ∘ (π₂ c)
{-# INLINE map #-}

record Effect : Set₁ where
  field
    Ops Scps : Container
open Effect

_∪_ : Effect → Effect → Effect
Ops  (E₁ ∪ E₂) = Ops  E₁ ⊕ Ops  E₂
Scps (E₁ ∪ E₂) = Scps E₁ ⊕ Scps E₂

data Env (Σ : Effect) (A : Set) : Set₁ where
  ∙     : A → Env Σ A
  _,-   : ⟦ Ops  Σ ⟧ (Env Σ A) → Env Σ A
  _,_+_ : (X : Set) → ⟦ Scps Σ ⟧ (Env Σ X) → Env Σ A → Env Σ A

data Prog (Σ : Effect) (A : Set) : Env Σ A → Set where
  var : (a : A) → Prog Σ A (∙ a)
  op  : (op : Shape (Ops Σ)) →
        -- ^ Current operation symbol
        {Γ : Pos (Ops Σ) op → Env Σ A} →
        -- ^ Typing environment for each subcomputation
        (κ : (p : Pos (Ops Σ) op) → Prog Σ A (Γ p)) →
        -- ^ Subcomputations
        Prog Σ A ((op , Γ) ,-)
  scp : (op : Shape (Scps Σ)) →
        -- ^ Current scope operation symbol
        {Γ : Pos (Scps Σ) op → Env Σ X} →
        -- ^ typing environment for each subcomputation
        {Γ′ : Env Σ A} →
        -- ^ typing environment for continuation
        (ω : (p : Pos (Scps Σ) op) → Prog Σ X (Γ p)) →
        -- ^ Subcomputations
        (κ : X → Prog Σ A Γ′) →
        -- ^ Continuation
        Prog Σ A (X , (op , Γ) + Γ′)

variable
  Σ : Effect
  Γ Γ′ : Env Σ A

_[∙/_] : Env Σ A → (A → Env Σ B) → Env Σ B
(∙ a)       [∙/ Γ′ ] = Γ′ a
(Γ ,-)      [∙/ Γ′ ] = map (_[∙/ Γ′ ]) Γ ,-
(X , Γ + Δ) [∙/ Γ′ ] = X , Γ + (Δ [∙/ Γ′ ])

_>>=_ : {Γ′ : A → Env Σ B} → Prog Σ A Γ → ((a : A) → Prog Σ B (Γ′ a)) → Prog Σ B (Γ [∙/ Γ′ ])
var x       >>= k = k x
op op₁ κ    >>= k = op op₁ ((_>>= k) ∘ κ)
scp op₁ ω κ >>= k = scp op₁ ω ((_>>= k) ∘ κ)

-- module Exc where
  -- Exc : Set → Effect
  -- Shape (Ops  (Exc E))    = E
  -- Pos   (Ops  (Exc E)) _  = ⊥
  -- Shape (Scps (Exc E))    = ⊤
  -- Pos   (Scps (Exc E)) tt = ⊤ ⊎ E
-- 
  -- throw : (e : E) → Prog (Exc E) A ((e , λ()) ,-)
  -- throw e = op e λ()
-- 
  -- infix 0 _catch_
  -- _catch_ : Prog (Exc E) A Γ → (E → Prog (Exc E) A Γ′) → Prog (Exc E) A ((tt , λ{ (inj₁ _) → Γ ; (inj₂ _) → Γ′ }) + ∙ , A)
  -- p catch h = scp tt (λ{(inj₁ tt) → p ; (inj₂ e)  → h e }) var
-- 
  -- foo : Prog (Exc ⊤) ℕ _
  -- foo = throw tt catch λ _ → var 42
-- 
  -- runExc : Prog (Exc E) A Γ → E ⊎ A
  -- runExc (var x)      = inj₂ x
  -- runExc (op e _)     = inj₁ e
  -- runExc (scp tt ω κ) = case runExc (ω (inj₁ tt)) of λ where
    -- (inj₁ e) → case runExc (ω (inj₂ e)) of λ where
      -- (inj₁ e) → inj₁ e
      -- (inj₂ x) → runExc (κ x)
    -- (inj₂ x) → runExc (κ x)
-- 
-- --  runExcΓ : Env (Exc E ∪ Σ) → Env Σ
-- --  runExcΓ         ∙                       = ∙
-- --  runExcΓ         ((inj₁ e , _) ,-)       = ∙
-- --  runExcΓ         ((inj₂ s , Γ) ,-)       = (s , runExcΓ ∘ Γ) ,-
-- --  runExcΓ         ((inj₁ tt , Γ) + Δ , X) = {!!}
-- --  runExcΓ {E = E} ((inj₂ s  , Γ) + Δ , X) = (s , runExcΓ ∘ Γ) + runExcΓ Δ , (E ⊎ X)
-- --
-- --  runExc″ : Prog (Exc E ∪ Σ) A Γ → Prog Σ (E ⊎ A) (runExcΓ Γ)
-- --  runExc″ (var x)             = var (inj₂ x)
-- --  runExc″ (op (inj₁ e) _)     = var (inj₁ e)
-- --  runExc″ (op (inj₂ s) κ)     = op s (runExc″ ∘ κ)
-- --  runExc″ (scp (inj₁ tt) ω κ) = {!!}
-- --  runExc″ (scp (inj₂ s ) ω κ) = {!!}
-- --
-- --  runExc′ : Prog (Exc E ∪ Σ) A Γ → Prog Σ (E ⊎ A) {!runExcΓ Γ!}
-- --  runExc′ (var x)         = var (inj₂ x)
-- --  runExc′ (op (inj₁ e) _) = var (inj₁ e)
-- --  runExc′ (op (inj₂ s) κ) = {!!} -- op s (runExc′ ∘ κ)
-- --  runExc′ (scp (inj₁ tt) ω κ) = runExc′ (ω (inj₁ tt)) >>= λ where
-- --    (inj₁ e) → runExc′ (ω (inj₂ e)) >>= λ where
-- --      (inj₁ e) → var (inj₁ e)
-- --      (inj₂ x) → runExc′ (κ x)
-- --    (inj₂ x) → runExc′ (κ x)
-- --  runExc′ (scp (inj₂ s ) ω κ) = {!!}
-- open Exc using (Exc; runExc; throw; _catch_)
-- 
module Nondet where
  data Nondetˢ : Set where failˢ ⁇ˢ : Nondetˢ
  data Onceˢ : Set where onceˢ : Onceˢ

  Nondet : Effect
  Shape (Ops Nondet)        = Nondetˢ
  Pos   (Ops Nondet)  failˢ = ⊥
  Pos   (Ops Nondet)  ⁇ˢ    = Bool
  Shape (Scps Nondet)       = Onceˢ
  Pos   (Scps Nondet) onceˢ = ⊤

  pattern Choice κ     = op (inj₁ ⁇ˢ) κ
  pattern Fail         = op (inj₁ failˢ) _
  pattern Once ω κ     = scp (inj₁ onceˢ) ω κ
  pattern Other s κ    = op (inj₂ s) κ
  pattern OtherS s ω κ = scp (inj₂ s) ω κ

  runNondetΓ : Env (Nondet ∪ Σ) A → Env Σ (List A)
  runNondetΓ (∙ a)                      = ∙ (a ∷ [])
  runNondetΓ ((inj₁ failˢ     , Γ) ,-)  = ∙ []
  runNondetΓ ((inj₁ ⁇ˢ        , Γ) ,-)  = runNondetΓ (Γ true) [∙/ (λ x → runNondetΓ (Γ false) [∙/ (λ y → ∙ (x ++ y)) ]) ]
  runNondetΓ ((inj₂ s         , Γ) ,-)  = (s , runNondetΓ ∘ Γ) ,-
  runNondetΓ (X , (inj₁ onceˢ , Γ) + Δ) = runNondetΓ (Γ tt) [∙/ (λ{ [] → ∙ [] ; (x ∷ _) → runNondetΓ Δ }) ]
  runNondetΓ (X , (inj₂ s     , Γ) + Δ) = List X , {!!} + {!!}

  runNondet : Prog (Nondet ∪ Σ) A Γ → Prog Σ (List A) (runNondetΓ Γ)
  runNondet (var x)        = var (x ∷ [])
  runNondet Fail           = var []
  runNondet (Choice κ)     = runNondet (κ true) >>= λ l → runNondet (κ false) >>= λ r → var (l ++ r)
  runNondet (Other s κ)    = op s (runNondet ∘ κ)
  runNondet (Once ω κ)     = runNondet (ω tt) >>= λ where
    []      → var []
    (x ∷ _) → runNondet (κ x)
  runNondet (OtherS s ω κ) = {!!}

  _⁇_ : Prog (Nondet ∪ Σ) A Γ → Prog (Nondet ∪ Σ) A Γ′ → Prog (Nondet ∪ Σ) A ((inj₁ ⁇ˢ , (if_then Γ else Γ′)) ,-)
  p ⁇ q = op (inj₁ ⁇ˢ) λ where
   false → q
   true  → p

  fail : Prog (Nondet ∪ Σ) A ((inj₁ failˢ , λ()) ,-)
  fail = op (inj₁ failˢ) λ()

  coin : Prog (Nondet ∪ Σ) ℕ _
  coin = var 0 ⁇ var 1

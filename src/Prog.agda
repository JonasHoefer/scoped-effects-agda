module Prog where

open import Function         using (_∘_; id)

open import Category.Functor using (RawFunctor)
open import Category.Monad   using (RawMonad)

open import Data.List        using (List; _∷_; []) public
open import Data.Nat         using (ℕ; suc)        public
open import Data.Product     using (_×_; _,_)      public

open import Variables
open import Effect


-- Monad from "Syntax and Semantics for Operations with Scoeps" by Piróg et al.

data Prog (effs : List Effect) (A : Set) : Set where
  var : A                                       → Prog effs A
  op  : ⟦ ops  effs ⟧ (Prog effs A)             → Prog effs A
  scp : ⟦ scps effs ⟧ (Prog effs (Prog effs A)) → Prog effs A

-- n-fold iteration of f
--
-- fⁿ(A) = (id ∘ f ∘ ⋯ ∘ f) (A)
infixl 10 _^_
_^_ : ∀ {ℓ} {C : Set ℓ} → (C → C) → ℕ → C → C
(f ^ 0)       x = x
(f ^ suc n) x = f ((f ^ n) x)

-- fold and induction scheme for nested data type following Fu and Selinger

foldP : (P : ℕ → Set) → ∀ n →
  (A                                       → P 0      ) →
  (∀ {n} → P n                             → P (suc n)) →
  (∀ {n} → ⟦ ops  effs ⟧ (P (suc n))       → P (suc n)) →
  (∀ {n} → ⟦ scps effs ⟧ (P (suc (suc n))) → P (suc n)) →
  (Prog effs ^ n) A → P n
foldP P 0       a v o s x       = a x
foldP P (suc n) a v o s (var x) = v (     foldP P n             a v o s  x)
foldP P (suc n) a v o s (op  x) = o (map (foldP P (suc n)       a v o s) x)
foldP P (suc n) a v o s (scp x) = s (map (foldP P (suc (suc n)) a v o s) x)

inP : (P : (n : ℕ) → (Prog effs ^ n) A → Set) → ∀ n →
  (∀ {x}       → A                                                 → P 0 x                  ) →
  (∀ {n x}     → P n x                                             → P (suc n) (var x)      ) →
  (∀ {n} s {κ} → ((p : Pos (ops  effs) s) → P (suc n)       (κ p)) → P (suc n) (op  (s , κ))) →
  (∀ {n} s {κ} → ((p : Pos (scps effs) s) → P (suc (suc n)) (κ p)) → P (suc n) (scp (s , κ))) →
  (x : (Prog effs ^ n) A) → P n x
inP P 0       a v o s x             = a x
inP P (suc n) a v o s (var x)       = v   (inP P n             a v o s x)
inP P (suc n) a v o s (op  (c , κ)) = o c (inP P (suc n)       a v o s ∘ κ)
inP P (suc n) a v o s (scp (c , κ)) = s c (inP P (suc (suc n)) a v o s ∘ κ)

mapⁿ : ∀ n → (A → B) → (Prog effs ^ n) A → (Prog effs ^ n) B
mapⁿ {B = B} n f = foldP (λ i → (Prog _ ^ i) B) n f var op scp

functor : RawFunctor (Prog effs)
RawFunctor._<$>_ functor = mapⁿ 1

>>=ₙ-P : ∀ {effs B} → ℕ → Set
>>=ₙ-P {effs} {B} 0       = Prog effs B
>>=ₙ-P {effs} {B} (suc n) = (Prog effs ^ suc n) B

>>=ₙ-var : ∀ {effs B} n → >>=ₙ-P {effs} {B} n → >>=ₙ-P {effs} {B} (suc n)
>>=ₙ-var 0       x = x
>>=ₙ-var (suc n) x = var x

>>=ₙ : ∀ {effs A B} n → (Prog effs ^ suc n) A → (A → Prog effs B) → (Prog effs ^ suc n) B
>>=ₙ {effs} {A} {B} n ma k = foldP (>>=ₙ-P {effs} {B}) (suc n) k (λ {n} → >>=ₙ-var n) op scp ma

monad : RawMonad (Prog effs)
monad = record { return = var ; _>>=_ = >>=ₙ 0 }

-- Smart constructors for operations with and without scopes

Op : ⦃ E ∈ effs ⦄ → ⟦ Ops E ⟧ (Prog effs A) → Prog effs A
Op ⦃ p ⦄ = op ∘ inj (ops-inj p)

Scp : ⦃ E ∈ effs ⦄ → ⟦ Scps E ⟧ (Prog effs (Prog effs A)) → Prog effs A
Scp ⦃ p ⦄ = scp ∘ inj (scps-inj p)

-- Utility functions for handling effects

pattern Other s κ = (inj₂ s , κ)

run : Prog [] A → A
run (var x) = x



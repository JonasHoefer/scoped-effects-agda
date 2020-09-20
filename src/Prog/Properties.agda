module Prog.Properties where

open import Function                              using (id; _∘_; const)
open import Level                                 using (Level)

open import Category.Monad                        using (RawMonad)
open        RawMonad ⦃...⦄                        renaming (_⊛_ to _<*>_)

open import Data.Nat                              using (ℕ; suc)
open import Data.Product                          using (_,_)

import      Relation.Binary.PropositionalEquality as Eq
open        Eq                                    using (_≡_; refl; cong)
open        Eq.≡-Reasoning                        using (begin_; _∎; step-≡; _≡⟨⟩_)

open import Variables
open import Prog                                  using (Prog; var; op; scp; inP; foldP; mapⁿ; _^_; >>=ₙ-var; >>=ₙ)
open import Prog.Instances

postulate
  extensionality : ∀ {ℓ ℓ′ : Level} {A : Set ℓ} {B : A → Set ℓ′} {f g : (x : A) → B x}
      → (∀ (x : A) → f x ≡ g x) → f ≡ g

----------------
-- Monad Laws --
----------------

>>=-identˡ : ∀ {A B : Set} {a} {k : A → Prog effs B} →
  (pure a >>= k) ≡ k a
>>=-identˡ = refl

>>=-identʳ : {A : Set} (ma : Prog effs A) →
  (ma >>= pure) ≡ ma
>>=-identʳ {effs} {A} = inP P 1
    (const refl)
    (λ {n} → varₙ n)
    (λ s → cong (op  ∘ (s ,_)) ∘ extensionality)
    (λ s → cong (scp ∘ (s ,_)) ∘ extensionality)
  where
    P : (n : ℕ) → (Prog effs ^ n) A → Set
    P 0       x = x ≡ x
    P (suc n) x = foldP _ (suc n) var (λ {n} → >>=ₙ-var {effs} {A} n) op scp x ≡ x

    varₙ : ∀ n {x : (Prog effs ^ n) A} → P n x → P (suc n) (var x)
    varₙ 0       x = refl
    varₙ (suc n) x = cong var x

>>=-assoc : ∀ {effs A B C} → (f : A → Prog effs B) → (g : B → Prog effs C) → (ma : Prog effs A) →
  (ma >>= f >>= g) ≡ (ma >>= (λ x → f x >>= g))
>>=-assoc {effs} {A} {B} {C} f g = inP P 1
    (const refl)
    (λ {n} → varₙ n)
    (λ s → cong (op  ∘ (s ,_)) ∘ extensionality)
    (λ s → cong (scp ∘ (s ,_)) ∘ extensionality)
  where
    P : ∀ n → (Prog effs ^ n) A → Set
    P 0       x = x ≡ x
    P (suc n) x = (>>=ₙ n (>>=ₙ n x f) g) ≡ (>>=ₙ n x (λ y → (>>=ₙ 0 (f y) g)))

    varₙ : ∀ n {x : (Prog effs ^ n) A} → P n x → P (suc n) (var x)
    varₙ 0       x = refl
    varₙ (suc n) x = cong var x

-------------------------------------------
-- Functor Laws (in terms of Monad laws) --
-------------------------------------------

fmap-id : ∀ {effs} {A B : Set} → (ma : Prog effs A) → (id <$> ma) ≡ ma
fmap-id ma = begin
  (id <$> ma)               ≡⟨⟩
  (ma >>= λ a → var (id a)) ≡⟨⟩
  (ma >>= var)              ≡⟨ >>=-identʳ ma ⟩
  ma                        ∎

fmap-∘ : ∀ {effs} {A B C : Set} → (f : B → C) → (g : A → B) → (ma : Prog effs A) → ((f ∘ g) <$> ma) ≡ (f <$> (g <$> ma))
fmap-∘ f g ma rewrite >>=-assoc (var ∘ g) (var ∘ f) ma = refl

-----------------------------------------------
-- Applicative Laws (in terms of monad laws) --
-----------------------------------------------

pure-<*> : ∀ {effs} {A B : Set} → (f : A → B) → (ma : Prog effs A) → (var f <*> ma) ≡ (f <$> ma)
pure-<*> f ma = refl

-- TOOD: finish

{-# OPTIONS --overlapping-instances #-}

module Effect.Nondet.Properties where

open import Function using (_$_; _∘_; id; const)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.List  using (List; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Tree

open import Variables
open import Effect
open import Effect.Nondet
open import Prog
open import Prog.Instances
open import Prog.Properties

import      Relation.Binary.PropositionalEquality as Eq
open        Eq using (_≡_; refl; cong; sym; trans)
open        Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


fail>>= : ∀ {effs A B} → (k : A → Prog (Nondet ∷ effs) B) →
  runNondet (fail >>= k) ≡ runNondet fail
fail>>= k = refl

⁇-algebraic : ∀ {effs A B} → (p q : Prog (Nondet ∷ effs) A) → (k : A → Prog (Nondet ∷ effs) B) →
  runNondet ((p ⁇ q) >>= k) ≡ runNondet (p >>= k ⁇ q >>= k)
⁇-algebraic p q k = refl

⁇-identˡ : ∀ {effs A} → (ma : Prog (Nondet ∷ effs) A) →
  runNondet (fail ⁇ ma) ≡ runNondet ma
⁇-identˡ {effs} {A} ma = begin
    runNondet (fail ⁇ ma)                                                ≡⟨⟩
    dfs empty <$> runNondet′ (fail ⁇ ma)                                 ≡⟨⟩
    dfs empty <$> (choice nothing <$> runNondet′ fail <*> runNondet′ ma) ≡⟨⟩
    dfs empty <$> (choice nothing <$> var failed      <*> runNondet′ ma) ≡⟨⟩
    dfs empty <$> (var (choice nothing failed)        <*> runNondet′ ma) ≡⟨⟩
    dfs empty <$> (choice nothing failed              <$> runNondet′ ma)
  ≡⟨ sym (fmap-∘ (dfs empty) (choice nothing failed) (runNondet′ ma)) ⟩
    (dfs empty ∘ choice nothing failed)               <$> runNondet′ ma  ≡⟨⟩
    dfs empty <$> runNondet′ ma                                          ≡⟨⟩
    runNondet ma                                                         ∎

⁇-identʳ : ∀ {effs A} → (ma : Prog (Nondet ∷ effs) A) →
  runNondet (ma ⁇ fail) ≡ runNondet ma
⁇-identʳ {effs} {A} ma = begin
    runNondet (ma ⁇ fail)                                                                     ≡⟨⟩
    dfs empty <$> (choice nothing <$> runNondet′ ma <*> var failed)                           ≡⟨⟩
    dfs empty <$> ((runNondet′ ma >>= var ∘ choice nothing) <*> var failed)                   ≡⟨⟩
    dfs empty <$> (runNondet′ ma >>= var ∘ choice nothing >>= _<$> var failed)                ≡⟨⟩
    dfs empty <$> (runNondet′ ma >>= var ∘ choice nothing >>= λ f → var (f failed))
  ≡⟨ cong (dfs empty <$>_) (>>=-assoc (var ∘ choice nothing) (λ f → var (f failed)) (runNondet′ ma)) ⟩
    dfs empty <$> (runNondet′ ma >>= (λ x → var (choice nothing x) >>= λ f → var (f failed))) ≡⟨⟩
    dfs empty <$> (runNondet′ ma >>= (λ x → var (choice nothing x failed)))                   ≡⟨⟩
    ((runNondet′ ma >>= (λ x → var (choice nothing x failed))) >>= var ∘ dfs empty)
  ≡⟨ >>=-assoc (λ x → var (choice nothing x failed)) (var ∘ dfs empty) (runNondet′ ma) ⟩
    (runNondet′ ma >>= (λ x → var (choice nothing x failed) >>= var ∘ dfs empty))             ≡⟨⟩
    (runNondet′ ma >>= (λ x → var (dfs empty (choice nothing x failed))))                     ≡⟨⟩
    (runNondet′ ma >>= (λ x → var (dfs empty x ++ [])))
  ≡⟨ cong (runNondet′ ma >>=_) (extensionality λ x → cong var (++-identityʳ $ dfs empty x)) ⟩
    (runNondet′ ma >>= (λ x → var (dfs empty x)))                                             ≡⟨⟩
    runNondet ma                                                                              ∎

-- ⁇ should also be associative and therefore a monoid. Proof should follow structure of ⁇-identʳ and use ++assoc.
-- this is NOT a law in "Purely Functional Lazy Non-deterministic Programming", because it does nt hold in a probabilistic context.

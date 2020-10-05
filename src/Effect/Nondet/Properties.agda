{-# OPTIONS --overlapping-instances #-}

module Effect.Nondet.Properties where

open import Function using (_$_; _∘_; id; const)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.List  using (List; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
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

-- could be simpler (expand p and q in opposite order to avoid extensionality)
⁇-++ : ∀ {effs A} → (p q : Prog (Nondet ∷ effs) A) →
  runNondet (p ⁇ q) ≡ ⦇ runNondet p ++ runNondet q ⦈
⁇-++ p q = begin
    runNondet (p ⁇ q)
  ≡⟨⟩
    (dfs empty <$> (choice nothing <$> runNondet′ p <*> runNondet′ q))
  ≡⟨⟩
    (dfs empty <$> (choice nothing <$> runNondet′ p >>= λ cp → runNondet′ q >>= var ∘ cp))
  ≡⟨⟩
    (dfs empty <$> (runNondet′ p >>= var ∘ choice nothing >>= λ cp → runNondet′ q >>= var ∘ cp))
  ≡⟨ cong (dfs empty <$>_) (>>=-assoc (var ∘ choice nothing) (λ cp → runNondet′ q >>= var ∘ cp) (runNondet′ p)) ⟩
    (dfs empty <$> (runNondet′ p >>= λ p → var (choice nothing p) >>= λ cp → runNondet′ q >>= var ∘ cp))
  ≡⟨⟩
    (dfs empty <$> (runNondet′ p >>= λ p → runNondet′ q >>= var ∘ choice nothing p))
  ≡⟨⟩
    (runNondet′ p >>= (λ p → runNondet′ q >>= var ∘ choice nothing p) >>= var ∘ dfs empty)
  ≡⟨ >>=-assoc (λ p → runNondet′ q >>= var ∘ choice nothing p) (var ∘ dfs empty) (runNondet′ p) ⟩
    (runNondet′ p >>= λ p → runNondet′ q >>= var ∘ choice nothing p >>= var ∘ dfs empty)
  ≡⟨ cong (runNondet′ p >>=_) (extensionality (λ p → >>=-assoc (var ∘ choice nothing p) (var ∘ dfs empty) (runNondet′ q))) ⟩
    (runNondet′ p >>= λ p → runNondet′ q >>= λ q → var (choice nothing p q) >>= var ∘ dfs empty)
  ≡⟨⟩
    (runNondet′ p >>= λ p → runNondet′ q >>= λ q → var (dfs empty p ++ dfs empty q))
  ≡⟨⟩
    (runNondet′ p >>= λ p → var (dfs empty p) >>= λ p → runNondet′ q >>= λ q → var (p ++ dfs empty q) )
  ≡⟨ sym (>>=-assoc (var ∘ dfs empty) _ (runNondet′ p)) ⟩
    (runNondet′ p >>= var ∘ dfs empty >>= λ p → runNondet′ q >>= λ q → var (p ++ dfs empty q) )
  ≡⟨⟩
    (runNondet p >>= λ p → runNondet′ q >>= λ q → var (dfs empty q) >>= var ∘ (p ++_) )
  ≡⟨ cong (runNondet p >>=_) (extensionality λ p → sym (>>=-assoc (var ∘ dfs empty) (var ∘ (p ++_)) (runNondet′ q))) ⟩
    (runNondet p >>= λ p → runNondet′ q >>= var ∘ dfs empty >>= var ∘ (p ++_) )
  ≡⟨⟩
    (runNondet p >>= λ p → runNondet q >>= var ∘ (p ++_) )
  ≡⟨⟩
    (runNondet p >>= λ p → var (p ++_) >>= λ p++ → runNondet q >>= var ∘ p++ )
  ≡⟨ sym (>>=-assoc (var ∘ _++_) _ (runNondet p)) ⟩
    (runNondet p >>= var ∘ _++_ >>= λ p++ → runNondet q >>= var ∘ p++ )
  ≡⟨⟩
    (_++_ <$> runNondet p >>= λ p++ → runNondet q >>= var ∘ p++ )
  ≡⟨⟩
    (_++_ <$> runNondet p <*> runNondet q)
  ≡⟨⟩
    ⦇ runNondet p ++ runNondet q ⦈
  ∎

-- ⁇ should also be associative and therefore a monoid.
-- this is NOT a law in "Purely Functional Lazy Non-deterministic Programming", because it does not hold in a probabilistic context.

⁇-assoc : ∀ {effs A} → (p q r : Prog (Nondet ∷ effs) A) →
  runNondet ((p ⁇ q) ⁇ r) ≡ runNondet (p ⁇ (q ⁇ r))
⁇-assoc p q r = begin
    runNondet ((p ⁇ q) ⁇ r)
  ≡⟨ ⁇-++ (p ⁇ q) r ⟩
    ⦇ runNondet (p ⁇ q) ++ runNondet r ⦈
  ≡⟨ cong (λ t → ⦇ t ++ runNondet r ⦈ ) (⁇-++ p q) ⟩
    ⦇ ⦇ runNondet p ++ runNondet q ⦈ ++ runNondet r ⦈
  ≡⟨⟩
    ((runNondet p >>= var ∘ _++_ >>= λ p++ → runNondet q >>= var ∘ p++) >>= var ∘ _++_ >>= λ pq++ → runNondet r >>= var ∘ pq++)
  ≡⟨ cong (λ t → t >>= var ∘ _++_ >>= λ pq++ → runNondet r >>= var ∘ pq++) (>>=-assoc (var ∘ _++_) _ (runNondet p)) ⟩
    (runNondet p >>= (λ p → runNondet q >>= var ∘ (p ++_)) >>= var ∘ _++_ >>= λ pq++ → runNondet r >>= var ∘ pq++)
  ≡⟨ >>=-assoc (var ∘ _++_) (λ pq++ → runNondet r >>= var ∘ pq++) (runNondet p >>= (λ p → runNondet q >>= var ∘ (p ++_))) ⟩
    (runNondet p >>= (λ p → runNondet q >>= var ∘ (p ++_)) >>= λ pq → runNondet r >>= var ∘ (pq ++_))
  ≡⟨ >>=-assoc (λ p → runNondet q >>= var ∘ (p ++_)) (λ pq → runNondet r >>= var ∘ (pq ++_)) (runNondet p) ⟩
    (runNondet p >>= λ p → runNondet q >>= var ∘ (p ++_) >>= λ pq → runNondet r >>= var ∘ (pq ++_))
  ≡⟨ cong (runNondet p >>=_) (extensionality λ p → >>=-assoc (var ∘ (p ++_)) (λ pq → runNondet r >>= var ∘ (pq ++_)) (runNondet q)) ⟩
    (runNondet p >>= λ p → runNondet q >>= λ q → runNondet r >>= λ r → var ((p ++ q) ++ r))
  ≡⟨ (cong (runNondet p >>=_) $ extensionality λ p → cong (runNondet q >>=_) $ extensionality λ q → cong (runNondet r >>=_) $ extensionality (λ r → cong var (++-assoc p q r))) ⟩
    (runNondet p >>= λ p → runNondet q >>= λ q → runNondet r >>= λ r → var (p ++ (q ++ r)))
  ≡⟨ cong (runNondet p >>=_) (extensionality λ p → cong (runNondet q >>=_) (extensionality λ q → sym (>>=-assoc (var ∘ (q ++_)) (var ∘ (p ++_)) (runNondet r)))) ⟩
    (runNondet p >>= λ p → runNondet q >>= λ q → runNondet r >>= var ∘ (q ++_) >>= var ∘ (p ++_))
  ≡⟨ cong (runNondet p >>=_) (extensionality (λ p → sym (>>=-assoc (var ∘ _++_) (λ q++ → runNondet r >>= var ∘ q++ >>= var ∘ (p ++_)) (runNondet q)))) ⟩
    (runNondet p >>= λ p → runNondet q >>= var ∘ _++_ >>= λ q++ → runNondet r >>= var ∘ q++ >>= var ∘ (p ++_))
  ≡⟨ cong (runNondet p >>=_) (extensionality (λ p → sym $ >>=-assoc (λ q++ → runNondet r >>= var ∘ q++) (var ∘ (p ++_))  (runNondet q >>= (var ∘ _++_)))) ⟩
    (runNondet p >>= λ p → runNondet q >>= var ∘ _++_ >>= (λ q++ → runNondet r >>= var ∘ q++) >>= var ∘ (p ++_))
  ≡⟨ sym (>>=-assoc (var ∘ _++_) _ (runNondet p)) ⟩
    (runNondet p >>= var ∘ _++_ >>= λ p++ → (runNondet q >>= var ∘ _++_ >>= λ q++ → runNondet r >>= var ∘ q++) >>= var ∘ p++)
  ≡⟨⟩
    ⦇ runNondet p ++ ⦇ runNondet q ++ runNondet r ⦈ ⦈
  ≡⟨ cong (λ t → ⦇ runNondet p ++ t ⦈) (sym $ ⁇-++ q r) ⟩
    ⦇ runNondet p ++ runNondet (q ⁇ r) ⦈
  ≡⟨ sym $ ⁇-++ p (q ⁇ r) ⟩
    runNondet (p ⁇ (q ⁇ r))
  ∎


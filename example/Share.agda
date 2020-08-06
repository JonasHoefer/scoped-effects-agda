{-# OPTIONS --overlapping-instances #-}

module Share where

open import Function                              using (_$_)
open import Size                                  using (Size; ↑_)

open import Data.List                             using (List; _∷_; [])
open import Data.MList                            using (Listᴹ; _∷ᴹ_; []ᴹ; _++_; head; sum)
open import Data.Nat                              using (ℕ; _+_)
open import Data.Product                          using (_×_; _,_)

open import Container                             using (Container)
open import Free
open import Injectable                            using (_⊂_)

open import Effect.Nondet                         using (Nondet; solutions; select; _⁇_)
open import Effect.State                          using (State; evalState)
open import Effect.Share                          using (Share; share; runCTC; nf)
open import Effect.Void                           using (run)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

coin : {F : Container} → ⦃ Nondet ⊂ F ⦄ → Free F ℕ
coin = pure 0 ⁇ pure 1

addM : ∀ {F : Container} → Free F ℕ → Free F ℕ → Free F ℕ
addM x y = (_+_) <$> x ⊛ y
  where open RawMonad freeMonad

module _ {F : Container} ⦃ _ : State (ℕ × ℕ) ⊂ F ⦄ ⦃ _ : Share ⊂ F ⦄ ⦃ _ : Nondet ⊂ F ⦄ where
  open RawMonad (freeMonad {F})

  -- | Shares the result of a non deterministic computation.
  coin*2 : Free F ℕ
  coin*2 = do
    x ← share coin
    addM x x

  -- | Shares results of computations using shared arguments.
  nested-sharing : Free F ℕ
  nested-sharing = share (share coin >>= λ fx → addM fx fx) >>= λ fy → addM fy fy

  add-shared-coin-clash : Free F ℕ
  add-shared-coin-clash = share (share coin >>= λ fx → addM fx fx) >>= λ fy → share coin >>= λ fz → addM fy fz

  share-list : Free F (Listᴹ F ℕ)
  share-list = do
    xs ← share (coin ∷ᴹ []ᴹ)
    xs ++ xs

  share-list-elems : Free F ℕ
  share-list-elems = do
    xs ← share (coin ∷ᴹ []ᴹ)
    _+_ <$> head xs ⊛ head xs

  shared-list-elem : Free F ℕ
  shared-list-elem = do
    x ← share coin
    sum (x ∷ᴹ x ∷ᴹ []ᴹ)

coin*2-test : 2 ∷ 0 ∷ [] ≡ runCTC coin*2
coin*2-test = refl

nested-sharing-test : 4 ∷ 0 ∷ [] ≡ runCTC nested-sharing
nested-sharing-test = refl

add-shared-coin-clash-test : 3 ∷ 2 ∷ 1 ∷ 0 ∷ [] ≡ runCTC add-shared-coin-clash
add-shared-coin-clash-test = refl

share-list-test : (1 ∷ 1 ∷ []) ∷ (0 ∷ 0 ∷ []) ∷ [] ≡ runCTC share-list
share-list-test = refl

share-list-elems-test : 2 ∷ 0 ∷ [] ≡ runCTC share-list-elems
share-list-elems-test = refl

shared-list-elem-test : 2 ∷ 0 ∷ [] ≡ runCTC shared-list-elem
shared-list-elem-test = refl

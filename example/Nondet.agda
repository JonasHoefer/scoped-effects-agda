{-# OPTIONS --overlapping-instances #-}

module Nondet where

open import Function                              using (_$_)
open import Size                                  using (Size; ↑_)

open import Data.List                             using (List; _∷_; [])
open import Data.Nat                              using (ℕ; _+_)
open import Data.Product                          using (_×_; _,_)

open import Container                             using (Container)
open import Free
open import Injectable                            using (_⊂_)

open import Effect.Nondet                         using (Nondet; solutions; select; _⁇_)
open import Effect.State                          using (State; evalState)
open import Effect.Share                          using (Share; share; bshare)
open import Effect.Void                           using (run)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

sumTwo : {F : Container} → ⦃ Nondet ⊂ F ⦄ → List ℕ → Free F ℕ
sumTwo xs = do
    x ← select xs
    y ← select xs
    pure (x + y)
  where open RawMonad freeMonad hiding (pure)

testNonDet : List ℕ
testNonDet = run (solutions (sumTwo (3 ∷ 4 ∷ 7 ∷ [])))

coin : {F : Container} → ⦃ Nondet ⊂ F ⦄ → Free F ℕ
coin = pure 0 ⁇ pure 1

addM : ∀ {F : Container} → Free F ℕ → Free F ℕ → Free F ℕ
addM x y = (_+_) <$> x ⊛ y
  where open RawMonad freeMonad

exAddSharedCoinTwice : {F : Container} → ⦃ Nondet ⊂ F ⦄ → Free F ℕ
exAddSharedCoinTwice {F} = let fx = coin in addM (addM fx coin) (addM fx coin) -- does not share!
  where open RawMonad (freeMonad {F})

-- | Tests | --

-- | Shares the result of a non deterministic computation.
coin*2 : {F : Container} → ⦃ State ℕ ⊂ F ⦄ → ⦃ Share ⊂ F ⦄ → ⦃ Nondet ⊂ F ⦄ → Free F ℕ
coin*2 = do x ← share coin ; addM x x
  where open RawMonad freeMonad

coin*2-test : 2 ∷ 0 ∷ [] ≡ (run $ solutions $ bshare $ evalState 0 coin*2)
coin*2-test = refl

-- | Shares results of computations using shared arguments.
nested-sharing : {F : Container} → ⦃ State ℕ ⊂ F ⦄ → ⦃ Share ⊂ F ⦄ → ⦃ Nondet ⊂ F ⦄ → Free F ℕ
nested-sharing = share (share coin >>= λ fx → addM fx fx) >>= λ fy → addM fy fy
  where open RawMonad freeMonad

nested-sharing-test : 4 ∷ 0 ∷ [] ≡ (run $ solutions $ bshare $ evalState 0 nested-sharing)
nested-sharing-test = refl

-- | Deep Sharing (TODO)
data Listᴹ (F : Container) (A : Set) : {Size} → Set where
  nil : {i : Size} → Listᴹ F A {i}
  cons : {i : Size} → Free F A → Free F (Listᴹ F A {i}) → Listᴹ F A {↑ i}

infixr 5 _∷ᴹ_
pattern []ᴹ       = pure nil
pattern _∷ᴹ_ x xs = pure (cons x xs)

sum : {i : Size} → {F : Container} → ⦃ State ℕ ⊂ F ⦄ → ⦃ Share ⊂ F ⦄ → ⦃ Nondet ⊂ F ⦄ → Free F (Listᴹ F ℕ {i}) → Free F ℕ
sum xs = xs >>= λ where
    nil          → return 0
    (cons x mxs) → _+_ <$> x ⊛ sum mxs
  where open RawMonad freeMonad

share-list-elems : {F : Container} → ⦃ State ℕ ⊂ F ⦄ → ⦃ Share ⊂ F ⦄ → ⦃ Nondet ⊂ F ⦄ → Free F ℕ
share-list-elems = do x ← share coin ; sum (x ∷ᴹ x ∷ᴹ []ᴹ)
  where open RawMonad freeMonad

share-list-elems-test : 2 ∷ 0 ∷ [] ≡ (run $ solutions $ bshare $ evalState 0 share-list-elems)
share-list-elems-test = refl

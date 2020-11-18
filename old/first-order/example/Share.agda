{-# OPTIONS --overlapping-instances #-}

module Share where

open import Function                              using (_$_)
open import Size                                  using (Size; ↑_)

open import Category.Monad                        using (RawMonad)
open        RawMonad ⦃...⦄                        using (_>>=_; _>>_; return; _<$>_) renaming (_⊛_ to _<*>_)


open import Data.List                             using (List; _∷_; [])
open import Data.MList                            using (Listᴹ; _∷ᴹ_; []ᴹ; _++_; head; sum)
open import Data.Nat                              using (ℕ; _+_)
open import Data.Product                          using (_×_; _,_)

open import Container                             using (Container)
open import Free
open import Free.Instances

open import Effect.Nondet                         using (Nondet; solutions; select; _⁇_)
open import Effect.State                          using (State; evalState)
open import Effect.Share                          using (Share; share; runCTC; nf)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Test for the sharing effect, i.e. simulation of Curry's call-time choice semantics.

private
  variable
    F : List Container
    A B : Set

coin : {@(tactic eff) _ : Nondet ∈ F} → Free F ℕ
coin = pure 0 ⁇ pure 1

addM : Free F ℕ → Free F ℕ → Free F ℕ
addM x y = ⦇ x + y ⦈

-- | Shares the result of a non deterministic computation.
coin*2 : {@(tactic eff) _ : State (ℕ × ℕ) ∈ F} {@(tactic eff) _ : Share ∈ F} {@(tactic eff) _ : Nondet ∈ F} → Free F ℕ
coin*2 = do
  x ← share coin
  addM x x

-- | Shares results of computations using shared arguments.
nested-sharing :
  {@(tactic eff) _ : State (ℕ × ℕ) ∈ F}
  {@(tactic eff) _ : Share         ∈ F}
  {@(tactic eff) _ : Nondet        ∈ F}
  → Free F ℕ
nested-sharing = share (share coin >>= λ fx → addM fx fx) >>= λ fy → addM fy fy

add-shared-coin-clash :
  {@(tactic eff) _ : State (ℕ × ℕ) ∈ F}
  {@(tactic eff) _ : Share         ∈ F}
  {@(tactic eff) _ : Nondet        ∈ F}
  → Free F ℕ
add-shared-coin-clash = share (share coin >>= λ fx → addM fx fx) >>= λ fy → share coin >>= λ fz → addM fy fz

share-list :
  {@(tactic eff) _ : State (ℕ × ℕ) ∈ F}
  {@(tactic eff) _ : Share         ∈ F}
  {@(tactic eff) _ : Nondet        ∈ F}
  → Free F (Listᴹ F ℕ)
share-list = do
  xs ← share (coin ∷ᴹ []ᴹ)
  xs ++ xs

share-list-elems :
  {@(tactic eff) _ : State (ℕ × ℕ) ∈ F}
  {@(tactic eff) _ : Share         ∈ F}
  {@(tactic eff) _ : Nondet        ∈ F}
  → Free F ℕ
share-list-elems = do
  xs ← share (coin ∷ᴹ []ᴹ)
  ⦇ head xs + head xs ⦈

shared-list-elem :
  {@(tactic eff) _ : State (ℕ × ℕ) ∈ F}
  {@(tactic eff) _ : Share         ∈ F}
  {@(tactic eff) _ : Nondet        ∈ F}
  → Free F ℕ
shared-list-elem = do
  x ← share coin
  sum (x ∷ᴹ x ∷ᴹ []ᴹ)

coin*2-test : 0 ∷ 2 ∷ [] ≡ runCTC coin*2
coin*2-test = refl

nested-sharing-test : 0 ∷ 4 ∷ [] ≡ runCTC nested-sharing
nested-sharing-test = refl

add-shared-coin-clash-test : 0 ∷ 1 ∷ 2 ∷ 3 ∷ [] ≡ runCTC add-shared-coin-clash
add-shared-coin-clash-test = refl

share-list-test : (0 ∷ 0 ∷ []) ∷ (1 ∷ 1 ∷ []) ∷ [] ≡ runCTC share-list
share-list-test = refl

share-list-elems-test : 0 ∷ 2 ∷ [] ≡ runCTC share-list-elems
share-list-elems-test = refl

shared-list-elem-test : 0 ∷ 2 ∷ [] ≡ runCTC shared-list-elem
shared-list-elem-test = refl

addSharedCoinTwice :
  {@(tactic eff) _ : State (ℕ × ℕ) ∈ F}
  {@(tactic eff) _ : Share         ∈ F}
  {@(tactic eff) _ : Nondet        ∈ F}
  → Free F ℕ
addSharedCoinTwice = do
  x ← share coin
  ⦇ ⦇ x + coin ⦈ + ⦇ x + coin ⦈ ⦈

runAddShareCoinTwice : runCTC addSharedCoinTwice ≡ (0 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ [])
runAddShareCoinTwice = refl

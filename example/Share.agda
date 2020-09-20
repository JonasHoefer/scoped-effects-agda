
{-# OPTIONS --overlapping-instances #-}
module Share where

open import Size     using (↑_)
open import Function using (_$_; flip)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.MList
open import Data.Nat using (ℕ; _+_; _≤?_)
open import Data.Normalform

open import Variables
open import Effect
open import Effect.Nondet
open import Effect.Share
open import Effect.Share.Shareable
open import Effect.State
open import Prog
open import Prog.Instances

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary.Decidable            using (⌊_⌋)


coin : ⦃ Nondet ∈ effs ⦄ → Prog effs ℕ
coin = pure 0 ⁇ pure 1

doubleUnSharedCoin : ⦃ Nondet ∈ effs ⦄ → Prog effs ℕ
doubleUnSharedCoin = do
  let c = coin
  ⦇ c + c ⦈

testDoubleUnSharedCoin : (run $ runNondet $ runShare $ evalState {S = SID} doubleUnSharedCoin (0 , 0)) ≡ 0 ∷ 1 ∷ 1 ∷ 2 ∷ []
testDoubleUnSharedCoin = refl

doubleSharedCoin : ⦃ Nondet ∈ effs ⦄ → ⦃ State SID ∈ effs ⦄ → ⦃ Share ∈ effs ⦄ → Prog effs ℕ
doubleSharedCoin = do
  c ← share coin
  ⦇ c + c ⦈

testDoubleSharedCoin : (run $ runNondet $ runShare $ evalState doubleSharedCoin (0 , 0)) ≡ 0 ∷ 2 ∷ []
testDoubleSharedCoin = refl

insertND : ⦃ Nondet ∈ effs ⦄ → Prog effs A → Prog effs (Listᴹ effs A {i}) → Prog effs (Listᴹ effs A {↑ i})
insertND mx mys = mys >>= λ where
  nilᴹ           → mx ∷ᴹ []ᴹ
  (consᴹ my mys) → mx ∷ᴹ my ∷ᴹ mys ⁇ my ∷ᴹ insertND mx mys

testInsertND : runCurry (insertND (var 1) (var 2 ∷ᴹ var 3 ∷ᴹ []ᴹ)) ≡ (1 ∷ 2 ∷ 3 ∷ []) ∷ (2 ∷ 1 ∷ 3 ∷ []) ∷ (2 ∷ 3 ∷ 1 ∷ []) ∷ []
testInsertND = refl

permutations : ⦃ Nondet ∈ effs ⦄ → Prog effs (Listᴹ effs A {i}) → Prog effs (Listᴹ effs A {i})
permutations = _>>= λ where
  nilᴹ           → []ᴹ
  (consᴹ mx mxs) → insertND mx (permutations mxs)

isSorted : Prog effs (Listᴹ effs ℕ {i}) → Prog effs Bool
isSorted = _>>= λ where
  nilᴹ           → var true
  (consᴹ mx mxs) → mxs >>= λ where
    nilᴹ           → var true
    (consᴹ my mys) → do
      x ← mx
      y ← my
      if ⌊ x ≤? y ⌋ then isSorted mxs else var false

sort : ⦃ Nondet ∈ effs ⦄ → ⦃ State SID ∈ effs ⦄ → ⦃ Share ∈ effs ⦄ →
  Prog effs (Listᴹ effs ℕ) → Prog effs (Listᴹ effs ℕ)
sort mxs = do
    xs ← share (permutations mxs)
    b  ← isSorted xs
    if b then xs else fail

testSort : (runCurry $ sort (var 3 ∷ᴹ var 1 ∷ᴹ var 4 ∷ᴹ var 2 ∷ᴹ []ᴹ)) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ∷ []
testSort = refl

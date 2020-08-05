{-# OPTIONS --overlapping-instances #-}

module Permutationsort where

open import Level                                 using (0ℓ)
open import Size                                  using (Size; ↑_)
open import Function                              using (_$_)

open import Data.Bool                             using (Bool; true; false; if_then_else_)
open import Data.Nat                              using (ℕ; _≤?_)
open import Data.List                             using (List; _∷_; [])
open import Data.MList                            using (Listᴹ; _∷ᴹ_; []ᴹ; cons; nil; _++_)
open import Data.Product                          using (_×_; _,_)

open import Relation.Nullary.Decidable using (⌊_⌋)

open import Container                             using (Container)
open import Free
open import Injectable                            using (_⊂_)

open import Effect.Nondet                         using (Nondet; solutions; select; _⁇_; fail)
open import Effect.State                          using (State; evalState)
open import Effect.Share                          using (Share; share; bshare; nf)
open import Effect.Void                           using (run)

insert : ∀ {F i} → ⦃ Share ⊂ F ⦄ → ⦃ State ℕ ⊂ F ⦄ → ⦃ Nondet ⊂ F ⦄ → Free F ℕ → Free F (Listᴹ F ℕ {i}) → Free F (Listᴹ F ℕ {↑ i})
insert mx mxs = (mx ∷ᴹ mxs) ⁇ mxs >>= λ where
    nil           → fail
    (cons my mys) → my ∷ᴹ insert mx mys
  where open RawMonad freeMonad

perm : ∀ {F i} → ⦃ Share ⊂ F ⦄ → ⦃ State ℕ ⊂ F ⦄ → ⦃ Nondet ⊂ F ⦄ → Free F (Listᴹ F ℕ {i}) → Free F (Listᴹ F ℕ {i})
perm = _>>= λ where
    nil → []ᴹ
    (cons mx mxs) → insert mx $ perm mxs
  where open RawMonad freeMonad

isSorted : ∀ {F i} → Free F (Listᴹ F ℕ {i}) → Free F Bool
isSorted {ord} = _>>= λ where
    nil           → return true
    (cons mx mxs) → mxs >>= λ where
      nil           → return true
      (cons my mys) → do
        x ← mx
        y ← my
        if ⌊ x ≤? y ⌋ then isSorted mxs else return false
  where open RawMonad freeMonad

mxs : ∀ {F} → ⦃ Share ⊂ F ⦄ → ⦃ State ℕ ⊂ F ⦄ → ⦃ Nondet ⊂ F ⦄ → Free F (Listᴹ F ℕ)
mxs = return 4 ∷ᴹ return 1 ∷ᴹ return 3 ∷ᴹ return 2 ∷ᴹ []ᴹ
  where open RawMonad freeMonad

sort : ∀ {F} → ⦃ Nondet ⊂ F ⦄ → ⦃ Share ⊂ F ⦄ → ⦃ State ℕ ⊂ F ⦄ → Free F (Listᴹ F ℕ)
sort = do
    pxs ← share (perm mxs)
    b ← isSorted pxs
    if b then pxs else fail
  where open RawMonad freeMonad

foo : List (List ℕ)
foo = run $ solutions $ bshare $ evalState 0 $ nf $ sort

share-perm : ∀ {F} → ⦃ Nondet ⊂ F ⦄ → ⦃ Share ⊂ F ⦄ → ⦃ State ℕ ⊂ F ⦄ → Free F (Listᴹ F ℕ)
share-perm = do
    xs ← share (perm (return 0 ∷ᴹ return 1 ∷ᴹ return 2 ∷ᴹ []ᴹ))
    xs ++ xs
  where open RawMonad freeMonad

bar : List (List ℕ)
bar = run $ solutions $ bshare $ evalState 0 $ nf $ share-perm

{-# OPTIONS --overlapping-instances #-}

module Data.MList where

open import Size           using (Size; ↑_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ using (_>>=_; _>>_; return; _<$>_) renaming (_⊛_ to _<*>_)

open import Data.List      using (List; _∷_; [])
open import Data.Nat       using (ℕ; _+_)
open import Data.Product   using (_×_; _,_)

open import Container      using (Container)
open import Free
open import Free.Instances

open import Effect.Nondet  using (Nondet; fail)
open import Effect.Share   using (Share; share; Normalform; nf; Shareable)
open import Effect.State   using (State)

data Listᴹ (C : List Container) (A : Set) : {Size} → Set where
  nil  : ∀ {i} → Listᴹ C A {i}
  cons : ∀ {i} → Free C A → Free C (Listᴹ C A {i}) → Listᴹ C A {↑ i}

infixr 5 _∷ᴹ_ _++_
pattern []ᴹ         = pure nil
pattern _∷ᴹ_ mx mxs = pure (cons mx mxs)

private
  variable
    F : List Container
    A B : Set

head : {@(tactic eff) _ : Nondet ∈ F} → Free F (Listᴹ F A) → Free F A
head = _>>= λ where
   nil         → fail
   (cons mx _) → mx

_++_ : ∀ {i} → Free F (Listᴹ F A {i}) → Free F (Listᴹ F A) → Free F (Listᴹ F A)
mxs ++ mys = mxs >>= λ where
    nil           → mys
    (cons mx mxs) → mx ∷ᴹ mxs ++ mys

sum : ∀ {i} → Free F (Listᴹ F ℕ {i}) → Free F ℕ
sum xs = xs >>= λ where
    nil          → return 0
    (cons x mxs) → ⦇ x + sum mxs ⦈

instance
  Listᴹ-normalform : ∀ {i} → ⦃ Normalform F A B ⦄ → Normalform F (Listᴹ F A {i}) (List B)
  Normalform.nf Listᴹ-normalform nil           = pure []
  Normalform.nf Listᴹ-normalform (cons mx mxs) = ⦇ (mx >>= nf) ∷ (mxs >>= nf) ⦈

  Listᴹ-shareable : ∀ {i} → ⦃ Shareable F A ⦄ → {@(tactic eff) _ : Share ∈ F} → {@(tactic eff) _ : State (ℕ × ℕ) ∈ F}
    → Shareable F (Listᴹ F A {i})
  Shareable.shareArgs Listᴹ-shareable nil           = []ᴹ
  Shareable.shareArgs Listᴹ-shareable (cons mx mxs) = cons <$> share mx <*> share mxs

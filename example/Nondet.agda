{-# OPTIONS --overlapping-instances #-}

module Nondet where

open import Data.List     using (List; _∷_; [])
open import Data.Nat      using (ℕ; _+_)

open import Container     using (Container)
open import Free
open import Injectable    using (_⊂_)

open import Effect.Nondet using (nondet; solutions; select)
open import Effect.Void   using (run)

sumTwo : {F : Container} → ⦃ nondet ⊂ F ⦄ → List ℕ → Free F ℕ
sumTwo xs = do
    x ← select xs
    y ← select xs
    pure (x + y)
  where open RawMonad freeMonad hiding (pure)

testNonDet : List ℕ
testNonDet = run (solutions (sumTwo (3 ∷ 4 ∷ 7 ∷ [])))

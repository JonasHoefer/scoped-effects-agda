{-# OPTIONS --overlapping-instances #-}

module NonDet where

open import Data.List     using (List; _∷_; [])
open import Data.Nat      using (ℕ; _+_)

open import Container     using (Container)
open import Free          using (Free; pure; _>>=_)
open import Injectable    using (_⊂_)

open import Effect.NonDet using (nondet; solutions; select)
open import Effect.Void   using (run)

sumTwo : {F : Container} → ⦃ nondet ⊂ F ⦄ → List ℕ → Free F ℕ
sumTwo xs = do
  x ← select xs
  y ← select xs
  pure (x + y)

testNonDet : List ℕ
testNonDet = run (solutions (sumTwo (3 ∷ 4 ∷ 7 ∷ [])))

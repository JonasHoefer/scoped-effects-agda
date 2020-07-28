{-# OPTIONS --overlapping-instances #-}

module Parser where

open import Function      using (_$_)
open import Size          using (Size; ↑_)

open import Data.Char     using (Char)
open import Data.List     using (List; _∷_; [])
open import Data.Nat      using (ℕ; _+_; _*_)
open import Data.String   using (toList)

open import Container     using (Container)
open import Free          using (Free; pure; _>>=_; _>>_)
open import Injectable    using (_⊂_)

open import Effect.Cut    using (call; cuts)
open import Effect.Nondet using (nondet; solutions; select; _⁇_)
open import Effect.Void   using (run)
open import Effect.Symbol using (parse; symbol; symbolᴾ; numberᴾ)

{-# TERMINATING #-}
expr   : {F : Container} → ⦃ nondet ⊂ F ⦄ → ⦃ symbol ⊂ F ⦄ → Free F ℕ
term   : {F : Container} → ⦃ nondet ⊂ F ⦄ → ⦃ symbol ⊂ F ⦄ → Free F ℕ
factor : {F : Container} → ⦃ nondet ⊂ F ⦄ → ⦃ symbol ⊂ F ⦄ → Free F ℕ

expr   = (do i ← term ; symbolᴾ '+' ; j ← expr ; pure (i + j)) ⁇ term
term   = (do i ← factor ; symbolᴾ '*' ; j ← term ; pure (i * j)) ⁇ factor
factor = numberᴾ ⁇ (do symbolᴾ '(' ; i ← expr ; symbolᴾ ')' ; pure i)

exprᶜ : {F : Container} → ⦃ nondet ⊂ F ⦄ → ⦃ symbol ⊂ F ⦄ → Free F ℕ
exprᶜ = do
  i ← term
  call ((do symbolᴾ '+' ; cuts ; j ← expr ; pure (i + j)) ⁇ pure i)

parse+* : List ℕ
parse+* = run $ solutions $ parse (toList "1+2*3") expr

parse-digit : List ℕ
parse-digit = run $ solutions $ parse (toList "1") exprᶜ

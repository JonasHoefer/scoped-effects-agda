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

open import Effect.Call   using (call; call′; runCut)
open import Effect.Cut    using (cut; cuts)                      renaming (call to callᶜ)
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
  callᶜ ((do symbolᴾ '+' ; cuts ; j ← expr ; pure (i + j)) ⁇ pure i)

parse+* : List ℕ
parse+* = run $ solutions $ parse (toList "1+2*3") expr

parse-digit-wrong : List ℕ
parse-digit-wrong = run $ solutions $ parse (toList "1") exprᶜ

{-# TERMINATING #-}
exprˢ   : {F : Container} → ⦃ nondet ⊂ F ⦄ → ⦃ symbol ⊂ F ⦄ → ⦃ call ⊂ F ⦄ → ⦃ cut ⊂ F ⦄ → Free F ℕ
termˢ   : {F : Container} → ⦃ nondet ⊂ F ⦄ → ⦃ symbol ⊂ F ⦄ → ⦃ call ⊂ F ⦄ → ⦃ cut ⊂ F ⦄ → Free F ℕ
factorˢ : {F : Container} → ⦃ nondet ⊂ F ⦄ → ⦃ symbol ⊂ F ⦄ → ⦃ call ⊂ F ⦄ → ⦃ cut ⊂ F ⦄ → Free F ℕ

exprˢ = do
  i ← termˢ
  call′ ((do symbolᴾ '+' ; cuts ; j ← exprˢ ; pure (i + j)) ⁇ pure i)
termˢ   = (do i ← factorˢ ; symbolᴾ '*' ; j ← termˢ ; pure (i * j)) ⁇ factorˢ
factorˢ = numberᴾ ⁇ (do symbolᴾ '(' ; i ← exprˢ ; symbolᴾ ')' ; pure i)

parse-digit-correct : List ℕ
parse-digit-correct = run $ solutions $ runCut $ parse (toList "1") exprˢ

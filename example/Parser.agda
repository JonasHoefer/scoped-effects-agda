{-# OPTIONS --overlapping-instances #-}

module Parser where

open import Function                              using (_$_)
open import Size                                  using (Size; ↑_)

open import Data.Char                             using (Char)
open import Data.List                             using (List; _∷_; [])
open import Data.Nat                              using (ℕ; _+_; _*_)
open import Data.String                           using (toList)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Container                             using (Container)
open import Free
open import Injectable                            using (_⊂_)

open import Effect.Call                           using (Call; call; runCut)
open import Effect.Cut                            using (Cut; cut)                       renaming (call to callᶜ)
open import Effect.Nondet                         using (Nondet; solutions; select; _⁇_)
open import Effect.Void                           using (run)
open import Effect.Symbol                         using (Symbol; parse; symbolᴾ; numberᴾ)

module Unscoped {F : Container} ⦃ _ : Nondet ⊂ F ⦄ ⦃ _ : Symbol ⊂ F ⦄ where
  open RawMonad (freeMonad {F})

  {-# TERMINATING #-}
  expr   : Free F ℕ
  term   : Free F ℕ
  factor : Free F ℕ

  expr   = (do i ← term ; symbolᴾ '+' ; j ← expr ; return (i + j)) ⁇ term
  term   = (do i ← factor ; symbolᴾ '*' ; j ← term ; return (i * j)) ⁇ factor
  factor = numberᴾ ⁇ (do symbolᴾ '(' ; i ← expr ; symbolᴾ ')' ; return i)

parse+* : 15 ∷ [] ≡ (run $ solutions $ parse Unscoped.expr $ toList "1+4*3+2")
parse+* = refl

module UnscopedError where
  {-# TERMINATING #-}
  exprᶜ : {F : Container} → ⦃ Nondet ⊂ F ⦄ → ⦃ Symbol ⊂ F ⦄ → Free F ℕ
  helper : {G : Container} → ⦃ Nondet ⊂ G ⦄ → ⦃ Symbol ⊂ G ⦄ → ℕ → Free G ℕ

  exprᶜ = do i ← Unscoped.term ; helper i
    where open RawMonad freeMonad

  helper i = callᶜ ((do symbolᴾ '+' ; cut ; j ← exprᶜ ; return (i + j)) ⁇ return i)
    where open RawMonad freeMonad

parse-digit-wrong : [] ≡ (run $ solutions $ parse UnscopedError.exprᶜ $ toList "1")
parse-digit-wrong = refl

module Scoped {F : Container} ⦃ _ : Nondet ⊂ F ⦄ ⦃ _ : Symbol ⊂ F ⦄ ⦃ _ : Call ⊂ F ⦄ ⦃ _ : Cut ⊂ F ⦄ where
  open RawMonad (freeMonad {F})

  {-# TERMINATING #-}
  exprˢ   : Free F ℕ
  termˢ   : Free F ℕ
  factorˢ : Free F ℕ

  exprˢ = do
    i ← termˢ
    call ((do symbolᴾ '+' ; cut ; j ← exprˢ ; return (i + j)) ⁇ return i)
  termˢ   = (do i ← factorˢ ; symbolᴾ '*' ; j ← termˢ ; return (i * j)) ⁇ factorˢ
  factorˢ = numberᴾ ⁇ (do symbolᴾ '(' ; i ← exprˢ ; symbolᴾ ')' ; return i)

parse-digit-correct : 1 ∷ [] ≡ (run $ solutions $ runCut $ parse Scoped.exprˢ $ toList "1")
parse-digit-correct = refl

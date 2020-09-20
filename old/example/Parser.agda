module Parser where

open import Function                              using (_$_)
open import Size                                  using (Size; ↑_)

open import Category.Monad                        using (RawMonad)
open        RawMonad ⦃...⦄                        using (_>>=_; _>>_; return)

open import Data.Char                             using (Char)
open import Data.List                             using (List; _∷_; [])
open import Data.Nat                              using (ℕ; _+_; _*_)
open import Data.String                           using (toList)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Container                             using (Container)
open import Free
open import Free.Instances

open import Effect.Call                           using (Call; call; runCut)
open import Effect.Cut                            using (Cut; cut)                       renaming (call to callᶜ)
open import Effect.Nondet                         using (Nondet; solutions; select; _⁇_)
open import Effect.Symbol                         using (Symbol; parse; symbolᴾ; numberᴾ)

open import Tactic.Assumption

private
  variable
    F : List Container

module Unscoped where
  {-# TERMINATING #-}
  expr   : {@(tactic eff) _ : Nondet ∈ F} {@(tactic eff) _ : Symbol ∈ F} → Free F ℕ
  term   : {@(tactic eff) _ : Nondet ∈ F} {@(tactic eff) _ : Symbol ∈ F} → Free F ℕ
  factor : {@(tactic eff) _ : Nondet ∈ F} {@(tactic eff) _ : Symbol ∈ F} → Free F ℕ

  expr   = (do i ← term ; symbolᴾ '+' ; j ← expr ; return (i + j)) ⁇ term
  term   = (do i ← factor ; symbolᴾ '*' ; j ← term ; return (i * j)) ⁇ factor
  factor = numberᴾ ⁇ (do symbolᴾ '(' ; i ← expr ; symbolᴾ ')' ; return i)

  parse+* : 15 ∷ [] ≡ (run $ solutions $ parse expr $ toList "1+4*3+2")
  parse+* = refl

-- module UnscopedError where
--   {-# TERMINATING #-}
--   exprᶜ  : {@(tactic eff) _ : Nondet ∈ F} {@(tactic eff) _ : Symbol ∈ F} → Free F ℕ
--   helper : {@(tactic eff) _ : Nondet ∈ F} {@(tactic eff) _ : Symbol ∈ F} → ℕ → Free F ℕ
-- 
--   exprᶜ = do i ← Unscoped.term ; helper i
-- 
--   helper i = callᶜ ((do symbolᴾ '+' ; cut ; j ← exprᶜ ; return (i + j)) ⁇ return i)
-- 
--   parse-digit-wrong : [] ≡ (run $ solutions $ parse exprᶜ $ toList "1")
--   parse-digit-wrong = refl

module Scoped where
  {-# TERMINATING #-}
  factorˢ termˢ exprˢ :
    {@(tactic eff) _ : Nondet ∈ F}
    {@(tactic eff) _ : Symbol ∈ F}
    {@(tactic eff) _ : Call   ∈ F}
    {@(tactic eff) _ : Cut    ∈ F}
    → Free F ℕ

  exprˢ = do
    i ← termˢ
    call ((do symbolᴾ '+' ; cut ; j ← exprˢ ; return (i + j)) ⁇ return i)
  termˢ   = (do i ← factorˢ ; symbolᴾ '*' ; j ← termˢ ; return (i * j)) ⁇ factorˢ
  factorˢ = numberᴾ ⁇ (do symbolᴾ '(' ; i ← exprˢ ; symbolᴾ ')' ; return i)

  parse-digit-correct : 1 ∷ [] ≡ (run $ solutions $ runCut $ parse exprˢ $ toList "1")
  parse-digit-correct = refl

module Tactic.Assumption where

open import Reflection                              hiding (_>>=_; _>>_)
open import Reflection.Argument                     using (vArg; _⟨∷⟩_; _⟅∷⟆_)
open import Reflection.TypeChecking.Monad.Instances

open import Category.Monad                          using (RawMonad; RawMonadPlus)
open RawMonad ⦃...⦄
open RawMonadPlus ⦃...⦄                             using (_∣_; ∅)

open import Data.List                               using (List; []; _∷_; length; map; foldr)
open import Data.Nat                                using (ℕ; suc)
open import Data.Unit                               using (⊤)
open import Data.List.Relation.Unary.Any            using (Any; here; there)

-- | The first n variables in the current context (i.e. variables with DeBruijn indices 0 ... n-1).
vars : ℕ → List Term
vars 0       = []
vars (suc n) = var n [] ∷ vars n

choice : {A : Set} → List (TC A) → TC A
choice = foldr (_∣_) ∅

-- | Tries to infer a varaible from the current context.
tac-assumption : Term → TC ⊤
tac-assumption ?hole = do
  cxt ← getContext
  choice (map (unify ?hole) (vars (length cxt)))

macro assumption = tac-assumption

tac-there-assumption : Term → TC ⊤
tac-there-assumption ?hole = do
  ?hole2 ← newMeta unknown
  unify ?hole (con (quote Any.there) (?hole2 ⟨∷⟩ []))
  tac-assumption ?hole2

macro there-assumption = tac-there-assumption

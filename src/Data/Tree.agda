module Data.Tree where

open import Data.List                               using (List; _∷_; []; _++_)
open import Data.Maybe                              using (Maybe; just; nothing)
open import Data.Nat                                using (ℕ)
open import Data.Nat.Properties                     using (<-strictTotalOrder)
open import Data.Product                            using (_×_)
open import Data.Product.Relation.Binary.Lex.Strict using (×-strictTotalOrder)

order = ×-strictTotalOrder (×-strictTotalOrder <-strictTotalOrder <-strictTotalOrder) <-strictTotalOrder
open import Data.AVL.Map order public               using (Map; empty; insert; lookup)

data Tree (A : Set) : Set where
  leaf   : A → Tree A
  failed : Tree A
  choice : Maybe ((ℕ × ℕ) × ℕ) → Tree A → Tree A → Tree A

data Decision : Set where
  L : Decision
  R : Decision

Memo = Map Decision

dfs : {A : Set} → Memo → Tree A → List A
dfs mem (leaf x)                = x ∷ []
dfs mem failed                  = []
dfs mem (choice nothing  t₁ t₂) = dfs mem t₁ ++ dfs mem t₂
dfs mem (choice (just n) t₁ t₂) with lookup n mem
... | just L  = dfs mem t₁
... | just R  = dfs mem t₂
... | nothing = dfs (insert n L mem) t₁ ++ dfs (insert n R mem) t₂

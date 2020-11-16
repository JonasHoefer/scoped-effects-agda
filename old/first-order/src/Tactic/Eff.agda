module Tactic.Eff where

open import Reflection                              hiding (_>>=_; _>>_)
open import Reflection.TypeChecking.Monad.Instances
open import Category.Monad                          using (RawMonadPlus)
open RawMonadPlus ⦃...⦄                             using (_∣_)

open import Data.Unit                               using (⊤)

open import Tactic.Assumption                       using (tac-assumption; tac-there-assumption) public
open import Tactic.FindIndex                        using (tac-find-index; _∈_; here; there)     public

eff : Term → TC ⊤
eff t = tac-assumption t ∣ tac-find-index t ∣ tac-there-assumption t

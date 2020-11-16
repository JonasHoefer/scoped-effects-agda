{-# OPTIONS --overlapping-instances #-}

module Effect.Cut where

open import Size           using (Size; ↑_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ using (_>>=_; _>>_; return)

open import Data.Bool      using (true; false)
open import Data.List      using (List; _∷_; [])
open import Data.Unit      using (⊤; tt)
open import Data.Empty     using (⊥)
open import Data.Maybe     using (Maybe; nothing; just)
open import Data.Product   using (_,_)
open import Data.Sum       using (inj₁; inj₂)

open import Container      using (Container; _▷_; _⊕_)
open import Free
open import Free.Instances

open import Effect.Nondet  using (Nondet; fail; _⁇_; choiceˢ; failˢ)
open import Tactic.Assumption
open import Tactic.FindIndex

data Shape : Set where
  cutfailˢ : Shape

Cut : Container
Cut = Shape ▷ λ _ → ⊥

pattern Cutfail pf = impure (inj₁ cutfailˢ , pf)

private
  variable
    F : List Container
    A : Set

  go : ∀ {i} {@(tactic eff) _ : Nondet ∈ F} → Free (Cut ∷ F) A {i} → Free F A → Free F A
  go (pure x)      q = pure x ⁇ q
  go (Cutfail κ)   q = fail
  go f@(Other s κ) q with prj {Nondet} {p = there assumption} f
  ... | just (failˢ     , κ′) = q
  ... | just (choiceˢ _ , κ′) = go (κ′ true) (go (κ′ false) q)
  ... | nothing               = impure (s , λ p → go (κ p) q)

call : ∀ {i} {@(tactic eff) _ : Nondet ∈ F} → Free (Cut ∷ F) A {i} → Free F A
call p = go p fail

cutfail : {@(tactic eff) _ : Cut ∈ F} → Free F A
cutfail = op (cutfailˢ , λ())

cut : {@(tactic eff) _ : Cut ∈ F} → {@(tactic eff) _ : Nondet ∈ F} → Free F ⊤
cut = pure tt ⁇ cutfail

once : {@(tactic eff) _ : Nondet ∈ F} → Free (Cut ∷ F) A → Free F A
-- We just habe a proof that Nondet ∈ F not Nondet ∈ Cut ∷ F.
once p = call (do x ← p ; cut ; pure x)

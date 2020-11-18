module Effect.Nondet where

open import Function       using (_∘_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ using (_<$>_) renaming (_⊛_ to _<*>_)

open import Data.Bool      using (Bool; true; false)
open import Data.Empty     using (⊥)
open import Data.List      using (List; []; _∷_; _++_)
open import Data.Nat       using (ℕ)
open import Data.Maybe     using (Maybe; just; nothing)
open import Data.Product   using (_×_; _,_)
open import Data.Sum       using (inj₁; inj₂)
open import Data.Tree

open import Container      using (Container; _▷_; _⊕_)
open import Free
open import Free.Instances

--------------------
-- Nondeterminism --
--------------------

data Shape : Set where
  failˢ   : Shape
  choiceˢ : Maybe ((ℕ × ℕ) × ℕ) → Shape

pattern Fail pf       = impure (inj₁ failˢ , pf)
pattern Choice mId pf = impure (inj₁ (choiceˢ mId) , pf)

-- non determinism effect
Nondet : Container
Nondet = Shape ▷ λ{ failˢ → ⊥ ; (choiceˢ x) → Bool }

private
  variable
    F : List Container
    A : Set

runNondet : Free (Nondet ∷ F) A → Free F (Tree A)
runNondet (pure x) = pure (leaf x)
runNondet (Fail pf) = pure failed
runNondet (Choice n pf) = choice n <$> runNondet (pf true) <*> runNondet (pf false)
runNondet (Other s pf) = impure (s , runNondet ∘ pf)

solutions : Free (Nondet ∷ F) A → Free F (List A)
solutions p = dfs empty <$> runNondet p

fail : {@(tactic eff) _ : Nondet ∈ F} → Free F A
fail = op (failˢ , λ())

-- smart constructor for the choice operator
infixr 0 _⁇_
_⁇_ : {@(tactic eff) _ : Nondet ∈ F} → Free F A → Free F A → Free F A
p ⁇ q = op (choiceˢ nothing , λ{ true → p ; false → q})

select : {@(tactic eff) _ : Nondet ∈ F} → List A → Free F A
select []       = fail
select (x ∷ xs) = pure x ⁇ select xs

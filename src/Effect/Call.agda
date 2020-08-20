module Effect.Call where

open import Function       using (_∘_)
open import Size           using (Size; ↑_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ using (_>>=_; _>>_; return)

open import Data.Bool      using (true; false)
open import Data.Unit      using (⊤; tt)
open import Data.Empty     using (⊥)
open import Data.List      using (List; _∷_)
open import Data.Maybe     using (Maybe; nothing; just)
open import Data.Product   using (_,_)
open import Data.Sum       using (inj₁; inj₂)

open import Container      using (Container; _▷_; _⊕_)
open import Free
open import Free.Instances

open import Effect.Nondet  using (Nondet; fail; _⁇_; choiceˢ; failˢ)
open import Effect.Cut     using (Cut) renaming (call to callᶜ)

data Shape : Set where
  bcallˢ : Shape
  ecallˢ : Shape

Call : Container
Call = Shape ▷ λ _ → ⊤

pattern BCall pf = impure (inj₁ bcallˢ , pf)
pattern ECall pf = impure (inj₁ ecallˢ , pf)

private
  variable
    F : List Container
    A : Set

  begin : {@(tactic eff) _ : Call ∈ F} → Free F ⊤
  begin = op (bcallˢ , λ _ → pure tt)

  end : {@(tactic eff) _ : Call ∈ F} → Free F ⊤
  end = op (ecallˢ , λ _ → pure tt)

  ecall : ∀ {i} {@(tactic eff) _ : Nondet ∈ F} → Free (Call ∷ Cut ∷ F) A {i} → Free (Cut ∷ F) (Free (Call ∷ Cut ∷ F) A {i})
  ecall (pure x)     = pure (pure x)
  ecall (BCall pf)   = upcast (callᶜ (ecall (pf tt))) >>= ecall
  ecall (ECall pf)   = pure (pf tt)
  ecall (Other s pf) = impure (s , ecall ∘ pf)

  bcall : ∀ {i} {@(tactic eff) _ : Nondet ∈ F} → Free (Call ∷ Cut ∷ F) A {i} → Free (Cut ∷ F) A
  bcall (pure x)   = pure x
  bcall (BCall pf) = upcast (callᶜ (ecall (pf tt))) >>= bcall
  -- We have to work in a total context. To avoid handling wrong scopes we correct the error.
  bcall (ECall pf) = bcall (pf tt)
  bcall (impure (inj₂ s , pf)) = impure (s , bcall ∘ pf)

call : {@(tactic eff) _ : Call ∈ F} → Free F A → Free F A
call p = do begin ; x ← p ; end ; pure x

runCut : {@(tactic eff) _ : Nondet ∈ F} → Free (Call ∷ Cut ∷ F) A → Free F A
runCut p = callᶜ (bcall p)

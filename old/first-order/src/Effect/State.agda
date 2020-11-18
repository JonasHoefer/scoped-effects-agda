module Effect.State where

open import Function         using (_∘_)

open import Category.Functor using (RawFunctor)
open        RawFunctor ⦃...⦄

open import Data.List        using (List; []; _∷_)
open import Data.Product     using (_×_; _,_; proj₂)
open import Data.Sum         using (inj₁; inj₂)
open import Data.Unit        using (⊤; tt)

open import Container        using (Container; _▷_)
open import Free.Instances
open import Free

-----------
-- State --
-----------

data Shape (S : Set) : Set where
  putˢ : S → Shape S
  getˢ : Shape S

State : Set → Container
State S = Shape S ▷ λ { (putˢ _) → ⊤ ; getˢ → S }

pattern Get pf = impure (inj₁ getˢ , pf)
pattern Put s pf = impure (inj₁ (putˢ s) , pf)

private
  variable
    A S : Set
    ops : List Container

runState : S → Free (State S ∷ ops) A → Free ops (S × A)
runState s₀ (pure x)    = pure (s₀ , x)
runState s₀ (Put s₁ κ)  = runState s₁ (κ tt)
runState s₀ (Get κ)     = runState s₀ (κ s₀)
runState s₀ (Other s κ) = impure (s , runState s₀ ∘ κ)

evalState : S → Free (State S ∷ ops) A → Free ops A
evalState s₀ p = proj₂ <$> runState s₀ p

get : {@(tactic eff) _ : State S ∈ ops} → Free ops S
get = op (getˢ , pure)

put : {@(tactic eff) _ : State S ∈ ops} → S → Free ops ⊤
put s = op (putˢ s , pure)

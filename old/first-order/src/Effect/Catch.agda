module Effect.Catch where

open import Level          using (Level)
open import Function       using (_∘_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ using (_>>=_; _>>_; return)

open import Data.Bool      using (true; false)
open import Data.Unit      using (⊤; tt)
open import Data.Empty     using (⊥)
open import Data.List      using (List; _∷_; [])
open import Data.Maybe     using (Maybe; nothing; just)
open import Data.Product   using (_,_)
open import Data.Sum       using (_⊎_; inj₁; inj₂)

open import Container      using (Container; _▷_; _⊕_)
open import Free
open import Free.Instances
open import Effect.Exc     using (Exc; runExc)

-------------------------
-- Catch scoped effect --
-------------------------

-- The implementation follows Wu et al.

data Catchˢ : Set where
  bcatchˢ ecatchˢ : Catchˢ

Catch : Set → Container
Catch E = Catchˢ ▷ λ { bcatchˢ → ⊤ ⊎ E ; ecatchˢ → ⊤ }

pattern BCatch pf = impure (inj₁ bcatchˢ , pf)
pattern ECatch pf = impure (inj₁ ecatchˢ , pf)

private
  variable
    A E : Set
    ops : List Container

begin : {@(tactic eff) _ : Catch E ∈ ops} → Free ops A → (E → Free ops A) → Free ops A
begin p h = op (bcatchˢ , λ{(inj₁ tt) → p ; (inj₂ e) → h e})

end : {@(tactic eff) _ : Catch E ∈ ops} → Free ops ⊤
end = op (ecatchˢ , λ _ → pure tt)

infix 0 _catch_
_catch_ : {@(tactic eff) _ : Catch E ∈ ops} → Free ops A → (E → Free ops A) → Free ops A
_catch_ p = begin (do x ← p ; end ; return x)

bcatch : ∀ {i} → Free (Catch E ∷ Exc E ∷ ops) A {i} → Free (Exc E ∷ ops) A
ecatch : ∀ {i} → Free (Catch E ∷ Exc E ∷ ops) A {i} → Free (Exc E ∷ ops) (Free (Catch E ∷ Exc E ∷ ops) A {i})

bcatch (pure x)    = pure x
bcatch (BCatch κ)  = upcast (runExc (ecatch (κ (inj₁ tt)))) >>= λ where
  (inj₁ e) → bcatch (κ (inj₂ e))
  (inj₂ k) → bcatch k
bcatch (ECatch κ)  = bcatch (κ tt)
bcatch (Other s κ) = impure (s , bcatch ∘ κ)

ecatch (pure x)    = pure (pure x)
ecatch (BCatch κ)  = upcast (runExc (ecatch (κ (inj₁ tt)))) >>= λ where
  (inj₁ e) → ecatch (κ (inj₂ e))
  (inj₂ k) → ecatch k
ecatch (ECatch κ)  = pure (κ tt)
ecatch (Other s κ) = impure (s , ecatch ∘ κ)

runCatch : Free (Catch E ∷ Exc E ∷ ops) A → Free ops (E ⊎ A)
runCatch = runExc ∘ bcatch

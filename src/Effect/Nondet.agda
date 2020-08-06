module Effect.Nondet where

open import Function     using (_∘_)

open import Data.Bool    using (Bool; true; false)
open import Data.Empty   using (⊥)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.Nat     using (ℕ)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Tree

open import Container    using (Container; _▷_; _⊕_)
open import Free
open import Injectable   using (_⊂_; inject; project; Other)

data Shape : Set where
  failˢ   : Shape
  choiceˢ : Maybe ((ℕ × ℕ) × ℕ) → Shape

pos : Shape → Set
pos failˢ       = ⊥
pos (choiceˢ _) = Bool

pattern Fail pf       = impure (inj₁ failˢ , pf)
pattern Choice mId pf = impure (inj₁ (choiceˢ mId) , pf)

-- non determinism effect
Nondet : Container
Nondet = Shape ▷ pos

runNondet : {F : Container} {A : Set} → Free (Nondet ⊕ F) A → Free F (Tree A)
runNondet (pure x) = pure (leaf x)
runNondet (Fail pf) = pure failed
runNondet (Choice n pf) = choice n <$> runNondet (pf true) ⊛ runNondet (pf false)
  where open RawMonad freeMonad using (_<$>_; _⊛_)
runNondet (Other s pf) = impure (s , runNondet ∘ pf)

solutions : {F : Container} {A : Set} → Free (Nondet ⊕ F) A → Free F (List A)
solutions = map (dfs empty) ∘ runNondet

fail : {F : Container} {A : Set} → ⦃ Nondet ⊂ F ⦄ → Free F A
fail = inject (failˢ , λ())

infixr 0 _⁇_
_⁇_ : {F : Container} {A : Set} → ⦃ Nondet ⊂ F ⦄ → Free F A → Free F A → Free F A
p ⁇ q = inject (choiceˢ nothing , λ{ false → p ; true → q})

select : {F : Container} {A : Set} → ⦃ Nondet ⊂ F ⦄ → List A → Free F A
select []       = fail
select (x ∷ xs) = pure x ⁇ select xs

module Effect.Nondet where

open import Function     using (_∘_)

open import Data.Bool    using (Bool; true; false)
open import Data.Empty   using (⊥)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)

open import Container    using (Container; _▷_; _⊕_)
open import Free         using (Free; pure; impure; _<$>_; _<*>_)
open import Injectable   using (_⊂_; inject; project)

data Shape : Set where
  failˢ   : Shape
  choiceˢ : Shape

pos : Shape → Set
pos failˢ   = ⊥
pos choiceˢ = Bool

pattern Fail pf = impure (inj₁ failˢ , pf)
pattern Choice pf = impure (inj₁ choiceˢ , pf)

-- non determinism effect
nondet : Container
nondet = Shape ▷ pos

solutions : {F : Container} {A : Set} → Free (nondet ⊕ F) A → Free F (List A)
solutions (pure x)    = pure (x ∷ [])
solutions (Fail pf)   = pure []
solutions (Choice pf) = _++_ <$> solutions (pf true) <*> solutions (pf false)
solutions (impure (inj₂ s , pf)) = impure (s , solutions ∘ pf)

module _ {F : Container} {A : Set} ⦃ _ : nondet ⊂ F ⦄ where
  fail : Free F A
  fail = inject (failˢ , λ())

  _⁇_ : Free F A → Free F A → Free F A
  p ⁇ q = inject (choiceˢ , λ{ false → p ; true → q})

  select : List A → Free F A
  select []       = fail
  select (x ∷ xs) = pure x ⁇ select xs

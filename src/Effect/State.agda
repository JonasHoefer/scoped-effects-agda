module Effect.State where

open import Function     using (_∘_)

open import Data.Product using (_×_; _,_; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)

open import Container    using (Container; _▷_; _⊕_)
open import Free
open import Injectable   using (_⊂_; inject)

data Shape (S : Set) : Set where
  putˢ : S → Shape S
  getˢ : Shape S

pos : (S : Set) → Shape S → Set
pos S (putˢ _) = ⊤
pos S getˢ     = S

state : Set → Container
state S = Shape S ▷ pos S

runState : {F : Container} {A S : Set} → S → Free (state S ⊕ F) A → Free F (S × A)
runState s₀ (pure x) = pure (s₀ , x)
runState s₀ (impure (inj₁ (putˢ s) , pf)) = runState s (pf tt)
runState s₀ (impure (inj₁ getˢ     , pf)) = runState s₀ (pf s₀)
runState s₀ (impure (inj₂ s        , pf)) = impure (s , runState s₀ ∘ pf )

evalState : {F : Container} {A S : Set} → S → Free (state S ⊕ F) A → Free F A
evalState s₀ p = map proj₂ (runState s₀ p)

get : {F : Container} {S : Set} → ⦃ state S ⊂ F ⦄ → Free F S
get = inject (getˢ , pure)

put : {F : Container} {S : Set} → ⦃ state S ⊂ F ⦄ → S → Free F ⊤
put s = inject (putˢ s , λ tt → pure tt)

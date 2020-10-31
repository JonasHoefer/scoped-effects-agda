module Effect.State where

open import Function       using (id; _∘_; const; _$_; flip)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Product   using (_×_; _,_; proj₂)
open import Data.Unit      using (⊤; tt)

open import Variables
open import Effect
open import Prog
open import Prog.Instances


private
  variable
    S : Set

data Stateˢ (S : Set) : Set where
  getˢ : Stateˢ S
  putˢ : S → Stateˢ S

State : Set → Effect
Ops  (State S) = Stateˢ S ▷ λ{ getˢ → S ; (putˢ _) → ⊤ }
Scps (State S) = Void

pattern Get κ = (inj₁ getˢ , κ)
pattern Put s κ = (inj₁ (putˢ s) , κ)

runState : Prog (State S ∷ effs) A → S → Prog effs (S × A)
runState {S} {effs} {A} = foldP (λ i → (λ X → S → Prog effs (S × X)) ^ i $ A) 1 id
  (λ a s₀ → var (s₀ , a))
  (λ where
    (Get κ)     s₀ → κ s₀ s₀
    (Put s₁ κ)  s₀ → κ tt s₁
    (Other s κ) s₀ → op (s , λ c → κ c s₀)
  ) λ where
    (Other s κ) s₀ → scp (s , λ c → (λ (a , f) → f a) <$> κ c s₀)

evalState : Prog (State S ∷ effs) A → S → Prog effs A
evalState p s₀ = proj₂ <$> runState p s₀

get : ⦃ State S ∈ effs ⦄ → Prog effs S
get = Op (getˢ , pure)

put : ⦃ State S ∈ effs ⦄ → S → Prog effs ⊤
put s = Op (putˢ s , pure)

-- we can simulate local using state operations
local : ⦃ State S ∈ effs ⦄ → (S → S) → Prog effs A → Prog effs A
local f p = do s₀ ← get ; put (f s₀) ; x ← p ; put s₀ ; return x

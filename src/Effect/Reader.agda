module Effect.Reader where

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
    Γ : Set

data Askˢ   (Γ : Set) : Set where askˢ   : Askˢ Γ
data Localˢ (Γ : Set) : Set where localˢ : (Γ → Γ) → Localˢ Γ

Reader : Set → Effect
Ops  (Reader Γ) = Askˢ   Γ ~> Γ
Scps (Reader Γ) = Localˢ Γ ~> ⊤

pattern Ask κ = (inj₁ askˢ , κ)
pattern Local s κ = (inj₁ (localˢ s) , κ)

runReader : Prog (Reader Γ ∷ effs) A → Γ → Prog effs A
runReader {Γ} {effs} {A} = foldP (λ i → (λ X → Γ → Prog effs X) ^ i $ A) 1 id
  (const ∘ var)
  ( λ where
    (Ask κ)     γ → κ γ γ
    (Other s κ) γ → op (s , λ p → κ p γ)
  ) λ where
    (Local t κ) γ → κ tt (t γ) >>= (_$ γ)
    (Other s κ) γ → scp (s , λ p → (_$ γ) <$> κ p γ)

ask : ⦃ Reader Γ ∈ effs ⦄ → Prog effs Γ
ask = Op (askˢ , pure)

local : ⦃ Reader Γ ∈ effs ⦄ → (Γ → Γ) → Prog effs A → Prog effs A
local t p = Scp (localˢ t , λ _ → pure <$> p)

asks : ⦃ Reader Γ ∈ effs ⦄ → (Γ → A) → Prog effs A
asks = _<$> ask

module Effect.Exc where

open import Function using (id; _∘_; const; _$_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Bool  using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum   using (_⊎_; inj₁; inj₂; [_,_])

open import Variables
open import Effect
open import Prog
open import Prog.Instances

----------------------
-- Exception effect --
----------------------

-- An in depth explanation can be found in the thesis.

data Excˢ (E : Set) : Set where throwˢ : (e : E) → Excˢ E
data Catchˢ         : Set where catchˢ : Catchˢ
data Catchᵖ (E : Set) : Set where
  mainᵖ   : Catchᵖ E
  handleᵖ : (e : E) → Catchᵖ E

Exc : Set → Effect
Ops  (Exc E) = Excˢ E ~> ⊥
Scps (Exc E) = Catchˢ ~> Catchᵖ E

pattern Throw e = (inj₁ (throwˢ e) , _)
pattern Catch κ = (inj₁ catchˢ , κ)

runExc : ∀ {E} → Prog (Exc E ∷ effs) A → Prog effs (E ⊎ A)
runExc {effs} {A} {E} = foldP (λ i → ((Prog effs ∘ (E ⊎_)) ^ i) A) 1 id
  (var ∘ inj₂)
  (λ where
    (Throw e)   → var (inj₁ e)
    (Other s κ) → op (s , κ)
  ) λ where
    (Catch κ) → κ mainᵖ >>= λ where
      (inj₁ e) → κ (handleᵖ e) >>= λ where
        (inj₁ e) → var (inj₁ e)
        (inj₂ x) → x
      (inj₂ x) → x
    (Other s κ) → scp (s , ([ var ∘ inj₁ , id ] <$>_) ∘ κ)

throw : ∀ {E} → ⦃ Exc E ∈ effs ⦄ → E → Prog effs A
throw e = Op (throwˢ e , λ())

infixl 0 _catch_
_catch_ : ∀ {E} → ⦃ Exc E ∈ effs ⦄ → Prog effs A → (E → Prog effs A) → Prog effs A
ma catch h = Scp (catchˢ , λ{ mainᵖ → pure <$> ma ; (handleᵖ e) → pure <$> h e })

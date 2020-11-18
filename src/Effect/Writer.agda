
module Effect.Writer where

open import Function       using (id; _∘_; const; _$_; flip)
open import Level          using (0ℓ)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Product   using (_×_; _,_; map₁)
open import Data.Unit      using (⊤; tt)

open import Variables
open import Effect
open import Prog
open import Prog.Instances

open import Algebra.Structures using (IsMonoid)


private
  variable
    M : Set

-- It seems that listen and pass cannot be implemented directly with this approach.
-- See last paragraph of "Syntax and Semantics for Operations with Scopes"
--
-- Similar to the HO approach with indexed bi-container representation the syntax is not expressive enough.
-- It is possible to generalize the syntax (Future Work) or to simulate the writer effect using state.

data Tellˢ   (M : Set) : Set where tellˢ   : M → Tellˢ M
data Censorˢ (M : Set) : Set where censorˢ : (M → M) → Censorˢ M

Writer : Set → Effect
Ops  (Writer M) = Tellˢ   M ~> ⊤
Scps (Writer M) = Censorˢ M ~> ⊤

pattern Tell m   κ = (inj₁ (tellˢ m) , κ)
pattern Censor c κ = (inj₁ (censorˢ c) , κ)

runWriter : ∀ {_·_ : M → M → M} {ε : M} {≈} → ⦃ IsMonoid {0ℓ} {0ℓ} ≈ _·_ ε ⦄ → Prog (Writer M ∷ effs) A → Prog effs (M × A)
runWriter {M} {effs} {A} {_·_} {ε} p = foldP (λ i → (λ X → M → Prog effs (M × X)) ^ i $ A) 1 id
  (λ p m → var (m , p))
  ( λ where
    (Tell m  κ) m′ → κ tt (m′ · m)
    (Other s κ) a  → op (s , flip κ a)
  )(λ where
    (Censor c κ) m → κ tt ε >>= λ (m′ , p) → p (m · c m′)
    (Other s  κ) m → scp (s , λ p → (λ (a , f) → f a) <$> κ p m)
  ) p $ ε

tell : ⦃ Writer M ∈ effs ⦄ → M → Prog effs ⊤
tell m = Op (tellˢ m , pure)

censor : ⦃ Writer M ∈ effs ⦄ → (M → M) → Prog effs A → Prog effs A
censor c p = Scp (censorˢ c , λ (tt) → pure <$> p)

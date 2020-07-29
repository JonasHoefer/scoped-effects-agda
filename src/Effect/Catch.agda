module Effect.Catch where

open import Function      using (_∘_)
open import Size          using (Size; ↑_)

open import Data.Bool     using (true; false)
open import Data.Unit     using (⊤; tt)
open import Data.Empty    using (⊥)
open import Data.Maybe    using (Maybe; nothing; just)
open import Data.Product  using (_,_)
open import Data.Sum      using (_⊎_; inj₁; inj₂)

open import Container     using (Container; _▷_; _⊕_)
open import Free
open import Injectable    using (_⊂_; inject; project; upcast)

open import Effect.Exc    using (exc; runExc)

data Shape (E : Set) : Set where
  bcatchˢ : Shape E
  ecatchˢ : Shape E

pattern BCatch pf = impure (inj₁ bcatchˢ , pf)
pattern ECatch pf = impure (inj₁ ecatchˢ , pf)

-- E ⊎ ⊤ continuation for exception handling and the next computiation
catch : Set → Container
catch E = Shape E ▷ λ{ bcatchˢ → E ⊎ ⊤ ; ecatchˢ → ⊤}

module _ {F : Container} {E : Set} ⦃ _ : catch E ⊂ F ⦄ where
  begin : {A : Set} → Free F A → (E → Free F A) → Free F A
  begin p h = inject (bcatchˢ , λ { (inj₁ e) → h e ; (inj₂ tt) → p})

  end : Free F ⊤
  end = inject (ecatchˢ , λ _ → pure tt)

_catchE_ : ∀ {F A E} → ⦃ catch E ⊂ F ⦄ → Free F A → (E → Free F A) → Free F A
p catchE h = begin (do x ← p ; end ; pure x) h
  where open RawMonad freeMonad using (_>>=_; _>>_)

ecatch : ∀ {F A E i} → Free (catch E ⊕ exc E ⊕ F) A {i} → Free (exc E ⊕ F) (Free (catch E ⊕ exc E ⊕ F) A {i})
ecatch (pure x)    = pure (pure x)
ecatch (BCatch pf) = upcast (runExc (ecatch (pf (inj₂ tt)))) >>= λ where
    (inj₁ e) → ecatch (pf (inj₁ e))
    (inj₂ k) → ecatch k
  where open RawMonad freeMonad using (_>>=_)
ecatch (ECatch pf) = pure (pf tt)
ecatch (impure (inj₂ s , pf)) = impure (s , ecatch ∘ pf)

bcatch : ∀ {F A E i} → Free (catch E ⊕ exc E ⊕ F) A {i} → Free (exc E ⊕ F) A
bcatch (pure x)    = pure x
bcatch (BCatch pf) = upcast (runExc (ecatch (pf (inj₂ tt)))) >>= λ where
    (inj₁ e) → bcatch (pf (inj₁ e))
    (inj₂ k) → bcatch k
  where open RawMonad freeMonad using (_>>=_)
bcatch (ECatch pf) = bcatch (pf tt)
bcatch (impure (inj₂ s , pf)) = impure (s , bcatch ∘ pf)

runCatch : ∀ {F A E} → Free (catch E ⊕ exc E ⊕ F) A → Free F (E ⊎ A)
runCatch = runExc ∘ bcatch

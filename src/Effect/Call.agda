{-# OPTIONS --overlapping-instances #-}

module Effect.Call where

open import Function      using (_∘_)
open import Size          using (Size; ↑_)

open import Data.Bool     using (true; false)
open import Data.Unit     using (⊤; tt)
open import Data.Empty    using (⊥)
open import Data.Maybe    using (Maybe; nothing; just)
open import Data.Product  using (_,_)
open import Data.Sum      using (inj₁; inj₂)

open import Container     using (Container; _▷_; _⊕_)
open import Free          using (Free; pure; impure; _<$>_; _<*>_; _>>=_; _>>_)
open import Injectable    using (_⊂_; inject; project; upcast)

open import Effect.Nondet using (nondet; fail; _⁇_; choiceˢ; failˢ)
open import Effect.Cut    using (cut)                                           renaming (call to callᶜ)

data Shape : Set where
  bcall′ : Shape
  ecall′ : Shape

call : Container
call = Shape ▷ λ _ → ⊤

pattern BCall pf = impure (inj₁ bcall′ , pf)
pattern ECall pf = impure (inj₁ ecall′ , pf)

module _ {F : Container} ⦃ _ : call ⊂ F ⦄ where
  begin : Free F ⊤
  begin = inject (bcall′ , λ _ → pure tt)

  end : Free F ⊤
  end = inject (ecall′ , λ _ → pure tt)

call′ : {F : Container} {A : Set} → ⦃ call ⊂ F ⦄ → Free F A → Free F A
call′ p = do begin ; x ← p ; end ; pure x

ecall : {i : Size} {A : Set} {F : Container} → ⦃ nondet ⊂ F ⦄ → Free (call ⊕ cut ⊕ F) A {i} → Free (cut ⊕ F) (Free (call ⊕ cut ⊕ F) A {i})
ecall (pure x)   = pure (pure x)
ecall (BCall pf) = upcast (callᶜ (ecall (pf tt))) >>= ecall
ecall (ECall pf) = pure (pf tt)
ecall (impure (inj₂ s , pf)) = impure (s , ecall ∘ pf)

bcall : {i : Size} {A : Set} {F : Container} → ⦃ nondet ⊂ F ⦄ → Free (call ⊕ cut ⊕ F) A {i} → Free (cut ⊕ F) A
bcall (pure x)   = pure x
bcall (BCall pf) = upcast (callᶜ (ecall (pf tt))) >>= bcall
-- We have to work in a total context. To avoid handling wrong scopes we correct the error.
bcall (ECall pf) = bcall (pf tt)
bcall (impure (inj₂ s , pf)) = impure (s , bcall ∘ pf)

runCut : {A : Set} {F : Container} → ⦃ nondet ⊂ F ⦄ → Free (call ⊕ cut ⊕ F) A → Free F A
runCut p = callᶜ (bcall p)

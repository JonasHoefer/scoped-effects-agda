{-# OPTIONS --overlapping-instances #-}

module Effect.Cut where

open import Size          using (Size; ↑_)

open import Data.Bool     using (true; false)
open import Data.Unit     using (⊤; tt)
open import Data.Empty    using (⊥)
open import Data.Maybe    using (Maybe; nothing; just)
open import Data.Product  using (_,_)
open import Data.Sum      using (inj₁; inj₂)

open import Container     using (Container; _▷_; _⊕_)
open import Free          using (Free; freeMonad; RawMonad; pure; impure)
open import Injectable    using (_⊂_; inject; project)

open import Effect.Nondet using (Nondet; fail; _⁇_; choiceˢ; failˢ)

data Shape : Set where
  cutfail′ : Shape

Cut : Container
Cut = Shape ▷ λ _ → ⊥

call : {i : Size} {F : Container} {A : Set} → ⦃ Nondet ⊂ F ⦄ → Free (Cut ⊕ F) A {i} → Free F A
call p = go p fail
  where
    go : {i : Size} {F : Container} {A : Set} → ⦃ Nondet ⊂ F ⦄ → Free (Cut ⊕ F) A {i} → Free F A → Free F A
    go (pure x)                      q = pure x ⁇ q
    go (impure (inj₁ cutfail′ , pf)) q = fail
    go f@(impure (inj₂ s , pf))      q with project {Nondet} f
    ... | just (choiceˢ _ , pf′) = go (pf′ false) (go (pf′ true) q)
    ... | just (failˢ     , pf′) = q
    ... | nothing                = impure (s , λ p → go (pf p) q )

cutfail : {F : Container} {A : Set} → ⦃ Cut ⊂ F ⦄ → Free F A
cutfail = inject (cutfail′ , λ())

cut : {F : Container} → ⦃ Cut ⊂ F ⦄ → ⦃ Nondet ⊂ F ⦄ → Free F ⊤
cut = pure tt ⁇ cutfail

once : {F : Container} {A : Set} → ⦃ Nondet ⊂ F ⦄ → Free (Cut ⊕ F) A → Free F A
once p = call (do x ← p ; cut ; return x)
  where open RawMonad freeMonad hiding (pure)

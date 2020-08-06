{-# OPTIONS --overlapping-instances #-}

module Data.MList where

open import Size          using (Size; ↑_)

open import Data.List     using (List; _∷_; [])
open import Data.Nat      using (ℕ; _+_)
open import Data.Product  using (_×_; _,_)

open import Container     using (Container)
open import Free
open import Injectable    using (_⊂_)

open import Effect.Nondet using (Nondet; fail)
open import Effect.Share  using (Share; share; Normalform; nf; Shareable)
open import Effect.State  using (State)

data Listᴹ (C : Container) (A : Set) : {Size} → Set where
  nil  : ∀ {i} → Listᴹ C A {i}
  cons : ∀ {i} → Free C A → Free C (Listᴹ C A {i}) → Listᴹ C A {↑ i}

infixr 5 _∷ᴹ_ _++_
pattern []ᴹ         = pure nil
pattern _∷ᴹ_ mx mxs = pure (cons mx mxs)

head : {F : Container} {A : Set} → ⦃ Nondet ⊂ F ⦄ → Free F (Listᴹ F A) → Free F A
head = _>>= λ where
   nil         → fail
   (cons mx _) → mx
 where open RawMonad freeMonad

_++_ : ∀ {F A i} → Free F (Listᴹ F A {i}) → Free F (Listᴹ F A) → Free F (Listᴹ F A)
mxs ++ mys = mxs >>= λ where
    nil           → mys
    (cons mx mxs) → mx ∷ᴹ mxs ++ mys
 where open RawMonad freeMonad

sum : {i : Size} → {F : Container} → Free F (Listᴹ F ℕ {i}) → Free F ℕ
sum xs = xs >>= λ where
    nil          → return 0
    (cons x mxs) → _+_ <$> x ⊛ sum mxs
  where open RawMonad freeMonad

instance
  Listᴹ-normalform : ∀ {N A B i} → ⦃ Normalform N A B ⦄ → Normalform N (Listᴹ N A {i}) (List B)
  Normalform.nf Listᴹ-normalform = _>>= λ where
       nil           → pure []
       (cons mx mxs) → _∷_ <$> nf mx ⊛ nf mxs
     where open RawMonad freeMonad hiding (pure)

  Listᴹ-shareable : ∀ {M A i} → ⦃ Shareable M A ⦄ → ⦃ Share ⊂ M ⦄ → ⦃ State (ℕ × ℕ) ⊂ M ⦄ → Shareable M (Listᴹ M A {i})
  Shareable.shareArgs Listᴹ-shareable nil           = []ᴹ
  Shareable.shareArgs Listᴹ-shareable (cons mx mxs) = share mx >>= λ my → share mxs >>= λ mys →  my ∷ᴹ mys -- cons <$> share mx ⊛ share mxs
    where open RawMonad freeMonad

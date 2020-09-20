module Data.MList where

open import Size                   using (Size; ↑_)

open import Category.Monad         using (RawMonad)
open        RawMonad ⦃...⦄         renaming (_⊛_ to _<*>_)

open import Data.List              using (List; _∷_; [])
open import Data.Normalform        using (Normalform)
open        Normalform ⦃...⦄

open import Variables
open import Effect
open import Effect.State
open import Effect.Share
open import Effect.Share.Shareable using (Shareable)
open        Shareable ⦃...⦄
open import Prog
open import Prog.Instances

data Listᴹ (effs : List Effect) (A : Set) : {Size} → Set where
  nilᴹ : Listᴹ effs A {i}
  consᴹ : (mx : Prog effs A) → (mxs : Prog effs (Listᴹ effs A {i})) → Listᴹ effs A {↑ i}

infixr 5 _∷ᴹ_ _++ᴹ_
pattern []ᴹ = var nilᴹ
pattern _∷ᴹ_ mx mxs = var (consᴹ mx mxs)

_++ᴹ_ : Prog effs (Listᴹ effs A {i}) → Prog effs (Listᴹ effs A) → Prog effs (Listᴹ effs A)
mxs ++ᴹ mys = mxs >>= λ where
  nilᴹ           → mys
  (consᴹ mx mxs) → mx ∷ᴹ mxs ++ᴹ mys

instance
  Listᴹ-Normalform : ⦃ Normalform effs A B ⦄ → Normalform effs (Listᴹ effs A {i}) (List B)
  Normalform.nf Listᴹ-Normalform nilᴹ           = var []
  Normalform.nf Listᴹ-Normalform (consᴹ mx mxs) = ⦇ ! mx ∷ ! mxs ⦈

  Listᴹ-Shareable : ⦃ Shareable effs A ⦄ → ⦃ State SID ∈ effs ⦄ → ⦃ Share ∈ effs ⦄ → Shareable effs (Listᴹ effs A {i})
  Shareable.shareArgs Listᴹ-Shareable nilᴹ           = []ᴹ
  Shareable.shareArgs Listᴹ-Shareable (consᴹ mx mxs) = ⦇ consᴹ (share mx) (share mxs) ⦈

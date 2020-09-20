
{-# OPTIONS --overlapping-instances #-}
module Effect.Share where

open import Function        using (id; _∘_; const; _$_; case_of_)

open import Category.Monad  using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Bool       using (Bool; true; false; if_then_else_)
open import Data.Unit       using (⊤; tt)
open import Data.Maybe      using (Maybe; just; nothing)
open import Data.Nat        using (ℕ; _+_)
open import Data.Normalform
open import Data.Tree       using (SID) public

open import Variables
open import Effect
open import Effect.Nondet
open import Effect.Share.Shareable
open import Effect.State
open import Prog
open import Prog.Instances


data Shareˢ : Set where shareˢ : SID → Shareˢ

Share : Effect
Ops Share  = Void
Scps Share = Shareˢ ~> ⊤

pattern ShareScp sid κ = (inj₁ (shareˢ sid) , κ)

share⟨_⟩ : ⦃ Share ∈ effs ⦄ → SID → Prog effs A → Prog effs A
share⟨_⟩ {Scps} {Ops} sid p = Scp (shareˢ sid , λ _ → pure <$> p)

share : ⦃ State SID ∈ effs ⦄ → ⦃ Share ∈ effs ⦄ → ⦃ Shareable effs A ⦄ → Prog effs A → Prog effs (Prog effs A)
share {Ops} {Scps} p = do
    (i , j) ← get
    put (i + 1 , j)
    let p′ = do put (i , j + 1)
                x  ← p
                x′ ← shareArgs x
                put (i + 1 , j)
                return x′
    return $ share⟨ i , j ⟩ p′

runShare′ : ⦃ Nondet ∈ effs ⦄ → Prog (Share ∷ effs) A → SID → ℕ → Prog effs A
runShare′ {effs} {A} ⦃ p ⦄ = foldP (λ i → ((λ X → SID → ℕ → Prog effs X) ^ i) A) 1 id
  (λ z _ _ → var z)
  (λ{ (Other s pf) → case prj (ops-inj p) (s , pf) of λ where
    nothing                sid n → op (s , λ p → pf p sid n)
    (just (failˢ     , κ)) sid n → fail
    (just (choiceˢ _ , κ)) sid n → Op (choiceˢ (just (sid , n)) , λ p → κ p sid (suc n))
  }) λ where
    (ShareScp sid′ κ) sid n → κ tt sid′ 1 >>= λ r → r sid n
    (Other    s    κ) sid n → scp (s , λ p → (λ k → k sid n) <$> κ p sid n)

runShare : ⦃ Nondet ∈ effs ⦄ → Prog (Share ∷ effs) A → Prog effs A
runShare p = runShare′ p (0 , 0) 0

runCurry : ⦃ Normalform (State SID ∷ Share ∷ Nondet ∷ []) A B ⦄ → Prog (State SID ∷ Share ∷ Nondet ∷ []) A → List B
runCurry p = run $ runNondet $ runShare $ evalState (! p) (0 , 0)

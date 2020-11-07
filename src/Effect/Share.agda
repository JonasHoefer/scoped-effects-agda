
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
open import Data.Product    using (_×_; proj₂)
open import Data.Tree       using (SID; CID) public

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

runShare′ : ⦃ Nondet ∈ effs ⦄ → Prog (Share ∷ effs) A → Maybe CID → Prog effs (Maybe CID × A)
runShare′ {effs} {A} ⦃ p ⦄ = foldP (λ i → ((λ X → Maybe CID → Prog effs (Maybe CID × X)) ^ i) A) 1 id
  (λ z cid → var (cid , z))
  (λ{ (Other s pf) → case prj (ops-inj p) (s , pf) of λ where
    nothing                cid              → op (s , λ p → pf p cid)
    (just (failˢ     , κ)) cid              → fail
    (just (choiceˢ _ , κ)) (just (sid , n)) → Op (choiceˢ (just (sid , n)) , λ p → κ p (just (sid , (suc n))))
    (just (choiceˢ _ , κ)) nothing          → Op (choiceˢ nothing , λ p → κ p nothing)
  }) λ where
    (ShareScp sid′ κ) cid → κ tt (just (sid′ , 0)) >>= λ (_ , r) → r cid
    (Other    s    κ) sid → scp (s , λ p → (λ (sid′ , k) → k sid′) <$> κ p sid) -- TODO: thread id through

runShare : ⦃ Nondet ∈ effs ⦄ → Prog (Share ∷ effs) A → Prog effs A
runShare p = proj₂ <$> runShare′ p nothing

runCTC : ⦃ Normalform (State SID ∷ Share ∷ Nondet ∷ []) A B ⦄ → Prog (State SID ∷ Share ∷ Nondet ∷ []) A → List B
runCTC p = run $ runNondet $ runShare $ evalState (! p) (0 , 0)

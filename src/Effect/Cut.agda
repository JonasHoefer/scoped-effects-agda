module Effect.Cut where

open import Function using (id; _∘_; const; _$_; case_of_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Bool  using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Tree
open import Data.Unit  using (⊤; tt)

open import Variables
open import Effect
open import Effect.Nondet
open import Prog
open import Prog.Instances

data Cutˢ : Set where cutfailˢ : Cutˢ
data Callˢ : Set where callˢ : Callˢ

Cut : Effect
Ops  Cut = Cutˢ ~> ⊥
Scps Cut = Callˢ ~> ⊤

pattern Cutfail = (inj₁ cutfailˢ , _)
pattern Call κ = (inj₁ callˢ , κ)

runCut′ : ⦃ Nondet ∈ effs ⦄ → Prog (Cut ∷ effs) A → Prog effs A → Prog effs A
runCut′ {effs} {A} ⦃ p ⦄ = foldP (λ i → ((λ X → Prog effs X → Prog effs X) ^ i) A) 1 id
  (λ x q → var x ⁇ q)
  (λ where
    Cutfail q     → fail
    (Other s κ) q → case prj (ops-inj p) (s , κ) of λ where
      nothing  → op (s , λ p → κ p q)
      (just (failˢ       , _)) → q
      (just (choiceˢ cid , κ)) → κ true (κ false q) -- cid?
  ) λ where
    (Call κ)    q → κ tt fail >>= λ r → r q
    (Other s κ) q → scp (s , λ p → (λ r → r q) <$> κ p fail) -- Wrong! Pass results to next one? Similar problem to Bunkenburgs HO impl

runCut : ⦃ Nondet ∈ effs ⦄ → Prog (Cut ∷ effs) A → Prog effs A
runCut p = runCut′ p fail

cutfail : ⦃ Cut ∈ effs ⦄ → Prog effs A
cutfail = Op (cutfailˢ , λ())

call : ⦃ Cut ∈ effs ⦄ → Prog effs A → Prog effs A
call p = Scp (callˢ , λ{ tt → pure <$> p })

cut : ⦃ Cut ∈ effs ⦄ → ⦃ Nondet ∈ effs ⦄ → Prog effs ⊤
cut = pure tt ⁇ cutfail

once : ⦃ Cut ∈ effs ⦄ → ⦃ Nondet ∈ effs ⦄ → Prog effs A → Prog effs A
once p = call (do x ← p ; cut ; pure x)

------------------------------------------------------------------------------------------------
-- Handler for Nondet and Cut, that cuts computations and traverses foreign socpes correctly¹ --
------------------------------------------------------------------------------------------------

-- ¹: modulo known Nondet problems

open import Data.List using (_++_)
open import Data.Product using (proj₂)

hdlᴮ : List (Prog effs (Bool × List A)) → Prog effs (Bool × List A)
hdlᴮ []       = var (false , [])
hdlᴮ (x ∷ xs) = x >>= λ where
  (true  , r) → var (true , r)
  (false , r) → hdlᴮ xs >>= λ where
    (didCut , rs) → var (didCut , r ++ rs)

runCutᴮ : Prog (Cut ∷ Nondet ∷ effs) A → Prog effs (Bool × List A)
runCutᴮ {effs} {A} = foldP (λ i → ((λ X → Prog effs (Bool × List X)) ^ i) A) 1 id
  (λ x → var (false , x ∷ []))
  (λ where
    Cutfail                        → var (true  , []) -- did cut
    (Other (inj₁ failˢ)         κ) → var (false , []) -- did not cut
    (Other (inj₁ (choiceˢ cid)) κ) → κ true >>= λ where
      (true  , l) → pure (true , l)
      (false , l) → κ false >>= λ where
        (didCut , r) → var (didCut , l ++ r)
    (Other (inj₂ s) κ) → op (s , κ)
  ) λ where
    (Call κ)           → κ tt >>= λ (_ , rs) → (λ (_ , rs) → false , rs) <$> hdlᴮ rs -- reset didcut flag
    (Other (inj₂ s) κ) → scp (s , λ p → (λ (didCut , rs) → hdlᴮ rs) <$> κ p)

runCut″ : Prog (Cut ∷ Nondet ∷ effs) A → Prog effs (List A)
runCut″ p = proj₂ <$> runCutᴮ p

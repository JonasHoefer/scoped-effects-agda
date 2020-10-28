{-# OPTIONS --overlapping-instances #-}

module StateCutInteraction where

open import Function       using (id; _$_; flip; case_of_; _∘_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (_++_)
open import Data.Maybe using (Maybe; nothing; just; maybe′; fromMaybe)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (map₂) renaming (map to ⊎-map)
open import Data.Unit using (⊤; tt)

open import Variables
open import Effect
open import Effect.Cut
open import Effect.Nondet hiding (hdl)
open import Effect.State
open import Prog
open import Prog.Instances

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)


data List! (A : Set) : Set where
  [] []! : List! A
  _∷_ : A → List! A → List! A

_+!+_ : List! A → List! A → List! A
[]       +!+ ys = ys
[]!      +!+ ys = []!
(x ∷ xs) +!+ ys = x ∷ (xs +!+ ys)

concat! : List! (List! A) → List! A
concat! []         = []
concat! []!        = []!
concat! (xs ∷ xss) = xs +!+ concat! xss

hdl! : List! (Prog effs (List! A)) → Prog effs (List! A)
hdl! []       = var []
hdl! []!      = var [] -- call -> cutfail ends here
hdl! (x ∷ xs) = ⦇ x +!+ hdl! xs ⦈

hdl : List! (Prog effs (List! A)) → Prog effs (List! A)
hdl []       = var []
hdl []!      = var []!
hdl (x ∷ xs) = ⦇ x +!+ hdl xs ⦈

doesCut : List! A → Bool
doesCut []       = false
doesCut []!      = true
doesCut (_ ∷ xs) = doesCut xs

runCutT : Prog (Cut ∷ Nondet ∷ effs) A → Prog effs (List! A)
runCutT {effs} {A} = foldP (λ i → ((Prog effs ∘ List!) ^ i) A) 1 id
  (var ∘ (_∷ [])) -- concat garanties that an inner []! is preserved
  (λ where
    (inj₁ cutfailˢ ,          κ) → var []!
    (Other (inj₁ failˢ)       κ) → var []
    (Other (inj₁ (choiceˢ _)) κ) → κ true >>= λ xs → if doesCut xs then var xs else ((xs +!+_) <$> κ false)
    (Other (inj₂ s)           κ) → op (s , κ)
  ) λ where
    (Call           κ) → κ tt >>= hdl!
    (Other (inj₂ s) κ) → scp (s , λ p → hdl <$> κ p)

cutLocal cutLocal′ : ⦃ Nondet ∈ effs ⦄ → ⦃ Cut ∈ effs ⦄ → ⦃ State ℕ ∈ effs ⦄ → Prog effs ℕ
cutLocal = pure 1 ⁇ (once (local id (pure 3 ⁇ pure 4))) ⁇ pure 10
cutLocal′ = (local id (pure 3 ⁇ pure 4) ⁇ pure 5) >>= λ x → cut >> pure x

runCutLocal : (run $ flip evalState 0 $ runCutT cutLocal) ≡ 1 ∷ 3 ∷ 10 ∷ []
runCutLocal = refl

runCutLocal′ : (run $ flip evalState 0 $ runCutT cutLocal′) ≡ 3 ∷ []!
runCutLocal′ = refl

{-# OPTIONS --overlapping-instances #-}

module NondetStateInteraction where

open import Function using (_$_; _∘_; flip)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Nat using (ℕ; _+_)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤; tt)

open import Variables
open import Effect
open import Effect.Exc
open import Effect.State
open import Effect.Nondet
open import Prog
open import Prog.Instances

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)


incr : ⦃ State ℕ ∈ effs ⦄ → Prog effs ⊤
incr = get >>= put ∘ suc

foo : ⦃ State ℕ ∈ effs ⦄ → ⦃ Exc ⊤ ∈ effs ⦄ → ⦃ Nondet ∈ effs ⦄ → Prog effs ℕ
foo = ((var tt ⁇ var tt) catch λ _ → throw tt) >>= λ (tt) → (get ⁇ incr >> get)

runFoo : ⊤ ⊎ (List (ℕ × ℕ))
runFoo = run $ runExc $ runNondet $ runState foo 0


-- Bug: Global scopes over Nondet reorder other global operations, because the handler
-- for ⁇ˢ already chains the operations using >>=
-- https://github.com/polysemy-research/polysemy/issues/246
-- Possbile fixes destroy generality of approach.
--
-- same semantics as higher order approach

tell : ⦃ State String ∈ effs ⦄ → String → Prog effs ⊤
tell msg = get >>= λ s → put (s ++ msg)

withScope : ⦃ State String ∈ effs ⦄ → ⦃ Exc ⊤ ∈ effs ⦄ → ⦃ Nondet ∈ effs ⦄ →
  Prog effs ⊤
withScope = do tell "a" ⁇ tell "b" catch λ _ → var tt
               tell "c"

withoutScope : ⦃ State String ∈ effs ⦄ → ⦃ Exc ⊤ ∈ effs ⦄ → ⦃ Nondet ∈ effs ⦄ →
  Prog effs ⊤
withoutScope = do tell "a" ⁇ tell "b"
                  tell "c"

runScopeTest : Prog (Nondet ∷ Exc ⊤ ∷ State String ∷ []) A → String × (⊤ ⊎ List A)
runScopeTest = run ∘ flip runState "" ∘ runExc ∘ runNondet

runWithScope : runScopeTest withScope ≡ ("abcc" , (inj₂ (tt ∷ tt ∷ [])))
runWithScope = refl

runWithoutScope : runScopeTest withoutScope ≡ ("acbc" , (inj₂ (tt ∷ tt ∷ [])))
runWithoutScope = refl

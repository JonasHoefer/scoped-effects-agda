{-# OPTIONS --overlapping-instances #-}

module ReaderExcInteraction where

open import Function using (_$_; flip; id)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (⊤; tt)

open import Variables
open import Effect
open import Effect.Exc
open import Effect.Reader
open import Prog
open import Prog.Instances

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)


localCatchInterleaved : ⦃ Reader ℕ ∈ effs ⦄ → ⦃ Exc ⊤ ∈ effs ⦄ → Prog effs ℕ
localCatchInterleaved = do v₁ ← ask
                           ((local suc ((do v₂ ← ask
                                            local suc (do v₃ ← ask
                                                          pure (v₁ + v₂ + v₃))) catch λ _ → pure 42)) catch λ _ → pure 41)

runLocalCatch1 : run (runExc $ flip runReader 1 localCatchInterleaved) ≡ inj₂ 6
runLocalCatch1 = refl

runLocalCatch2 : run (flip runReader 1 $ runExc localCatchInterleaved) ≡ inj₂ 6
runLocalCatch2 = refl

throwInLocal : ⦃ Reader ℕ ∈ effs ⦄ → ⦃ Exc ⊤ ∈ effs ⦄ → Prog effs ℕ
throwInLocal = (do ask ; local id (throw tt)) catch λ _ → pure 42

runThrowInLocal1 : run (runExc $ flip runReader 1 throwInLocal) ≡ inj₂ 42
runThrowInLocal1 = refl

runThrowInLocal2 : run (flip runReader 1 $ runExc throwInLocal) ≡ inj₂ 42
runThrowInLocal2 = refl

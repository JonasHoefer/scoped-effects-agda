{-# OPTIONS --overlapping-instances #-}

module Reader where

open import Function       using (_$_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ using (_>>=_; _>>_; return)

open import Data.List      using (List)
open import Data.Nat       using (ℕ; _+_)

open import Container      using (Container)
open import Free
open import Free.Instances

open import Effect.Reader using (Reader; runReader; local; ask)

localComp : {F : List Container} → {@(tactic eff) _ : Reader ℕ ∈ F} → Free F ℕ
localComp = local (1 +_) $ do
    x ← ask
    y ← local (1 +_) ask
    pure $ x + y

testReader : ℕ
testReader = run $ runReader 1 $ do
    x ← ask
    y ← localComp
    z ← ask
    pure $ x + y + z

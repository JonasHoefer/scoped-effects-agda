{-# OPTIONS --overlapping-instances #-}

module Reader where

open import Function      using (_$_)

open import Data.Nat      using (ℕ; _+_)

open import Container     using (Container)
open import Free
open import Injectable    using (_⊂_)

open import Effect.Reader using (reader; runReader; local; ask)
open import Effect.Void   using (run)

localComp : {F : Container} → ⦃ reader ℕ ⊂ F ⦄ → Free F ℕ
localComp = local (1 +_) $ do
    x ← ask
    y ← local (1 +_) ask
    pure $ x + y
  where open RawMonad freeMonad using (_>>=_; _>>_)

testReader : ℕ
testReader = run $ runReader 1 $ do
    x ← ask
    y ← localComp
    z ← ask
    pure $ x + y + z
  where open RawMonad freeMonad using (_>>=_; _>>_)

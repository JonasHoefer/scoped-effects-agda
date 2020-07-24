{-# OPTIONS --overlapping-instances #-}

module Reader where

open import Function      using (_$_)

open import Data.Nat      using (ℕ; _+_)

open import Container     using (Container)
open import Free          using (Free; pure; _>>=_)
open import Injectable    using (_⊂_)

open import Effect.Reader using (reader; runReader; local; ask)
open import Effect.Void   using (run)

localComp : {F : Container} → ⦃ reader ℕ ⊂ F ⦄ → Free F ℕ
localComp = local (λ x → 1 + x) ask

testReader : ℕ
testReader = run $ runReader 1 $ do
  x ← ask
  y ← localComp
  z ← ask --wrong!
  pure $ x + y + z

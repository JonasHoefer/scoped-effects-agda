{-# OPTIONS --overlapping-instances #-}

module State where


open import Data.Nat      using (ℕ; _+_)
open import Data.Product  using (_×_)
open import Data.Unit     using (⊤)

open import Container     using (Container)
open import Free
open import Injectable    using (_⊂_)

open import Effect.State  using (state; runState; get; put)
open import Effect.Void   using (run)

tick : {F : Container} → ⦃ state ℕ ⊂ F ⦄ → Free F ⊤
tick = get >>= λ n → put (n + 1)
  where open RawMonad freeMonad using (_>>=_)

testState : ℕ × ⊤
testState = run (runState 0 (tick >> tick >> tick))
  where open RawMonad freeMonad using (_>>_)

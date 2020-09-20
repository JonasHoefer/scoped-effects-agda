module State where

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ hiding (pure)

open import Data.Nat       using (ℕ; _+_)
open import Data.Product   using (_×_)
open import Data.Unit      using (⊤)

open import Container      using (Container)
open import Free
open import Free.Instances

open import Effect.State   using (State; runState; get; put)

tick : ∀ {F} → {@(tactic eff) _ : State ℕ ∈ F } → Free F ⊤
tick = get >>= λ n → put (n + 1)

testState : ℕ × ⊤
testState = run (runState 0 (tick >> tick >> tick))

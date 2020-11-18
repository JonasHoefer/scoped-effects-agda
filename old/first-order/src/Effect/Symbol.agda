module Effect.Symbol where

open import Function       using (_∘_; flip)
open import Size           using (Size; ↑_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ using (_<$>_; _>>=_; _>>_; return)

open import Data.Bool      using (Bool; true; false; if_then_else_)
open import Data.Char      using (Char; _==_; toℕ)
open import Data.Empty     using (⊥)
open import Data.List      using (List; []; _∷_; _++_; foldr)
open import Data.Maybe     using (Maybe; just; nothing)
open import Data.Nat       using (ℕ; _∸_)
open import Data.Product   using (_,_)
open import Data.Sum       using (inj₁; inj₂)
open import Data.Unit      using (⊤; tt)

open import Container      using (Container; _▷_; _⊕_)
open import Free
open import Free.Instances

open import Effect.Nondet  using (Nondet; _⁇_; fail)

--------------------------------
-- Symbol following Wu et al. --
--------------------------------

-- The usual definitions of some and many are problematic because they allow iterating arbitrary operations.
-- Technically they produce arbitrarily large programs.
-- The effect can be implemented analogously to Haskell and is still a usefull test.
-- Implementing a (usefull) version of this effect without inherent termination problems is outside the scope for this thesis.

data Shape : Set where
  symbolˢ : Char → Shape

Symbol : Container
Symbol = Shape ▷ λ _ → ⊤

pattern Symbolˢ c pf = impure (inj₁ (symbolˢ c) , pf)

private
  variable
    F : List Container
    A : Set

parse : {@(tactic eff) _ : Nondet ∈ F} → Free (Symbol ∷ F) A → List Char → Free F A
parse (pure x)       []       = pure x
parse (pure _)       (x ∷ xs) = fail
parse (Symbolˢ c pf) []       = fail
parse (Symbolˢ c pf) (x ∷ xs) = if x == c then parse (pf tt) xs else fail
parse (Other s pf)   xs       = impure (s , flip parse xs ∘ pf)

symbolᴾ : {@(tactic eff) symbol : Symbol ∈ F} → Char → Free F Char
symbolᴾ c = op (symbolˢ c , λ tt → pure c)

digitᵖ : {@(tactic eff) _ : Symbol ∈ F} → {@(tactic eff) _ : Nondet ∈ F} → Free F Char
digitᵖ = foldr _⁇_ fail -- shortest solutions with the current std lib ...
  (Data.List.map symbolᴾ ('9' ∷ '8' ∷ '7' ∷ '6' ∷ '5' ∷ '4' ∷ '3' ∷ '2' ∷ '1' ∷ '0' ∷ []))

numberᴾ : {@(tactic eff) _ : Symbol ∈ F} → {@(tactic eff) _ : Nondet ∈ F} → Free F ℕ
numberᴾ = (λ c → toℕ c ∸ toℕ '0') <$> digitᵖ

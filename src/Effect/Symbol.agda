module Effect.Symbol where

open import Function      using (_∘_)
open import Size          using (Size; ↑_)

open import Data.Bool     using (Bool; true; false; if_then_else_)
open import Data.Char     using (Char; _==_; toℕ)
open import Data.Empty    using (⊥)
open import Data.List     using (List; []; _∷_; _++_; foldr)
open import Data.Maybe    using (Maybe; just; nothing)
open import Data.Nat      using (ℕ; _∸_)
open import Data.Product  using (_,_)
open import Data.Sum      using (inj₁; inj₂)
open import Data.Unit     using (⊤; tt)

open import Container     using (Container; _▷_; _⊕_)
open import Free
open import Injectable    using (_⊂_; inject; project)

open import Effect.Nondet using (nondet; _⁇_; fail)

data Shape : Set where
  symbolˢ : Char → Shape

symbol : Container
symbol = Shape ▷ λ _ → ⊤

pattern Symbol c pf = impure (inj₁ (symbolˢ c) , pf)
pattern Other s pf = impure (inj₂ s , pf)

parse : {F : Container} {A : Set} → ⦃ nondet ⊂ F ⦄ → List Char → Free (symbol ⊕ F) A → Free F A
parse []       (pure x)      = pure x
parse (x ∷ xs) (pure _)      = fail
parse []       (Symbol c pf) = fail
parse (x ∷ xs) (Symbol c pf) = if x == c then parse xs (pf tt) else fail
parse xs       (Other s pf)  = impure (s , parse xs ∘ pf)

module _ {F : Container} ⦃ _ : symbol ⊂ F ⦄ where
  symbolᴾ : Char → Free F Char
  symbolᴾ c = inject (symbolˢ c , λ tt → pure c)

  digitᵖ : ⦃ nondet ⊂ F ⦄ → Free F Char
  digitᵖ = foldr _⁇_ fail -- shortest solutions with the current std lib ...
    (Data.List.map symbolᴾ ('9' ∷ '8' ∷ '7' ∷ '6' ∷ '5' ∷ '4' ∷ '3' ∷ '2' ∷ '1' ∷ '0' ∷ []))

  -- TODO: `some` and `many`
  numberᴾ : ⦃ nondet ⊂ F ⦄ → Free F ℕ
  numberᴾ = map (λ c → toℕ c ∸ toℕ '0') digitᵖ

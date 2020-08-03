module Effect.Symbol where

open import Function      using (_∘_; flip)
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
open import Injectable    using (_⊂_; inject; project; Other)

open import Effect.Nondet using (Nondet; _⁇_; fail)

data Shape : Set where
  symbolˢ : Char → Shape

Symbol : Container
Symbol = Shape ▷ λ _ → ⊤

pattern Symbolˢ c pf = impure (inj₁ (symbolˢ c) , pf)

parse : {F : Container} {A : Set} → ⦃ Nondet ⊂ F ⦄ → Free (Symbol ⊕ F) A → List Char → Free F A
parse (pure x)       []       = pure x
parse (pure _)       (x ∷ xs) = fail
parse (Symbolˢ c pf) []       = fail
parse (Symbolˢ c pf) (x ∷ xs) = if x == c then parse (pf tt) xs else fail
parse (Other s pf)   xs       = impure (s , flip parse xs ∘ pf)

module _ {F : Container} ⦃ _ : Symbol ⊂ F ⦄ where
  symbolᴾ : Char → Free F Char
  symbolᴾ c = inject (symbolˢ c , λ tt → pure c)

  digitᵖ : ⦃ Nondet ⊂ F ⦄ → Free F Char
  digitᵖ = foldr _⁇_ fail -- shortest solutions with the current std lib ...
    (Data.List.map symbolᴾ ('9' ∷ '8' ∷ '7' ∷ '6' ∷ '5' ∷ '4' ∷ '3' ∷ '2' ∷ '1' ∷ '0' ∷ []))

  -- TODO: `some` and `many`
  numberᴾ : ⦃ Nondet ⊂ F ⦄ → Free F ℕ
  numberᴾ = map (λ c → toℕ c ∸ toℕ '0') digitᵖ

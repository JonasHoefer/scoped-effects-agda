module Effect.Share where

open import Function      using (_$_; _∘_)

open import Data.Maybe    using (Maybe; nothing; just)
open import Data.Nat      using (ℕ; suc; _*_; _+_)
open import Data.Product  using (_,_)
open import Data.Sum      using (inj₁; inj₂)
open import Data.Unit     using (⊤; tt)

open import Container     using (Container; _▷_; _⊕_)
open import Free
open import Injectable    using (_⊂_; inject; project; upcast; Other)

open import Effect.Nondet using (Nondet; failˢ; choiceˢ; fail)
open import Effect.State  using (State; get; put)

data Shape : Set where
  BShareˢ : ℕ → Shape
  EShareˢ : ℕ → Shape

pattern BShare n pf = impure (inj₁ (BShareˢ n) , pf)
pattern EShare n pf = impure (inj₁ (EShareˢ n) , pf)

Share : Container
Share = Shape ▷ λ _ → ⊤

eshare : ∀ {F A i} → ⦃ Nondet ⊂ F ⦄ → ℕ → Free (Share ⊕ F) A {i} → Free F (Free (Share ⊕ F) A {i})
eshare _ (pure x)       = pure (pure x)
eshare _ (BShare n pf)  = eshare n (pf tt)
eshare _ (EShare n pf)  = pure (pf tt)
eshare n p@(Other s pf) with project {Nondet} p
... | just (failˢ     , pf′) = fail
... | just (choiceˢ _ , pf′) = inject (choiceˢ (just n) , pure ∘ pf′)
... | nothing                = impure (s , eshare n ∘ pf)

bshare : ∀ {F A i} → ⦃ Nondet ⊂ F ⦄ → Free (Share ⊕ F) A {i} → Free F A
bshare (pure x)      = pure x
bshare (BShare n pf) = eshare n (pf tt) >>= bshare
  where open RawMonad freeMonad
bshare (EShare n pf) = bshare (pf tt)
bshare (Other s pf)  = impure (s , bshare ∘ pf)

begin : {F : Container} → ⦃ Share ⊂ F ⦄ → ℕ → Free F ⊤
begin n = inject (BShareˢ n , λ _ → pure tt)

end : {F : Container} → ⦃ Share ⊂ F ⦄ → ℕ → Free F ⊤
end n = inject (EShareˢ n , λ _ → pure tt)

share : ∀ {F A} → ⦃ Share ⊂ F ⦄ → ⦃ State ℕ ⊂ F ⦄ → Free F A → Free F (Free F A)
share p = do i ← get ; put (i * 2) ; return $ (do begin i ; put (i * 2 + 1) ; x ← p ; put (i * 2) ; end i ; return x)
  where open RawMonad freeMonad

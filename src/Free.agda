module Free where

open import Data.Product using (_,_)
open import Function     using (_∘_)
open import Container    using (Container; ⟦_⟧)

data Free (C : Container) (A : Set) : Set where
  pure : A → Free C A
  impure : ⟦ C ⟧ (Free C A) → Free C A

infixl 1 _>>=_
_>>=_ : {A B : Set} {C : Container} → Free C A → (A → Free C B) → Free C B
pure x          >>= k = k x
impure (s , pf) >>= k = impure (s , λ p → pf p >>= k)

infixl 1 _>>_
_>>_ : {A B : Set} {C : Container} → Free C A → Free C B → Free C B
ma >> mb = ma >>= λ _ → mb

infixl 4 _<$>_
_<$>_ : {A B : Set} {C : Container} → (A → B) → Free C A → Free C B
f <$> (pure x)          = pure (f x)
f <$> (impure (s , pf)) = impure (s ,  (f <$>_) ∘ pf )

infixl 4 _<*>_
_<*>_ : {A B : Set} {C : Container} → Free C (A → B) → Free C A → Free C B
mf <*> ma = mf >>= λ f → ma >>= λ a → pure (f a)

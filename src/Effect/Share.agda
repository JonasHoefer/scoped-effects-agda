{-# OPTIONS --overlapping-instances #-}

module Effect.Share where

open import Function           using (_$_; _∘_; id; case_of_)

open import Data.Bool          using (Bool; false; true)
open import Data.List          using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_; toList)
open import Data.Maybe         using (Maybe; nothing; just)
open import Data.Nat           using (ℕ; suc; _*_; _+_)
open import Data.Product       using (_×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.Sum           using (inj₁; inj₂)
open import Data.Unit          using (⊤; tt)

open import Container          using (Container; _▷_; _⊕_)
open import Free
open import Injectable         using (_⊂_; inject; project; upcast; Other)

open import Effect.Nondet      using (Nondet; failˢ; choiceˢ; fail; solutions)
open import Effect.State       using (State; get; put; evalState)
open import Effect.Void        using (Void; run)

data Shape : Set where
  BShareˢ : ℕ × ℕ → Shape
  EShareˢ : ℕ × ℕ → Shape

pattern BShare n pf = impure (inj₁ (BShareˢ n) , pf)
pattern EShare n pf = impure (inj₁ (EShareˢ n) , pf)

Share : Container
Share = Shape ▷ λ _ → ⊤

----------------
-- Normalform --
----------------

record Normalform (T : Container) (A B : Set) : Set where
  field
    nf : Free T A → Free T B
open Normalform ⦃...⦄ public

instance
  ℕ-normalform : ∀ {N} → Normalform N ℕ ℕ
  Normalform.nf ℕ-normalform = id

  bool-normalform : ∀ {N} → Normalform N Bool Bool
  Normalform.nf bool-normalform = id

---------------
-- Shareable --
---------------

record Shareable (M : Container) (A : Set) : Set₁ where
  field
    shareArgs : A → Free M A
open Shareable ⦃...⦄ public

instance
  ℕ-shareable : ∀ {M} → ⦃ Share ⊂ M ⦄ → ⦃ State (ℕ × ℕ) ⊂ M ⦄ → Shareable M ℕ
  Shareable.shareArgs ℕ-shareable = pure

  bool-shareable : ∀ {M} → ⦃ Share ⊂ M ⦄ → ⦃ State (ℕ × ℕ) ⊂ M ⦄ → Shareable M Bool
  Shareable.shareArgs bool-shareable = pure

-------------
-- Handler --
-------------

nameChoices : ∀ {F A i} → ⦃ Nondet ⊂ F ⦄ → List⁺ ((ℕ × ℕ) × ℕ) → Free (Share ⊕ F) A {i} → Free F A
runShare : ∀ {F A i} → ⦃ Nondet ⊂ F ⦄ → Free (Share ⊕ F) A {i} → Free F A

nameChoices scopes@((sid , next) ∷ scps) (pure x)       = pure x
nameChoices scopes@((sid , next) ∷ scps) (BShare n pf)  = nameChoices ((sid , 0) ∷ toList scopes) (pf tt)
nameChoices scopes@((sid , next) ∷ scps) (EShare n pf)  = case scps of λ { [] → runShare (pf tt) ; (s ∷ ss) → nameChoices (s ∷ ss) (pf tt) }
nameChoices scopes@((sid , next) ∷ scps) p@(Other s pf) with project {Nondet} p
... | just (failˢ     , pf′) = fail
... | just (choiceˢ _ , pf′) = inject $ choiceˢ (just (sid , next)) , λ where
  false → nameChoices ((sid , (suc next)) ∷ scps) (pf′ false)
  true  → nameChoices ((sid , (suc next)) ∷ scps) (pf′ true)
... | nothing = impure (s , nameChoices scopes ∘ pf)

runShare (pure x)        = pure x
runShare (BShare sid pf) = nameChoices ((sid , 0) ∷ []) (pf tt)
runShare (EShare _   pf) = runShare (pf tt)
runShare (Other s pf)    = impure (s , runShare ∘ pf)

--------------------
-- Share Operator --
--------------------

begin : {F : Container} → ⦃ Share ⊂ F ⦄ → ℕ × ℕ → Free F ⊤
begin n = inject (BShareˢ n , λ _ → pure tt)

end : {F : Container} → ⦃ Share ⊂ F ⦄ → ℕ × ℕ → Free F ⊤
end n = inject (EShareˢ n , λ _ → pure tt)

share : ∀ {F A} → ⦃ Shareable F A ⦄ → ⦃ Share ⊂ F ⦄ → ⦃ State (ℕ × ℕ) ⊂ F ⦄ → Free F A → Free F (Free F A)
share p = do
      (i , j) ← get
      put (i + 1 , j)
      return $ do
        begin (i , j)
        put (i , j + 1)
        x ← p
        x′ ← shareArgs x
        put (i + 1 , j)
        end (i , j)
        return x′
  where open RawMonad freeMonad

------------------------------
-- Call Time Choice Utility --
------------------------------

runCTC : ∀ {A B}
  → ⦃ Shareable (State (ℕ × ℕ) ⊕ Share ⊕ Nondet ⊕ Void) A ⦄
  → ⦃ Normalform (State (ℕ × ℕ) ⊕ Share ⊕ Nondet ⊕ Void) A B ⦄
  → Free (State (ℕ × ℕ) ⊕ Share ⊕ Nondet ⊕ Void) A → List B
runCTC = run ∘ solutions ∘ runShare ∘ evalState (0 , 0) ∘ nf

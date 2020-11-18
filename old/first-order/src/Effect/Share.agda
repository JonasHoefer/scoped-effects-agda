{-# OPTIONS --overlapping-instances #-}

module Effect.Share where

open import Function           using (_$_; _∘_; id; case_of_)

open import Category.Monad     using (RawMonad)
open        RawMonad ⦃...⦄     using (_>>=_; _>>_; return)

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
open import Free.Instances

open import Effect.Nondet      using (Nondet; failˢ; choiceˢ; fail; solutions)
open import Effect.State       using (State; get; put; evalState)

open import Tactic.Assumption

----------------------------------------------------
-- Sharing of Nondeterminism following Bunkenburg --
----------------------------------------------------

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

record Normalform (T : List Container) (A B : Set) : Set where
  field
    nf : A → Free T B
open Normalform ⦃...⦄ public

instance
  ℕ-normalform : ∀ {N} → Normalform N ℕ ℕ
  Normalform.nf ℕ-normalform = pure

  bool-normalform : ∀ {N} → Normalform N Bool Bool
  Normalform.nf bool-normalform = pure

---------------
-- Shareable --
---------------

record Shareable (M : List Container) (A : Set) : Set₁ where
  field
    shareArgs : A → Free M A
open Shareable ⦃...⦄ public

instance
  ℕ-shareable : ∀ {M} → {@(tactic eff) _ : Share ∈ M} → {@(tactic eff) _ : State (ℕ × ℕ) ∈ M} → Shareable M ℕ
  Shareable.shareArgs ℕ-shareable = pure

  bool-shareable : ∀ {M} → {@(tactic eff) _ : Share ∈ M} → {@(tactic eff) _ : State (ℕ × ℕ) ∈ M} → Shareable M Bool
  Shareable.shareArgs bool-shareable = pure

-------------
-- Handler --
-------------

nameChoices : ∀ {F A i} → {@(tactic eff) _ : Nondet ∈ F} → List⁺ ((ℕ × ℕ) × ℕ) → Free (Share ∷ F) A {i} → Free F A
runShare : ∀ {F A i} → {@(tactic eff) _ : Nondet ∈ F} → Free (Share ∷ F) A {i} → Free F A

nameChoices scopes@((sid , next) ∷ scps) (pure x)       = pure x
nameChoices scopes@((sid , next) ∷ scps) (BShare n pf)  = nameChoices ((sid , 0) ∷ toList scopes) (pf tt)
nameChoices scopes@((sid , next) ∷ scps) (EShare n pf)  = case scps of λ { [] → runShare (pf tt) ; (s ∷ ss) → nameChoices (s ∷ ss) (pf tt) }
nameChoices scopes@((sid , next) ∷ scps) p@(Other s pf) with prj {Nondet} {p = there assumption} p
... | just (failˢ     , _) = fail
... | just (choiceˢ _ , κ) = op $ choiceˢ (just (sid , next)) , λ where
  false → nameChoices ((sid , (suc next)) ∷ scps) (κ false)
  true  → nameChoices ((sid , (suc next)) ∷ scps) (κ true)
... | nothing = impure (s , nameChoices scopes ∘ pf)

runShare (pure x)        = pure x
runShare (BShare sid pf) = nameChoices ((sid , 0) ∷ []) (pf tt)
runShare (EShare _   pf) = runShare (pf tt)
runShare (Other s pf)    = impure (s , runShare ∘ pf)

--------------------
-- Share Operator --
--------------------

begin : ∀ {F} → {@(tactic eff) _ : Share ∈ F} → ℕ × ℕ → Free F ⊤
begin n = op (BShareˢ n , λ _ → pure tt)

end : ∀ {F} → {@(tactic eff) _ : Share ∈ F} → ℕ × ℕ → Free F ⊤
end n = op (EShareˢ n , λ _ → pure tt)

share : ∀ {F A} → ⦃ Shareable F A ⦄ → {@(tactic eff) _ : Share ∈ F} → {@(tactic eff) _ : State (ℕ × ℕ) ∈ F} → Free F A → Free F (Free F A)
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

------------------------------
-- Call Time Choice Utility --
------------------------------

runCTC : ∀ {A B}
  → ⦃ Shareable (State (ℕ × ℕ) ∷ Share ∷ Nondet ∷ []) A ⦄
  → ⦃ Normalform (State (ℕ × ℕ) ∷ Share ∷ Nondet ∷ []) A B ⦄
  → Free (State (ℕ × ℕ) ∷ Share ∷ Nondet ∷ []) A → List B
runCTC prog = run $ solutions $ runShare $ evalState (0 , 0) (prog >>= nf)

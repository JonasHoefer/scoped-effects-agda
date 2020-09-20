module Effect.Nondet where

open import Function using (id; _∘_; const; _$_)

open import Category.Monad using (RawMonad)
open        RawMonad ⦃...⦄ renaming (_⊛_ to _<*>_)

open import Data.Bool  using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Tree

open import Variables
open import Effect
open import Prog
open import Prog.Instances


data Nondetˢ : Set where
  failˢ : Nondetˢ
  choiceˢ : Maybe CID → Nondetˢ

Nondet : Effect
Ops  Nondet = Nondetˢ ▷ λ{ failˢ → ⊥ ; (choiceˢ x) → Bool }
Scps Nondet = Void

pattern Fail = (inj₁ failˢ , _)
pattern Choice cid κ = (inj₁ (choiceˢ cid) , κ)

hdl : ∀ {A} → Tree (Prog effs (Tree A)) → Prog effs (Tree A)
hdl (leaf x)         = x
hdl failed           = var failed
hdl (choice cid l r) = choice cid <$> hdl l <*> hdl r

runNondet′ : Prog (Nondet ∷ effs) A → Prog effs (Tree A)
runNondet′ {effs} {A} = foldP (λ i → (Prog effs ∘ Tree) ^ i $ A) 1 id
  (var ∘ leaf)
  (λ where
    Fail           → var failed
    (Choice cid κ) → choice cid <$> κ true <*> κ false
    (Other s κ)    → op (s , κ)
  ) λ where
    (Other s κ)    → scp (s , (hdl <$>_) ∘ κ)

runNondet : Prog (Nondet ∷ effs) A → Prog effs (List A)
runNondet p = dfs empty <$> runNondet′ p

fail : ⦃ Nondet ∈ effs ⦄ → Prog effs A
fail = Op (failˢ , λ())

infixl 0 _⁇_ _⁇⟨_⟩_
_⁇_ : ⦃ Nondet ∈ effs ⦄ → Prog effs A → Prog effs A → Prog effs A
p ⁇ q = Op (choiceˢ nothing , (if_then p else q))

_⁇⟨_⟩_ : ⦃ Nondet ∈ effs ⦄ → Prog effs A → CID → Prog effs A → Prog effs A
p ⁇⟨ cid ⟩ q = Op ((choiceˢ (just cid)) , (if_then p else q))


module Tactic.FindIndex where

open import Function using (_$_)

open import Reflection
open import Reflection.Argument                     using (vArg; _⟨∷⟩_; _⟅∷⟆_)
open import Reflection.Term                         using (_⋯⟨∷⟩_; _⋯⟅∷⟆_)
open import Reflection.TypeChecking.Monad.Instances

open import Category.Monad                          using (RawMonad; RawMonadPlus)
open RawMonad ⦃...⦄                                 using (pure; _⊗_)
open RawMonadPlus ⦃...⦄                             using (_∣_)

open import Data.Bool                               using (Bool; true; false)
open import Data.List                               using (List; _∷_; []; map; intersperse; foldr)
open import Data.List.Relation.Unary.Any            using (Any; here; there)                       public
open import Data.Unit                               using (⊤; tt)

open import Relation.Binary.PropositionalEquality   using (_≡_; refl)
open import Tactic.Reflection.Meta

infix 3 _∈_
_∈_ : ∀ {a} {A : Set a} → A → List A → Set a
x ∈ xs = Any (_≡_ x) xs

pattern _`∷_ x xs = con (quote _∷_) (_ ∷ _ ∷ x ⟨∷⟩ xs ⟨∷⟩ [])

indices′ : Term → Term → List Term
indices′ (_ `∷ xs) t = t ∷ indices′ xs (con (quote Any.there) (t ⟨∷⟩ []))
indices′ _         _ = []

indices : Term → List Term
indices xs = indices′ xs (con (quote Any.here) $ (con (quote refl) []) ⟨∷⟩ [])

inferNormalisedType : Term → TC Type
inferNormalisedType t = withNormalisation true (inferType t)

choice : {A : Set} → List (TC A) → TC A
choice = foldr (_∣_) (typeError [])

nometaSpine : Term → TC ⊤
nometaSpine (_ `∷ xs) = nometaSpine xs
nometaSpine (con _ _) = pure _
nometaSpine (var _ _) = pure _
nometaSpine x         = ensureNoMetas x

tac-find-index : Term → TC ⊤
tac-find-index ?hole = do
  def (quote Any)
    ( _ ∷ _ ∷ _
    ∷ vArg (def (quote _≡_) (_ ∷ _ ∷ vArg `x ∷ []))
    ∷ vArg `xs ∷ []) ← inferNormalisedType ?hole
     where g → do
             ensureNoMetas g
             typeError $ termErr g ∷ strErr "!= _ ∈ _" ∷ []
  nometaSpine `xs
  choice (map (unify ?hole) (indices `xs)) ∣ withNormalisation true do
    typeError $ termErr `x ∷ strErr "not found in" ∷ termErr `xs ∷ []

macro find-index = tac-find-index

test : 3 ∈ (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
test = find-index

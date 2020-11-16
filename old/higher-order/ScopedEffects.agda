-- | Sketch of scoped effects as higher order functors based on "Effect Handlers in Scope" by Wu et al. in Agda.

{-# OPTIONS --cumulativity #-}

module ScopedEffects where

open import Level        using (0ℓ; suc)

open import Data.Bool    using (Bool; true; false; if_then_else_)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing; fromMaybe)

-- # Problem
--
-- With this approach it seems impossible to model effectful data structures such as Listᴹ (see below).


-- # General ideas and questions
--
-- 1. The implementation does not recognize that the monadic list stored in Free Op contains Free Op layers.
--    (not arbitrary Set₁ elements - just Set₀ elements with the same type constructor interleaved).
--    Is it possible to describe this interleaved structure for generic data types as a constructor of Free?
-- 2. Universe polymorphic Free + increase level as needed. This seems extremely complicated and not feasible 
--    for large programs.

module MinimalExample where
  -- Stores result type X : Set₀ of intermediate computation => intermediate computation cannot produce Listᴹ : Set₁
  --           ↓ 
  data Free (Shape : Set₁) (Pos : Shape → Set) (Ctx : (s : Shape) → Pos s → Maybe Set₁) (A : Set₁) : Set₁ where
    pure   : A → Free Shape Pos Ctx A
    impure : (s : Shape) → (p : Pos s) → Free Shape Pos Ctx (fromMaybe A (Ctx s p)) → Free Shape Pos Ctx A

  -- Element of Set₁ because Free [...] : Set₁ because Shape : Set₁ because the type of the subcomputation 
  -- needs to be stored somewhere.
  --    ↓ 
  data Listᴹ (Shape : Set₁) (Pos : Shape → Set) (Ctx : (s : Shape) → Pos s → Maybe Set₁) (A : Set₁) : Set₁ where
    nil  : Listᴹ Shape Pos Ctx A
    cons : Free Shape Pos Ctx A → Free Shape Pos Ctx (Listᴹ Shape Pos Ctx A) → Listᴹ Shape Pos Ctx A

module LargerExample where
  -- (modified) indexed container as representation for higher order functor i.e. a scoped effect.
  record Container : Set₂ where
    constructor _◁_/_
    field
      Shape : Set₁
      Pos : Shape → Set
      -- Usually (s : Shape) → Pos s → Set → Set, but
      -- - returned type constructor has to be strictly positive (for definition of Listᴹ)
      -- - the functor is always Id or Const for some type stored in the shape
      -- - returning a first order container as strictly positive representation of Set → Set is possible but 
      --   complicates things later
      -- => Maybe is the simplest solution for this example
      -- returns type stored in the shape (via lift or cumulativity)
      Ctx : (s : Shape) → Pos s → Maybe {suc (suc 0ℓ)} Set₁
  open Container public

  ⟦_⟧ : Container → (Set₁ → Set₁) → Set₁ → Set₁
  ⟦ S ◁ P / C ⟧ F A = Σ[ s ∈ S ] ((p : P s) → F (fromMaybe {suc (suc 0ℓ)} A (C s p)))

  data Free (C : Container) (A : Set₁) : Set₁ where
    pure   : A                → Free C A
    impure : ⟦ C ⟧ (Free C) A → Free C A

  -- I want to be able to store data types with interleaved Free layers in the free monad
  -- (i.e. effectful data types).
  -- but ℓ-Free = ℓ-Shape > ℓ-captured and ℓ-Listᴹ = ℓ-Free => I cannot use such
  -- data structures in scoped effects (those producing another type in Ctx).
  data Listᴹ (C : Container) (A : Set₁) : Set₁ where
    nil : Listᴹ C A
    cons : Free C A → Free C (Listᴹ C A) → Listᴹ C A

  ---------------------
  -- A scoped effect --
  ---------------------

  data OpShape : Set₁ where opˢ : (X : Set) → OpShape

  OpPos : OpShape → Set
  OpPos (opˢ X) = ⊤ ⊎ X -- the scoped operation stores a computation which produces its
                        -- argument of type X and a computation which transforms X to A

  OpCtx : (s : OpShape) → OpPos s → Maybe Set₁
  OpCtx (opˢ X) (inj₁ tt) = just X  -- captured subcomputation is of type Free C X
  OpCtx (opˢ X) (inj₂ x)  = nothing -- continuation is of type Free C A

  Op : Container
  Op = OpShape ◁ OpPos / OpCtx

  -- Generic operation for Opˢ.
  --         ↓ Can only capture computation with value form Set₀
  op : {A : Set₀} → Free Op A → Free Op A
  op {A} ma = impure (opˢ A , λ{ (inj₁ tt) → ma ; (inj₂ x) → pure x })

  foo bar : Free Op (Listᴹ Op Bool)
  foo = pure nil
  bar = {! op foo !} -- as expected this does not work
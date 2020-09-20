module Variables where

open import Size      using (Size)

open import Data.List using (List)
open import Effect    using (Effect)

variable
  A B C : Set
  E : Effect
  effs : List Effect
  i : Size

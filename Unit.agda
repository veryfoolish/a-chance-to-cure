module Unit where

open import Level using (Level) renaming (zero to lzero)
open import Equality
open import Contractible
open import Sigma

data Unit : Set lzero where
  ✫ : Unit

-- some theorems

Unit-Is-Contractible : Contractible Unit
Unit-Is-Contractible = ( ✫ , helper ) where
                         helper : (x : Unit) → ✫ ≡ x
                         helper ✫ = refl

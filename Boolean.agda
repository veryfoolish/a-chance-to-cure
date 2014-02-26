module Boolean where

open import Level using (Level) renaming (zero to lzero)

data Boolean : Set lzero where
  ⊤ ⊥ : Boolean
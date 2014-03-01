module Binary where

open import Level using (Level) renaming (zero to ∘)
open import List
open import Boolean renaming (⊤ to #1; ⊥ to #0)
open import Natural

data Binary : Set ∘ where
  ##0 : Binary
  _+#1 : List Boolean → Binary

testit = [ #0 ] +#1

inc : List Boolean → List Boolean
inc [] = [ #0 ]
inc (x ∷ xs) with x
... | #0 = #1 ∷ xs
... | #1 = #0 ∷ (inc xs)

bsuc : Binary → Binary
bsuc ##0 = [] +#1
bsuc (x +#1) = (inc x) +#1

ToList : Binary → List Boolean
ToList ##0 = [ #0 ]
ToList (x +#1) = x ++ [ #1 ]

2-power : List Boolean → List ℕ
2-power [] = []
2-power (x ∷ xs) with x
... | #0 = 2-power xs
... | #1 = (exp 2 (length xs)) ∷ (2-power xs)

To-2-power : Binary → List ℕ
To-2-power x = 2-power (reverse (ToList x))

sum : List ℕ → ℕ
sum [] = 0
sum (x ∷ xs) = x + sum xs

To-ℕ : Binary → ℕ
To-ℕ x = sum (To-2-power x)

From-ℕ : ℕ → Binary
From-ℕ 0 = ##0
From-ℕ (S n) = bsuc (From-ℕ n)
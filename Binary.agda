module Binary where

open import Level using (Level) renaming (zero to l0)
open import List
open import Boolean
open import Natural
open import Cartesian
open import Sigma

data OneList : Set l0 where
  Zero : OneList
  FromList : List Boolean → OneList


ToList : OneList → List Boolean
ToList Zero = [ ⊥ ]
ToList (FromList a) = [ ⊤ ] ++ a

--- examples

One : OneList
One = FromList []

all-⊤ : List Boolean → Boolean
all-⊤ [] = ⊤
all-⊤ (x ∷ a) = x ∧ (all-⊤ a)

testit = all-⊤ (⊤ ∷ [ ⊤ ])

-- Next : OneList → OneList
-- Next Zero = FromList []
-- Next (FromList a) with ∀-⊤ a


ZeroList : ℕ → List Boolean
ZeroList 0 = []
ZeroList (S n)  = ⊥ ∷ (ZeroList n)

--- a peculiar increment function for my binary numbers
--- won't be generally useful
--- Increment : List Boolean → List Boolean
--- Increment [] = []
--- Increment x ∷ xs with 

Half-Adder : Boolean → Boolean → Boolean × Boolean
Half-Adder a b = (a ∧ b) , (a ⊕ b)

Full-Adder : Boolean → Boolean → Boolean → Boolean × Boolean
Full-Adder a b c = (((a ⊕ b) ⊕ c)) , ((a ∧ b) ⊹ (c ∧ (a ⊕ b)))


inc : List Boolean → List Boolean
inc [] = []
inc (x ∷ xs) with x
... | ⊤ = ⊥ ∷ (inc xs)
... | ⊥ = ⊤ ∷ xs

Inc : List Boolean → List Boolean
Inc x = reverse (inc (reverse x))

ALL-⊤ : OneList → Boolean
ALL-⊤ x = all-⊤ (ToList x)

Next : OneList → OneList
Next Zero = One
Next (FromList x) with (ALL-⊤ (FromList x))
... | ⊤ = (FromList (ZeroList (length x)))
... | ⊥ = FromList (Inc (ToList (FromList x)))

iinc : List Boolean → List Boolean
iinc x = reverse (inc (reverse x))

Increment : List Boolean → List Boolean
Increment [] = []
Increment x with (all-⊤ x)
... | ⊤ = ⊤ ∷ ZeroList (length (iinc x))
... | ⊥ = iinc x


From-ℕ : ℕ → List Boolean
From-ℕ 0 = [ ⊥ ]
From-ℕ (S n) = Increment (From-ℕ n)


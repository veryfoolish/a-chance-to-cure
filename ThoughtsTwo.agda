module ThoughtsTwo where

open import Level using (Level) renaming (zero to lzero; suc to lsuc)
open import Natural
open import List
open import Sigma
open import Coproduct
open import Equality
open import Cartesian

data ArithmeticError : Set lzero where
  Overflow : ArithmeticError

NonEmpty = (a : List ℕ) → (length a > 0)

data Empty? : Set lzero where
  isEmpty : (a : List ℕ) → (length a ≡ 0) → Empty?


theorem-empty : (j : List ℕ) → (j ≡ []) → Empty?
theorem-empty [] refl = isEmpty [] refl

data DecimalDigit? (n : ℕ) :  Set (lsuc lzero) where
  isDec : (n ≤ 9) → DecimalDigit? n


≤th : {n : ℕ} → (n ≤ S n)
≤th {0} = 0≤n
≤th {(S n)} = +1≤ (≤th)

≤ok : (n : ℕ) → (n ≤ n)
≤ok 0 = 0≤n
≤ok (S n) = +1≤ (≤ok n)

≤trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
≤trans 0≤n _ = 0≤n
≤trans (+1≤ p) (+1≤ q) = +1≤ (≤trans p q)

theorem-w : {a b : ℕ} → a ≤ b → a ≤ (S b)
theorem-w p = ≤trans p ≤th

--- this is actually, if b ≤ c and a ≤ b then a ≤ c 
theorem-q : {a b : ℕ} → S a ≤ b → a ≤ b
theorem-q p = ≤trans ≤th p

--- better ;-)
theorem-t⋆ : {n : ℕ} → (S n ≤ 9) → (n ≤ 9)
theorem-t⋆ p = (theorem-q p)


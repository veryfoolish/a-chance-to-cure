open import Product
open import Natural
open import Agda.Primitive
module ProductSpace where

Π : {ℓ : Level} → (A : Set ℓ) → Set ℓ
Π A = A × A

data unit {ℓ : Level} : Set ℓ where
  ✹ : unit

_^_ : {ℓ : Level} → (A : Set ℓ) → (n : ℕ) → Set ℓ
A ^ 0 = unit 
A ^ (S n) = A × (A ^ n)

open import Sigma


t : (n : ℕ) → ℕ ^ n
t O = ✹
t (S n) = n , t n


q = t 5

form : (ℕ → ℕ) → (n : ℕ) → ℕ ^ n → ℕ ^ n
form f O _ = ✹
form f (S n) (x , y) = f x , form f n y

F = form S 5

Z = F q
ZZ = F Z

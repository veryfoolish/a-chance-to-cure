module List where

open import Level
open import Natural

infixr 5 _∷_ _++_

data List {ℓ} (A : Set ℓ) : Set ℓ where
  [] : List A
  _∷_ : (x : A) (xs : List A) → List A

[_] : {ℓ : Level} {A : Set ℓ} → A → List A
[ x ] = x ∷ []

_++_ : {ℓ : Level} {A : Set ℓ} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : {ℓ : Level} {A : Set ℓ} → List A → ℕ
length [] = 0
length (x ∷ xs) = S (length xs)

foldr : {i j : Level} {A : Set i} {B : Set j} → (A → B → B) → B → List A → B
foldr c n [] = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : {i j : Level} {A : Set i} {B : Set j} → (A → B → A) → A → List B → A
foldl c n [] = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

reverse : {ℓ : Level} {A : Set ℓ} → List A → List A
reverse = foldl (λ rev x → x ∷ rev) []
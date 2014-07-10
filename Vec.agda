module Vec where

open import Natural

infixr 5 _∷_

data Vec {a} (A : Set a) : ℕ → Set a where
  [] : Vec A 0
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (S n)

infixr 4 _∈_

data _∈_ {a} {A : Set a} : A → {n : ℕ} → Vec A n → Set a where
  here : ∀ {n} {x} {xs : Vec A n} → x ∈ x ∷ xs
  there : ∀ {n} {x y} {xs : Vec A n} (x∈xs : x ∈ xs) → x ∈ y ∷ xs

head : ∀ {a n} {A : Set a} → Vec A (1 + n) → A
head (x ∷ xs) = x

tail : ∀ {a n} {A : Set a} → Vec A (1 + n) → Vec A n
tail (x ∷ xs) = xs
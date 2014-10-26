{-# OPTIONS --without-K #-}

open import Natural
open import Identity
open import Boolean

module Integer where

data ℤ : Set where
  O : ℤ
  pos : (n : ℕ) → ℤ
  neg : (n : ℕ) → ℤ

succ : ℤ → ℤ
succ O = pos 0
succ (pos n) = pos (S n)
succ (neg O) = O
succ (neg (S n)) = neg n

pred : ℤ → ℤ
pred O = neg O
pred (pos O) = O
pred (pos (S n)) = pos n
pred (neg n) = neg (S n)

abstract
  succ-pred : (n : ℤ) → succ (pred n) ≡ n
  succ-pred O = refl
  succ-pred (pos O) = refl
  succ-pred (pos (S n)) = refl
  succ-pred (neg n) = refl

ℤ~ : ℤ → ℤ
ℤ~ O = O
ℤ~ (pos n) = neg n
ℤ~ (neg n) = (pos n)

_ℤ+_ : ℤ → ℤ → ℤ
O ℤ+ b = b
pos O ℤ+ b = succ b
pos (S n) ℤ+ b = succ (pos n ℤ+ b)
neg O ℤ+ b = pred b
neg (S n) ℤ+ b = pred (neg n ℤ+ b)

ℤ≥0? : ℤ → Boolean
ℤ≥0? O = true
ℤ≥0? (pos n) = true
ℤ≥0? (neg n) = false

ℤ<0? : ℤ → Boolean
ℤ<0? a = Not (ℤ≥0? a)

ℤ+-unit-l : ∀ z → O ℤ+ z ≡ z
ℤ+-unit-l _ = refl


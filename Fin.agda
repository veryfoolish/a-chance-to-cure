{-# OPTIONS --without-K #-}
module Fin where

open import Agda.Primitive
open import Natural

data Fin : ℕ → Set lzero where
  fzero : {n : ℕ} → Fin (S n)
  fsuc : {n : ℕ} → Fin n → Fin (S n)

fromℕ≤ : ∀ {m n} → m < n → Fin n
fromℕ≤ (+1≤ 0≤n) = fzero
fromℕ≤ (+1≤ (+1≤ m≤n)) = fsuc (fromℕ≤ (+1≤ m≤n))

toℕ : ∀ {n : ℕ} → Fin n → ℕ
toℕ fzero = 0
toℕ (fsuc j) = S (toℕ j)

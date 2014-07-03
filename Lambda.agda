module Lambda where

open import Natural
open import Coproduct

{-- reading http://arxiv.org/pdf/cs/0702152v1.pdf --}
mutual
  data Term : Set where
    Index : ℕ → Term
    Pair : Term → Term → Term
    Abstraction : Term → Term
    ⟦_,_,_,_⟧ : Term → ℕ → ℕ → Environment → Term

  data Entry : Set where
    ⟨_,_⟩ : Term → ℕ → Entry

  data Environment : Set where
    Nil : Environment
    _∷_ : Entry → Environment → Environment
    ⟪_,_,_,_⟫ : Environment → ℕ → ℕ → Environment → Environment


toℕ : Entry → ℕ
toℕ ⟨ t , l ⟩ = l

len : Environment → ℕ
len Nil = 0
len (x ∷ e) = len e + 1
len ⟪ e₁ , nl₁ , ol₂ , e₂ ⟫ = len e₁ + (len e₂ ∸ nl₁)

lev : Environment → ℕ
lev Nil = 0
lev (⟨ t , l ⟩ ∷ e) = l
lev ⟪ e₁ , nl , ol , e₂ ⟫ = lev e₂ + (nl ∸ ol)

  
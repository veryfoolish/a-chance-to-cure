open import Natural
open import Boolean
open import Empty
open import Equality
open import Product
open import Coproduct
open import Sigma

module Evaluation where

Domain = Boolean ∨ ℕ

eq?ℕ : ℕ → ℕ → Boolean
eq?ℕ O O = true
eq?ℕ O (S b) = false
eq?ℕ (S a) O = false
eq?ℕ (S a) (S b) = eq?ℕ a b

cond : (x y : Domain) → Domain
cond (inl false) (inl false) = inl true
cond (inl false) (inl true) = inl true
cond (inl true) p = p
cond (inl x) (inr x₁) = inl false
cond (inr x) (inl x₁) = inl false
cond (inr x) (inr x₁) = inl (eq?ℕ x x₁)

neg : (x : Domain) → Domain
neg x = cond x (inl false)


conj : (a b : Domain) → Domain
conj a b = neg (cond a (neg b))

id∙ : (a b : Domain) → Domain
id∙ a b = conj (cond a b) (cond b a)

open import Level
theorem : (a : ℕ) → (id∙ (inr a) (inr a)) ≡ inl true
theorem O = refl
theorem (S a) = theorem a

t′ : (a b : ℕ) → (S a ≡ S b) → a ≡ b
t′ O O p = refl
t′ O (S b) ()
t′ (S a) O ()
t′ (S a) (S .a) refl = refl


thm : (a b : ℕ) → (a ≡ b) → id∙ (inr a) (inr a) ≡ (inl true)
thm O O p = refl
thm O (S b) p = refl
thm (S a) b p = thm a a refl 

--- another way to do this is 

⟪t,f⟫∙∈_ : {ℓ : Level} (A : Set ℓ) → Set ℓ
⟪t,f⟫∙∈ A = Boolean → A

th : ⟪t,f⟫∙∈ ℕ 
th false = O
th true = 1




open import Natural
open import List
open import Level renaming (zero to lzero)
open import Boolean
module Lambda where


data Var : Set lzero where
  ∙var : ℕ → Var

data Lambda : Set lzero where
  V : Var → Lambda
  Λ : Var → Lambda → Lambda
  ⟨_,_⟩ : Lambda → Lambda → Lambda

x = ∙var 5
y = ∙var 6
t = ⟨ V x , V y ⟩
ab  = Λ x t

eqℕ? : ℕ → ℕ → Boolean
eqℕ? O O = true
eqℕ? O (S b) = false
eqℕ? (S a) (S b) = eqℕ? a b
eqℕ? (S a) O = false

eq? : Var → Var → Boolean
eq? (∙var x) (∙var y) = eqℕ? x y

case : {ℓ : Level} → {A : Set ℓ} → A → A → Boolean → A
case x y true = x
case x y false = y

accessory : Var → Var → List Var
accessory x y = case{A = List Var} [] [ y ] (eq? x y)

Free : Lambda → List Var
Free (V x) = [ x ]
Free (Λ x (V y )) = case [] [ y ] (eq? x y)
Free (Λ x (Λ x₁ b)) = Free b
Free (Λ x ⟨ b , b₁ ⟩) = {!!}
Free ⟨ x , x₁ ⟩ = Free x ++ Free x₁

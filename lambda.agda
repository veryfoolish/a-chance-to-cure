open import Natural
open import List
open import Level renaming (zero to lzero)
open import Boolean
module Lambda where


data Var : Set lzero where
  ∙var : ℕ → Var

data Lambda : Set lzero where
  var : Var → Lambda
  Λ : Lambda → Lambda → Lambda
  ⟨_,_⟩ : Lambda → Lambda → Lambda

x = var (∙var 5)
y = var (∙var 6)
t = ⟨ x , y ⟩
ab  = Λ x t

eqℕ? : ℕ → ℕ → Boolean
eqℕ? O O = true
eqℕ? O (S b) = false
eqℕ? (S a) (S b) = eqℕ? a b
eqℕ? (S a) O = false

eq? : Var → Var → Boolean
eq? (∙var x) (∙var y) = eqℕ? x y

Free : Lambda → List Var
Free (var x) = [ x ]
Free (Λ l l₁) = Free l₁
Free ⟨ l , l₁ ⟩ = Free l ++ Free l₁



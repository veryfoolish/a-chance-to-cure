module Maps where

open import Level
open import Equality
open import Sigma 

data _~_ {ℓ} {A B : Set ℓ} (f g : A → B) : Set ℓ where
  feq : {a : A}  → f a ≡ g a → f ~ g


_∘_ : {ℓ : Level} → {A B C : Set ℓ} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → (g (f x))

data monomorphism {ℓ : Level} {A B C : Set ℓ} (e : A → B) {g f : C → A} {p : (e ∘ g) ~ (e ∘ f)} :  Set ℓ where
  monic : (g ~ f) → monomorphism e

open import Natural
open import Product
data Weird : ℕ → Set where
  ok : Weird O
  hm : Weird 1
  oh : Weird 2
  uh : {n : ℕ} → (Weird n) → (Weird (S n)) → Weird (S (S n)) → Weird (S (S (S n)))


hi : Weird 6
hi = uh (uh ok hm oh) (uh hm oh (uh ok hm oh))
       (uh oh (uh ok hm oh) (uh hm oh (uh ok hm oh)))

thmthm : (n : ℕ) → Weird n → Weird (S n)
thmthm O x = hm
thmthm (S .0) hm = oh
thmthm (S .1) oh = uh ok hm oh
thmthm (S ._) (uh x x₁ x₂) = uh x₁ x₂ (thmthm (S (S _)) x₂)



==thmthm : (n : ℕ) → (Weird n)
==thmthm 0 = ok
==thmthm (S n) = thmthm n (==thmthm n)

t = ==thmthm 15

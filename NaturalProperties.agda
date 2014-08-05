module NaturalProperties where

open import Natural
open import Equality
open import EquationalReasoning
open import Unit
open import Level
open import Empty 
+0-left-id : {a : ℕ} → 0 + a ≡ a
+0-left-id = refl

+0-right-id : {a : ℕ} → a + 0 ≡ a
+0-right-id {0} = refl
+0-right-id {S n} = ap S +0-right-id

+comm-zero-id₁ : {a : ℕ} → a + 0 ≡ 0 + a
+comm-zero-id₁ = +0-right-id □ +0-left-id

+comm-zero-id₂ : {a : ℕ} → 0 + a ≡ a + 0
+comm-zero-id₂ = ⇕ +0-left-id +0-right-id

m+1+n≡1+m+n : (m n : ℕ) → m + S n ≡ S (m + n)
m+1+n≡1+m+n 0 n = refl
m+1+n≡1+m+n (S m) n = ap S (m+1+n≡1+m+n m n)

+-comm : (a b : ℕ) → a + b ≡ b + a
+-comm 0     n = +comm-zero-id₂
+-comm (S m) n = 
            S m + n ≡⟨ refl ⟩
            S m + n ≡⟨ ap S (+-comm m n) ⟩
            S n + m ≡⟨ flip (m+1+n≡1+m+n n m) ⟩
            n + S m
            ∎


+-assoc : (a b c : ℕ) → ((a + b) + c) ≡ (a + (b + c))
+-assoc O b c = refl
+-assoc (S a) b c = ap S (+-assoc a b c )

code : ℕ → ℕ → Set zero
code O O = Unit
code (S a) 0 = ⊥
code 0 (S b) = ⊥
code (S m) (S n) = code m n

r : (n : ℕ) → code n n
r 0 = ✫
r (S n) = r n

transport : {ℓ : Level} {A : Set ℓ}{x y : A} → (x ≡ y) → (P : A → Set ℓ) → (P x → P y)
transport refl P x = x

encode : (m n : ℕ) → (m ≡ n) → code m n
encode m n p = transport p (λ x → code m x) (r m)

decode : (m n : ℕ) → code m n → (m ≡ n)
decode O O x = refl
decode O (S b) () 
decode (S a) O () 
decode (S a) (S b) x = ap S (decode a b x)


open import Coproduct 


thm : (a b : ℕ) → ((a ≡ b) ∨ (¬ (a ≡ b)))
thm O O = inl refl
thm O (S b) = inr (λ ())
thm (S a) O = inr (λ ())
thm (S a) (S b) with (thm a b)
thm (S a) (S .a) | inl refl = inl refl
thm (S a) (S b) | inr x = inr (thm′ a b x) where 
    thm′ : (a b : ℕ) → (¬ (a ≡ b)) → (¬ (S a ≡ S b))
    thm′ O O x x₁ = x refl
    thm′ O (S b) x ()
    thm′ (S a) .(S a) x refl = x refl

{-- proof of decidable equality of ℕ --^--- --}

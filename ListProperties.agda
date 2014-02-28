module ListProperties where

open import List renaming (length to len)
open import Natural
open import Equality
open import Level



module Length {ℓ : Level} {A : Set ℓ} where
  
  Lemma₁ : (a : List A) → (len a) ≡ (len ([] ++ a))
  Lemma₁ [] = refl
  Lemma₁ (x ∷ a) = refl

  Lemma₁-Sym = λ a →  ≡-symmetric (Lemma₁ a)

  Lemma₂ : (a : List A) → (e : A) → S (len a) ≡ len (e ∷ a)
  Lemma₂ [] e = refl
  Lemma₂ (x ∷ xs) e = refl

  Lemma₂-Sym = λ a e → ≡-symmetric (Lemma₂ a e)

open Length public

module Null where
  Lemma₃ : ∀ {ℓ} → {A : Set ℓ} → (a b : List A) → (e : A) → (a ≡ b)  → (e ∷ a) ≡ (e ∷ b)
  Lemma₃ a .a e refl = refl

  LemmaA : ∀ {ℓ} → {A : Set ℓ} → (a b c : List A) → (a ≡ b) → (c ++ a) ≡ (c ++ b)
  LemmaA a .a c refl = refl

  --- this proof (Lemma₄) is surprisingly difficult. it doesn't look difficult, but it wasn't
  --- easy to get right.
  Lemma₄ : ∀ {ℓ} → {A : Set ℓ} → (a : List A) → a ++ [] ≡ a
  Lemma₄ [] = refl
  Lemma₄ (x ∷ xs) = Lemma₃ (xs ++ []) xs x (Lemma₄ xs)

  Lemma₅ : ∀ {ℓ} → {A : Set ℓ} → (a : List A) → a ≡ [] ++ a
  Lemma₅ x = refl

  Lemma₆ : ∀ {ℓ} → {A : Set ℓ} → (a : List A) → (a ++ [] ≡ [] ++ a)
  Lemma₆ a = ≡-trans  (Lemma₄ a) (Lemma₅ a)

open Null public
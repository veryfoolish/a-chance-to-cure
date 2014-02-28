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

module Null {ℓ : Level} {A : Set ℓ} where

  Lemma₃ : (a b : List A) → (e : A) → (a ≡ b)  → (e ∷ a) ≡ (e ∷ b)
  Lemma₃ a .a e refl = refl

  LemmaA : (a b c : List A) → (a ≡ b) → (c ++ a) ≡ (c ++ b)
  LemmaA a .a c refl = refl

  --- surprisingly difficult to get right.
  Lemma₄ : (a : List A) → a ++ [] ≡ a
  Lemma₄ [] = refl
  Lemma₄ (head ∷ tail) = Lemma₃ (tail ++ []) tail head (Lemma₄ tail)

  Lemma₅ : {a : List A} → a ≡ [] ++ a
  Lemma₅ = refl

  Lemma₆ : (a : List A) → (a ++ [] ≡ [] ++ a)
  Lemma₆ a = ≡-trans  (Lemma₄ a) Lemma₅

open Null public
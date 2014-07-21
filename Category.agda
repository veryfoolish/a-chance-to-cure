{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import Equality
open import Natural

module Category where

L⟪_⟫ : ℕ → Level
L⟪ 0 ⟫ = lzero
L⟪ (S n) ⟫ = (lsuc L⟪ n ⟫)

record Category : Set (lsuc (lsuc L⟪ 0 ⟫)) where
  field
    Obj : Set L⟪ 0 ⟫
    Hom : Obj → Obj → Set L⟪ 0 ⟫
    Id : (A : Obj) → Hom A A
    comp : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    id-r : ∀ {A B : Obj} → {f : Hom A B} → comp f (Id A) ≡ f
    id-l : ∀ {A B} → {f : Hom A B} → comp (Id B) f ≡ f
    assoc : ∀ {A B C D} → {f : Hom C D} → {g : Hom B C} → {h : Hom A B} → comp f (comp g h) ≡ comp (comp f  g) h
open Category public

≤-trans′ : {a b c : ℕ} → b ≤ c → a ≤ b → a ≤ c
≤-trans′ p q = ≤-trans q p

inc : {a b : ℕ} → a ≤ b → S a ≤ S b
inc = +1≤

inc′ : {a b : ℕ} → a ≤ b → a ≤ S b
inc′ p = {!!}

helper : {a b : ℕ} → (S a ≤ S b) → a ≤ b
helper (+1≤ p) = p

helper′ : (a b : ℕ) → (S a ≤ S b) → a ≤ S b
helper′ O b (+1≤ p) = 0≤n
helper′ (S a) O (+1≤ ())
helper′ (S a) (S b) (+1≤ p) = +1≤ (helper′ a b p)


help : (a b : ℕ) → (f : a ≤ b) → ≤-trans id≤ f ≡ f
help O O 0≤n = refl
help O (S b) 0≤n = refl
help (S a) O ()
help (S a) (S b) f = {!h!}
                      

ℕ≤ : Category
ℕ≤ = record
       { Obj = ℕ
       ; Hom = _≤_
       ; Id = λ a → id≤ {a}
       ; comp = ≤-trans′
       ; id-r = {!help!}
       ; id-l = {!!}
       ; assoc = {!!}
       }


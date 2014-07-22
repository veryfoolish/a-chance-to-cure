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
    Obj : Set L⟪ 1 ⟫
    Hom : Obj → Obj → Set L⟪ 1 ⟫
    Id : (A : Obj) → Hom A A
    comp : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    id-r : ∀ {A B : Obj} → {f : Hom A B} → comp f (Id A) ≡ f
    id-l : ∀ {A B} → {f : Hom A B} → comp (Id B) f ≡ f
    assoc : ∀ {A B C D} → {f : Hom C D} → {g : Hom B C} → {h : Hom A B} → comp f (comp g h) ≡ comp (comp f  g) h
open Category public

data uhom (A B : Set) : Set (lsuc L⟪ 0 ⟫) where
  hom-form : (f : A → B) → uhom A B

composition : {A B C : Set} → (g : uhom B C) → (g : uhom A B) → (uhom A C)
composition (hom-form f) (hom-form f₁) = hom-form (λ z → f (f₁ z))

∙id : (A : Set) → uhom A A
∙id A = hom-form (λ z → z)

UniverseCategory : Category
UniverseCategory = record
                     { Obj = Set
                     ; Hom = uhom
                     ; Id = ∙id
                     ; comp = composition
                     ; id-r = {!!}
                     ; id-l = {!!}
                     ; assoc = {!!}
                     }

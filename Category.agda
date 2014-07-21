{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import Equality

module Category where

record Category {ℓ} : Set (lsuc ℓ) where
  field
    Obj : Set ℓ
    Hom : Obj → Obj → Set ℓ
    Id : (A : Obj) → Hom A A
    comp : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    id-r : ∀ {A B : Obj} → {f : Hom A B} → comp f (Id A) ≡ f
    id-l : ∀ {A B} → {f : Hom A B} → comp (Id B) f ≡ f
    assoc : ∀ {A B C D} → {f : Hom C D} → {g : Hom B C} → {h : Hom A B} → comp f (comp g h) ≡ comp (comp f  g) h
open Category public

module SomeTest {ℓ} where

  data FakeCatObj : Set ℓ where
    A B C : FakeCatObj

  data HomFake (a b : FakeCatObj) : Set ℓ where
    hom : HomFake a b

  ∙ID : (A : FakeCatObj) → (HomFake A A)
  ∙ID x = hom

  ∙comp : {X Y Z : FakeCatObj} → HomFake Y Z → HomFake X Y → HomFake X Z
  ∙comp hom hom = hom

  ∙id-r : {A B : FakeCatObj} → {f : HomFake A B} → (∙comp f (∙ID A)) ≡ f
  ∙id-r {x} {y} {hom} = refl

  ∙id-l : {A B : FakeCatObj} → {f : HomFake A B} → (∙comp (∙ID B) f) ≡ f
  ∙id-l {x} {y} {hom} = refl

  ∙assoc : (A B C D : FakeCatObj) → (f : HomFake C D) → (g : HomFake B C) → (h : HomFake A B) → ∙comp f (∙comp g h) ≡ ∙comp (∙comp f g) h
  ∙assoc x y z d hom hom hom = refl

  CC : Category {ℓ}
  CC = record
         { Obj = FakeCatObj
         ; Hom = λ x y → HomFake x y
         ; Id = ∙ID
         ; comp = ∙comp
         ; id-r = ∙id-r
         ; id-l = ∙id-l
         ; assoc = λ {w} {x} {y} {z} {f} {g} {h} → ∙assoc w x y z f g h
         }

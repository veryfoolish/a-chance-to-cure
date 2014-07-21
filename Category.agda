{-# OPTIONS --without-K #-}
open import Agda.Primitive
open import Equality

module Category where

record Category {ℓ} (Obj : Set ℓ) 
                (Hom : Obj → Obj → (Set ℓ)) 
                (Id : (A : Obj) → Hom A A)
                (_∘_ : ∀ {A B C : Obj} → Hom B C → Hom A B → Hom A C) 
                (_==_ : ∀ {A B : Obj} → (f g : Hom A B) → Set ℓ) : Set (lsuc ℓ) where
  field

    id-r : (A B : Obj) → {f : Hom A B} → (f ∘ (Id A)) == f
    id-l : ∀ {A B} → {f : Hom A B} → ((Id B) ∘ f) == f
    assoc : ∀ {A B C D} → {f : Hom C D} → {g : Hom B C} → {h : Hom A B} → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
open Category public



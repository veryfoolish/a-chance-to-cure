{-# OPTIONS --type-in-type #-}
module Category where

open import Product
open import Equality
open import Sigma

theory : {A : Set} → {df cg a : A} → df ≡ a → cg ≡ a → df ≡ cg
theory refl refl = refl

record Category : Set where
  field Ar : Set
        Ob : Set
        dom : Ar → Ob
        cod : Ar → Ob
        Id : Ob → Ar
        comp : (g f : Ar) → {p : (dom g) ≡ (cod f)} →  Ar
        id-axL : (A : Ob) → ((dom (Id A)) ≡ A)
        id-axR : (A : Ob) → ((cod (Id A)) ≡ A)

  axwhatever : {A : Ob}  → ((dom (Id A)) ≡ ((cod (Id A))))
  axwhatever {A} = theory (id-axL A) (id-axR A)

  field id-axiomC : {A : Ob} {f : Ar} {q : dom f ≡ A} → (comp f (Id A) {(theory q (id-axR A))}) ≡ f
  
  thm : ∀ {A} → (comp (Id A) (Id A) {axwhatever}) ≡ (Id A)
  thm = id-axiomC




module Monoid where

open import Equality
open import Cartesian
open import Sigma

record Monoid (A : Set) : Set where
  field
    _⋆_ : A → A → A
    e : A
    unit : {x : A} → (x ⋆ e ≡ x) × (e ⋆ x ≡ x)
    assoc : (x y z : A) → ((x ⋆ y) ⋆ z) ≡ (x ⋆ (y ⋆ z))
open Monoid public

module _ where
  open import Natural
  open import NaturalProperties

  theorem : Monoid ℕ
  theorem = record { _⋆_ = _+_; 
                     e = 0;
                     unit = (+0-right-id , +0-left-id);
                     assoc = +-assoc}
module Coproduct where

open import Level using (Level) renaming (_⊔_ to lmax)

data _∨_ {i j : Level} (A : Set i) (B : Set j) : Set (lmax i j) where
  inl : A → A ∨ B
  inr : B → A ∨ B


module Rec-∨ {i j k : Level} (A : Set i) (B : Set j) (C : Set k) where
  rec-∨ : (A → C) → (B → C) → A ∨ B → C
  rec-∨ g₁ g₂ (inl a) = (g₁ a)
  rec-∨ g₁ g₂ (inr b) = (g₂ b)
open Rec-∨ public

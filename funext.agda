{-- some thoughts on functional extensionality --}

open import Agda.Primitive using (Level)
open import Identity

module funext where

module ∙ap∙ {k l} {C : Set k} {D : Set l} where
  {-- repeating ap here for readability --}
  ap∙ : {x y : C} → (f : C → D) → x ≡ y → f x ≡ f y
  ap∙ f refl = refl

open ∙ap∙ public

module funext′ {ℓ ⊚ : Level} (A : Set ℓ) (B : Set ⊚) where
  apply : (x : A) → ((A → B) → B)
  apply x = λ f → f x

  happly : {f g : A → B} → (p : f ≡ g) → ((x : A) → (f x) ≡ (g x))
  happly p x = ap∙ (apply x) p

open funext′ public

{- of course we can't prove the converse in intentional type -}
{- theory; because the functions are only "extensionally" -}
{- equal. Intentional equality implies extensional equality but the -}
{- opposite is not true in general -}

module Thoughts where

--- Okay, so I want to get this problem REALLY clear.
--- It's the problem of converting a string to a value <= some maximum value.
--- All of this is provisional, and really isn't meant to be in a STDLIB.

open import Level using (Level) renaming (zero to ℓz)
open import Natural
open import Fin
open import List
open import Equality

--- first of all, what is a string? well, on my computer it's a thing that basically
--- is a list of 256 different characters. so what's a character? it's a member of 
--- fin 256

Character = Fin(256)

--- so a string a list of these things.

String = List(Character)


--- we want to map some set of things in Character to decimal digits.
--- how do we do this?
--- well...

Decimal = Fin(10)

--- of course, we want them to be UNIQUE i.e.,
--- f : Fin(10) → Fin(256)
--- f a = fzero
---
--- obviously this won't do, this isn't enough of a definition.
---
---
--- we want... f : Fin(10) → Fin(256) such that if x : Fin(10) then f(x):Fin(256) and we want
--- a f(-1) such that inv-f f x ≡ x 
---
--- so we really want a *pair* of morphisms. f, inv-f

--- in ASCII the encoding is:
--- '0' => 48
--- '1' => 49
--- ... => ...
--- '9' => 57

Toℕ : Decimal → ℕ
Toℕ a = (toℕ a)

-- if s(n) ≡ m ⇒ n < m

helper : {m : ℕ} →  (m ≤ m)
helper {0} = 0≤n
helper {S n} = +1≤ (helper {n})

sn≡m-then-n<m : {m n : ℕ} → (S n ≡ m) → n < m
sn≡m-then-n<m refl = +1≤ helper

<zth : (n : ℕ) → 0 < S n
<zth O = +1≤ 0≤n
<zth (S a) = +1≤ 0≤n

9<10 : 9 < 10
9<10 = sn≡m-then-n<m refl

5<10 : 5 < 10 
5<10 = +1≤ (+1≤ (+1≤ (+1≤ (+1≤ (+1≤ 0≤n)))))

five : Decimal
five = fromℕ≤ 5<10

theorem′ : (m : ℕ) → m ≤ m
theorem′ O = 0≤n
theorem′ (S a) = +1≤ (theorem′ a)

theorem-a : (m : ℕ) → m ≤ (S m)
theorem-a 0 = 0≤n
theorem-a (S a) = +1≤ (theorem-a a)


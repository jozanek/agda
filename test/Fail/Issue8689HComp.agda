-- Issue #8689: the internal type checker did not check the side
-- condition of hcomp.  The type of a with-function is checked only by
-- the internal type checker.

{-# OPTIONS --cubical --safe #-}

open import Agda.Primitive.Cubical renaming (primHComp to hcomp)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

data Reveal (A : Set) : A → Set where
  rev : {a : A} → Reveal A a

-- The hcomp in the type of foo is well-formed only because p j is y
-- on the face j = i1.  The with-abstraction replaces p j by w and
-- forgets this, so the with-function has the type
--   (x y : Nat) (p : x ≡ y) (j : I) (w : Nat) → Reveal Nat (hcomp (λ i _ → y) w)
-- in which the hcomp breaks its side condition  w = y  on j = i1.

foo : (x y : Nat) (p : x ≡ y) (j : I) → Reveal Nat (hcomp {φ = j} (λ i _ → y) (p j))
foo x y p j with p j
... | w = rev

-- Expected error: w and y are not equal (in the with-function type).

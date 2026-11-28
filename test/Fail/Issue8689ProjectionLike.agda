-- Issue #8689: the internal type checker puts applications of
-- projection-like functions into postfix form.  Then the hcomp below
-- is followed by a projection elimination, and the side condition of
-- hcomp has to be checked all the same.

{-# OPTIONS --cubical --safe #-}

open import Agda.Primitive.Cubical renaming (primHComp to hcomp)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

data Reveal (A : Set) : A → Set where
  rev : {a : A} → Reveal A a

data Wrap (A : Set) : Set where
  wrap : A → Wrap A

-- unwrap is projection-like.
unwrap : {A : Set} → Wrap A → A
unwrap (wrap a) = a

-- The hcomp is well-formed only because p j is y on the face j = i1.
-- The with-abstraction replaces p j by w.

foo : (g : Nat → Wrap Nat) (x y : Nat) (p : x ≡ y) (j : I) →
      Reveal Nat (unwrap (hcomp {φ = j} (λ i _ → g y) (g (p j))))
foo g x y p j with p j
... | w = rev

-- Expected error: w and y are not equal (in the with-function type).

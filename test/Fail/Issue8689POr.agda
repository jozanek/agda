-- Issue #8689: the internal type checker did not check the side
-- condition of primPOr.  The type of a with-function is checked only by
-- the internal type checker.

{-# OPTIONS --cubical --safe #-}

open import Agda.Primitive.Cubical renaming (primHComp to hcomp)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

data Reveal (A : Set) : A → Set where
  rev : {a : A} → Reveal A a

-- The two partial elements of primPOr agree on the face j only because
-- p j is y on j = i1.  The with-abstraction replaces p j by w.

foo : (x y : Nat) (p : x ≡ y) (j : I) →
      Reveal Nat (hcomp {φ = j} (λ i → primPOr j j (λ _ → y) (λ _ → p j)) y)
foo x y p j with p j
... | w = rev

-- Expected error: y and w are not equal (in the with-function type).

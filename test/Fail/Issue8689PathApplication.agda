-- Issue #8689: the internal type checker did not check that the
-- endpoints stored in a path application are the endpoints of the
-- path type.  The type of a with-function is checked only by the
-- internal type checker.

{-# OPTIONS --cubical --safe #-}

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

data Reveal (A : Set) : A → Set where
  rev : {a : A} → Reveal A a

+-zero : (x : Nat) → x + 0 ≡ x
+-zero zero    = λ _ → zero
+-zero (suc x) = λ i → suc (+-zero x i)

-- In internal syntax, the path application  +-zero x j  stores the
-- endpoints  x + 0  and  x  of the path.  The with-abstraction replaces
-- the endpoint  x + 0  by w, but the type of  +-zero x  is still
-- x + 0 ≡ x.

foo : (x : Nat) (j : I) → Reveal Nat (+-zero x j)
foo x j with x + 0
... | w = rev

-- Expected error: w and x + 0 are not equal (in the with-function type).

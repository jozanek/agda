-- Issue #8689: the internal type checker also has to check the
-- endpoints of an eta-contracted path lambda.  instantiateFull
-- contracts the path lambda  λ i → f i  to  f, and f has a function
-- type, not a path type.  The type of a with-function is checked only
-- by the internal type checker.

{-# OPTIONS --cubical --safe #-}

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

data Reveal (A : Set) : A → Set where
  rev : {a : A} → Reveal A a

-- The with-abstraction replaces  f i0  by w.  Then the path
-- λ i → f i  (contracted to f) does not have the type  w ≡ f i1.

foo : (f : I → Nat) → Reveal (f i0 ≡ f i1) (λ i → f i)
foo f with f i0
... | w = rev

-- Expected error: f i0 and w are not equal (in the with-function type).

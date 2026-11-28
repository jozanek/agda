-- Issue #8689: the internal type checker also has to check the
-- endpoints that a path application stores when its head has a
-- function type.  instantiateFull contracts the path lambda  λ i → f i
-- to  f, and substitution puts f in front of the path application
-- p j  in the body of T.  The type of a with-function is checked only
-- by the internal type checker.

{-# OPTIONS --cubical --safe #-}

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

data Reveal (A : Set) : A → Set where
  rev : {a : A} → Reveal A a

module _ {x y : Nat} (p : x ≡ y) (j : I) where

  T : Set
  T = Reveal Nat (p j)

-- The with-function type contains the path application  f j  with the
-- stored endpoints  w  and  f i1, because the with-abstraction replaces
-- f i0  by w.  But  f j  is  f i0  at  j = i0, not w.

foo : (f : I → Nat) (j : I) → T {f i0} {f i1} (λ i → f i) j
foo f j with f i0
... | w = rev

-- Expected error: w and f i0 are not equal (in the with-function type).

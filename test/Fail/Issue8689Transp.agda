-- Issue #8689: the internal type checker did not check the side
-- condition of transp.  The type of a with-function is checked only by
-- the internal type checker.

{-# OPTIONS --cubical --safe #-}

open import Agda.Primitive.Cubical renaming (primTransp to transp)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

data Reveal (A : Set) : A → Set where
  rev : {a : A} → Reveal A a

module _ (A : I → Set) where

  F : Nat → I → Set
  F zero    i = Nat
  F (suc n) i = A i

  -- The transp in the type of foo is well-formed only because p j is 0
  -- on the face j = i1: there the family  λ i → F (p j) i  is
  -- λ i → Nat, which is constant.  The with-abstraction replaces p j
  -- by w, and the family  λ i → F w i  is not constant.

  foo : (x : Nat) (p : x ≡ 0) (j : I) (a : F (p j) i0) →
        Reveal (F (p j) i1) (transp (λ i → F (p j) i) j a)
  foo x p j a with p j
  ... | w = rev

-- Expected error: i and i0 are not equal (in the with-function type).

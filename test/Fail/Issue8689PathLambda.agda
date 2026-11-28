-- Issue #8689: the internal type checker did not check the endpoints
-- of path lambdas.  The type of a with-function is checked only by the
-- internal type checker.
--
-- The development version of the cubical library used this pattern
-- (_UsingEq) in Cubical.Data.Nat.

{-# OPTIONS --cubical --safe #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat renaming (_<_ to _<ᵇ_)
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma

singl : {A : Set} (a : A) → Set
singl {A} a = Σ A (λ x → a ≡ x)

_UsingEq : {A : Set} (a : A) → singl a
a UsingEq = a , (λ _ → a)
infixl 0 _UsingEq

min : Nat → Nat → Nat
min zero    m       = zero
min (suc n) zero    = zero
min (suc n) (suc m) with n <ᵇ m UsingEq
... | false , _ = suc m
... | true  , _ = suc n

-- The goal contains  (suc n <ᵇ suc m , λ _ → suc n <ᵇ suc m)  as the
-- argument of type  singl (suc n <ᵇ suc m)  of the with-function of min.
-- The with-abstraction replaces both occurrences of  suc n <ᵇ suc m  by w,
-- and the path  λ _ → w  does not have the type  (suc n <ᵇ suc m) ≡ w.

minSuc : (n m : Nat) → min (suc (suc n)) (suc (suc m)) ≡ suc (min (suc n) (suc m))
minSuc n m with suc n <ᵇ suc m
... | false = λ _ → suc (suc m)
... | true  = λ _ → suc (suc n)

-- Expected error: w and n <ᵇ m are not equal (in the with-function type).

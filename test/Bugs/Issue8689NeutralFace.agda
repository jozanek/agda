-- Issue #8689: since the internal type checker checks the side
-- conditions of hcomp, Agda rejects this well-typed with-abstraction.
-- Before, test/Succeed/Issue6506.agda had exactly this shape.
--
-- The with-function type contains the reduct of ex, which is
--   hcomp {φ = i ∨ ~ i} (λ _ → primPOr i (~ i) (λ _ → A) (λ _ → A)) (p i).
-- Its side condition holds, because p i0 and p i1 are A.
-- But i is a postulate, not a variable, and the conversion checker can
-- split the face  i ∨ ~ i  only if i is a variable.  The same happens
-- for other neutral interval terms that are not variables, for example
-- h n  with  h : Nat → I.  The type checker rejects this hcomp too,
-- if you write it yourself.
--
-- When this is fixed, move this test to test/Succeed.

{-# OPTIONS --cubical #-}
module Issue8689NeutralFace where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
  renaming (primIMax to _∨_ ; primIMin to _∧_ ; primINeg to ~_ ; primComp to comp ; primHComp to hcomp ; primTransp to transp)

postulate
  A : Type
  B : Type
  p : A ≡ A
  i : I

ex : Type
ex = transp {λ i → lsuc lzero} (λ i → A ≡ A) i0 p i

test : Type → ex ≡ ex
test t with B
... | A = λ i → ex

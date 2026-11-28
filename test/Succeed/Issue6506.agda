{-# OPTIONS --cubical --no-double-check #-}
module Issue6506 where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
  renaming (primIMax to _∨_ ; primIMin to _∧_ ; primINeg to ~_ ; primComp to comp ; primHComp to hcomp ; primTransp to transp)

postulate
  A : Type
  B : Type
  p : A ≡ A

-- Issue #8689: i is a module parameter, not a postulate.
-- The with-function type below contains the reduct of ex, which is
--   hcomp {φ = i ∨ ~ i} (λ _ → primPOr i (~ i) (λ _ → A) (λ _ → A)) (p i).
-- The internal type checker checks the side condition of this hcomp.
-- The conversion checker can split the face  i ∨ ~ i  only if i is a
-- variable.  test/Bugs/Issue8689NeutralFace.agda has the old version of
-- this test, with a postulated i, which Agda now rejects.

module _ (i : I) where

  ex : Type
  ex = transp {λ i → lsuc lzero} (λ i → A ≡ A) i0 p i

  -- Incorrect level in transp of PathP also leads to malformed
  -- with-abstraction types(!)
  test : Type → ex ≡ ex
  test t with B
  ... | A = λ j → ex

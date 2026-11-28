{-# OPTIONS_GHC -Wunused-imports #-}

-- | Side conditions of cubical primitives.
--
--   Some cubical primitives put conditions on their arguments that
--   their types do not express.  For example, in @hcomp {φ = φ} u a@
--   the base @a@ has to agree with @u i0@ on @φ@.
--
--   The type checker ("Agda.TypeChecking.Rules.Application") and the
--   internal type checker ("Agda.TypeChecking.CheckInternal") both
--   check these side conditions (issue #8689).
--
--   This module imports "Agda.TypeChecking.Conversion".  Thus,
--   "Agda.TypeChecking.Primitive" and the modules it imports must not
--   import this module.

module Agda.TypeChecking.Primitive.Cubical.SideConditions
  ( SideCondition(..)
  , cubicalSideCondition
  ) where

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Conversion (equalTerm, equalTermOnFace)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Names
import Agda.TypeChecking.Pretty (text)
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Primitive.Cubical.Base (primIntervalType)
import Agda.TypeChecking.Substitute

-- | The side condition of a cubical primitive that is applied to
--   enough arguments.
data SideCondition = SideCondition
  { sideConditionArg :: Int
      -- ^ The position of the argument that the side condition is about.
      --   The type checker blocks this argument on the side condition.
  , sideConditionArgType :: Type
      -- ^ The type of this argument.
  , sideConditionCheck :: TCM ()
      -- ^ Check the side condition.
  }

-- | If the primitive has a side condition, return the function that
--   computes the side condition from the arguments of the primitive.
--   This function returns 'Nothing' if the primitive is not applied
--   to enough arguments.
cubicalSideCondition :: PrimitiveId -> Maybe (Args -> TCM (Maybe SideCondition))
cubicalSideCondition = \case
  PrimComp   -> Just sideConditionComp
  PrimHComp  -> Just sideConditionHComp
  PrimTrans  -> Just sideConditionTrans
  PrimPOr    -> Just sideConditionPOr
  Prim_glue  -> Just sideCondition_glue
  Prim_glueU -> Just sideCondition_glueU
  _          -> Nothing

-- | @primComp : ∀ {ℓ} (A : (i : I) → Set (ℓ i)) (φ : I) (u : ∀ i → Partial φ (A i)) (a : A i0) → A i1@
--
--   Check:  @u i0 = (λ _ → a) : Partial φ (A i0)@.
--
sideConditionComp :: Args -> TCM (Maybe SideCondition)
sideConditionComp = \case
    l : a : phi : u : a0 : _ -> do
      iz <- Arg defaultArgInfo <$> intervalUnview IZero
      let lz = unArg l `apply` [iz]
          az = unArg a `apply` [iz]
      ty <- el's (pure lz) $ primPartial <#> pure lz <@> pure (unArg phi) <@> pure az
      bAz <- el' (pure lz) (pure az)
      return $ Just $ SideCondition 4 bAz $
        equalTerm ty
          (Lam defaultArgInfo $ NoAbs "_" $ unArg a0)
          (apply (unArg u) [iz])
    _ -> return Nothing

-- | @primHComp : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A@
--
--   Check:  @u i0 = (λ _ → a) : Partial φ A@.
--
sideConditionHComp :: Args -> TCM (Maybe SideCondition)
sideConditionHComp = \case
    l : a : phi : u : a0 : _ -> do
      -- iz = i0
      iz <- Arg defaultArgInfo <$> intervalUnview IZero
      -- ty = Partial φ A
      ty <- el's (pure (unArg l)) $ primPartial <#> pure (unArg l) <@> pure (unArg phi) <@> pure (unArg a)
      -- (λ _ → a) = u i0 : ty
      bA <- el' (pure $ unArg l) (pure $ unArg a)
      return $ Just $ SideCondition 4 bA $
        equalTerm ty
          (Lam defaultArgInfo $ NoAbs "_" $ unArg a0)
          (apply (unArg u) [iz])
    _ -> return Nothing

-- | @transp : ∀{ℓ} (A : (i : I) → Set (ℓ i)) (φ : I) (a0 : A i0) → A i1@
--
--   Check:  If φ, then @A i = A i0 : Set (ℓ i)@ must hold for all @i : I@.
--
--   Only 3 arguments are needed to check the side condition
--   (Andreas, 2019-03-02, issue #3601).
--
sideConditionTrans :: Args -> TCM (Maybe SideCondition)
sideConditionTrans = \case
    l : a : phi : _ -> do
      iz <- Arg defaultArgInfo <$> intervalUnview IZero
      -- ty = (i : I) -> Set (l i)
      ty <- runNamesT [] $ do
        l <- open $ unArg l
        nPi' "i" primIntervalType $ \ i -> (sort . tmSort <$> (l <@> i))
      return $ Just $ SideCondition 1 ty $
        equalTermOnFace (unArg phi) ty
          (unArg a)
          (Lam defaultArgInfo $ NoAbs "_" $ apply (unArg a) [iz])
    _ -> return Nothing

-- | @primPOr : ∀ {ℓ} (φ₁ φ₂ : I) {A : Partial (φ₁ ∨ φ₂) (Set ℓ)}
--             → (u : PartialP φ₁ (λ (o : IsOne φ₁) → A (IsOne1 φ₁ φ₂ o)))
--             → (v : PartialP φ₂ (λ (o : IsOne φ₂) → A (IsOne2 φ₁ φ₂ o)))
--             → PartialP (φ₁ ∨ φ₂) A@
--
--   Check:  @u = v : PartialP (φ₁ ∨ φ₂) A@ whenever @IsOne (φ₁ ∧ φ₂)@.
--
sideConditionPOr :: Args -> TCM (Maybe SideCondition)
sideConditionPOr = \case
    l : phi1 : phi2 : a : u : v : _ -> do
      phi <- intervalUnview (IMin phi1 phi2)
      reportSDoc "tc.term.por" 10 $ text (show phi)
      t1 <- runNamesT [] $ do
             l <- open . unArg $ l
             a <- open . unArg $ a
             psi <- open =<< intervalUnview (IMax phi1 phi2)
             pPi' "o" psi $ \ o -> el' l (a <..> o)
      tv <- runNamesT [] $ do
             l    <- open . unArg $ l
             a    <- open . unArg $ a
             phi1 <- open . unArg $ phi1
             phi2 <- open . unArg $ phi2
             pPi' "o" phi2 $ \ o -> el' l (a <..> (cl primIsOne2 <@> phi1 <@> phi2 <@> o))
      return $ Just $ SideCondition 5 tv $
        -- φ₁ ∧ φ₂  ⊢ u , v : PartialP (φ₁ ∨ φ₂) \ o → a o
        equalTermOnFace phi t1 (unArg u) (unArg v)
    _ -> return Nothing

-- | @prim^glue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
--              → {T : Partial φ (Set ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
--              → (t : PartialP φ T) → (a : A) → primGlue A T e@
--
--   Check   @φ ⊢ a = e 1=1 (t 1=1)@  or actually the equivalent:  @(\ _ → a) = (\ o -> e o (t o)) : PartialP φ A@
sideCondition_glue :: Args -> TCM (Maybe SideCondition)
sideCondition_glue = \case
    la : lb : bA : phi : bT : e : t : a : _ -> do
      v <- runNamesT [] $ do
            lb  <- open . unArg $ lb
            la  <- open . unArg $ la
            bA  <- open . unArg $ bA
            phi <- open . unArg $ phi
            bT  <- open . unArg $ bT
            e   <- open . unArg $ e
            t   <- open . unArg $ t
            let f o = cl primEquivFun <#> lb <#> la <#> (bT <..> o) <#> bA <@> (e <..> o)
            glam defaultIrrelevantArgInfo "o" $ \ o -> f o <@> (t <..> o)
      ty <- runNamesT [] $ do
            lb  <- open . unArg $ lb
            phi <- open . unArg $ phi
            bA  <- open . unArg $ bA
            el's lb $ cl primPartialP <#> lb <@> phi <@> glam defaultIrrelevantArgInfo "o" (\ _ -> bA)
      let a' = Lam defaultIrrelevantArgInfo (NoAbs "o" $ unArg a)
      ta <- el' (pure $ unArg la) (pure $ unArg bA)
      return $ Just $ SideCondition 7 ta $ equalTerm ty a' v
    _ -> return Nothing

-- | @prim^glueU : ∀ {ℓ} {φ : I}
--              → {T : I → Partial φ (Set ℓ)} → {A : Set ℓ [ φ ↦ T i0 ]}
--              → (t : PartialP φ (T i1)) → (a : outS A) → hcomp T (outS A)@
--
--   Check   @φ ⊢ a = transp (\ i -> T 1=1 (~ i)) i0 (t 1=1)@  or actually the equivalent:
--           @(\ _ → a) = (\o -> transp (\ i -> T o (~ i)) i0 (t o)) : PartialP φ (T i0)@
sideCondition_glueU :: Args -> TCM (Maybe SideCondition)
sideCondition_glueU = \case
    la : phi : bT : bA : t : a : _ -> do
      v <- runNamesT [] $ do
            la  <- open . unArg $ la
            phi <- open . unArg $ phi
            bT  <- open . unArg $ bT
            bA  <- open . unArg $ bA
            t   <- open . unArg $ t
            let f o = cl primTrans <#> lam "i" (const la) <@> lam "i" (\ i -> bT <@> (cl primINeg <@> i) <..> o) <@> cl primIZero
            glam defaultIrrelevantArgInfo "o" $ \ o -> f o <@> (t <..> o)
      ty <- runNamesT [] $ do
            la  <- open . unArg $ la
            phi <- open . unArg $ phi
            bT  <- open . unArg $ bT
            pPi' "o" phi $ \ o -> el' la (bT <@> cl primIZero <..> o)
      let a' = Lam defaultIrrelevantArgInfo (NoAbs "o" $ unArg a)
      ta <- runNamesT [] $ do
            la  <- open . unArg $ la
            phi <- open . unArg $ phi
            bT  <- open . unArg $ bT
            bA  <- open . unArg $ bA
            el' la (cl primSubOut <#> (cl primLevelSuc <@> la) <#> (Sort . tmSort <$> la) <#> phi <#> (bT <@> cl primIZero) <@> bA)
      return $ Just $ SideCondition 5 ta $ equalTerm ty a' v
    _ -> return Nothing

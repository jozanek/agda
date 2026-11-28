{-# OPTIONS_GHC -Wunused-imports #-}

-- Initially authored by Andreas, 2013-10-22.

-- | A bidirectional type checker for internal syntax.
--
--   Performs checking on unreduced terms.
--   With the exception that projection-like function applications
--   have to be reduced since they break bidirectionality.

module Agda.TypeChecking.CheckInternal
  ( checkType, infer, inferSpine
  , CheckInternal(..)
  , Action(..), defaultAction, eraseUnusedAction
  ) where

import Control.Monad

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Common.Pretty (prettyShow)

import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive.Cubical.SideConditions (SideCondition(..), cubicalSideCondition)
import Agda.TypeChecking.ProjectionLike (elimView, LoneProjectionLikeToLambda(..))
import Agda.TypeChecking.Records (shouldBeProjectible)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Sort
import Agda.TypeChecking.Telescope

import Agda.Utils.Function (applyWhen, applyWhenM)
import Agda.Utils.Functor (($>))
import Agda.Utils.Maybe
import Agda.Utils.Size
import Agda.Utils.Tuple (fst3, snd3)

import Agda.Utils.Impossible

import Agda.Interaction.Options
import Agda.TypeChecking.Reduce (instantiate, reduce)

-- * Bidirectional rechecker

-- | Entry point for e.g. checking WithFunctionType.
checkType :: Type -> TCM ()
checkType t = catchConstraint (CheckType t) $ inferInternal t

-- | 'checkInternal' traverses the whole 'Term', and we can use this
--   traversal to modify the term.
data Action = Action
  { preAction  :: Type -> Term -> TCM Term
    -- ^ Called on each subterm before the checker runs.
  , postAction :: Type -> Term -> TCM Term
    -- ^ Called on each subterm after the type checking.
  , modalityAction :: Modality -> Modality -> Modality
    -- ^ Called for each @ArgInfo@.
    --   The first 'Modality' is from the type,
    --   the second from the term.
  , elimViewAction :: Term -> TCM Term
    -- ^ Called for bringing projection-like funs in post-fix form
  }

-- | The default action is to not change the 'Term' at all.
defaultAction :: Action
defaultAction = Action
  { preAction       = \ _ -> return
  , postAction      = \ _ -> return
  , modalityAction  = \ _ -> id
  , elimViewAction  = elimView LoneProjectionLikeToLambda
  }

eraseUnusedAction :: Action
eraseUnusedAction = defaultAction { postAction = eraseUnused }
  where
    eraseUnused :: Type -> Term -> TCM Term
    eraseUnused t = \case
      Def f es -> do
        pols <- getPolarity f
        return $ Def f $ eraseIfNonvariant pols es
      v        -> return v

    eraseIfNonvariant :: [Polarity] -> Elims -> Elims
    eraseIfNonvariant []                  es             = es
    eraseIfNonvariant pols                []             = []
    eraseIfNonvariant (Nonvariant : pols) (e : es) = (fmap dontCare e) : eraseIfNonvariant pols es
    eraseIfNonvariant (_          : pols) (e : es) = e : eraseIfNonvariant pols es

class CheckInternal a where
  checkInternal' :: Action -> a -> Comparison -> TypeOf a -> TCM a

  checkInternal :: a -> Comparison -> TypeOf a -> TCM ()
  checkInternal v cmp t = void $ checkInternal' defaultAction v cmp t

  inferInternal' :: (TypeOf a ~ ()) => Action -> a -> TCM a
  inferInternal' act v = checkInternal' act v CmpEq ()

  inferInternal :: (TypeOf a ~ ()) => a -> TCM ()
  inferInternal v = checkInternal v CmpEq ()


instance CheckInternal Type where
  checkInternal' action (El s t) cmp _ = do
    reportSDoc "tc.check.internal" 20 $ sep
      [ "checking internal type "
      , nest 2 $ sep [ prettyTCM t <+> ":"
                     , nest 2 $ prettyTCM s ]
      ]
    t' <- checkInternal' action t cmp (sort s)
    -- Nathaniel, 2026-10-25: We used to reinfer the sort and check against it
    -- here, but @checkInternal'@ for @Term@ should already check the sort, so
    -- this was redundant
    --
    -- s' <- sortOf t'
    -- reportSDoc "tc.check.internal" 30 $
    --   "checking if sort" <+> prettyTCM s' <+>
    --   "of" <+> prettyTCM t' <+>
    --   "fits in given sort" <+> prettyTCM s
    -- compareSort cmp s' s
    return (El s t')

instance CheckInternal Term where
  checkInternal' :: Action -> Term -> Comparison -> Type -> TCM Term
  checkInternal' action v cmp t = verboseBracket "tc.check.internal" 20 "" $ do

    -- Debug print
    verboseS "tc.check.internal" 20 do
      reportSDoc "tc.check.internal" 20 $ sep
        [ "checking internal "
        , nest 2 $ sep [ prettyTCM v <+> ":"
                      , nest 2 $ prettyTCM t ] ]
      reportSDoc "tc.check.internal" 60 $ sep
        [ "checking internal with DB indices"
        , nest 2 $ sep [ pretty v <+> ":"
                      , nest 2 $ pretty t ] ]
      ctx <- getContextTelescope
      unless (null ctx) $ reportSDoc "tc.check.internal" 30 $ sep
        [ "In context"
        , nest 2 $ sep [ prettyTCM ctx ] ]

    -- Bring projection-like funs in post-fix form,
    -- (even lone ones by default).
    v <- elimViewAction action =<< preAction action t v
    postAction action t =<< case v of
      Var i es   -> do
        d <- domOfBV i
        n <- nameOfBV i

        -- Lucas, 23-11-2022:
        -- For now we only check if pure modalities are respected.
        -- In the future we SHOULD also be doing the same checks for every modality, as in Rules/Applications.hs
        -- (commented below)
        -- but this will break stuff that is allowed right now

        reportSDoc "tc.check.internal" 30 $ fsep
          [ "variable" , prettyTCM (var i) , "has type" , prettyTCM (unDom d)
          , "and modality", pretty (getModality d)
          ]

        unless (usableCohesion d) $
          typeError $ VariableIsOfUnusableCohesion n (getCohesion d)

        unless (usablePolarity d) $
          typeError $ VariableIsOfUnusablePolarity n (getModalPolarity d)

        checkSpine action (unDom d) (Var i) es cmp t
      Def f es   -> do  -- f is not projection(-like)!
        -- There is no "implicitely applied module telescope" at this stage, so no
        -- need to check it for modal errors, everything is covered by the
        -- variable rule!
        def <- getConstInfo f
        v' <- checkSpine action (defType def) (Def f) es cmp t
        checkCubicalSideCondition def es
        return v'
      MetaV x es -> do -- we assume meta instantiations to be well-typed
        a <- metaType x
        reportSDoc "tc.check.internal" 30 $ "metavariable" <+> prettyTCM x <+> "has type" <+> prettyTCM a
        checkSpine action a (MetaV x) es cmp t
      Con c ci vs -> do
        -- We need to fully apply the constructor to make getConType work!
        fullyApplyCon c vs t $ \ _d _dt _pars a vs' tel t -> do
          checkSpine action a (Con c ci) vs' cmp t >>= \case
            Con c ci vs2 ->
              -- Strip away the extra arguments
              return $ applySubst (strengthenS impossible (size tel))
                $ Con c ci $ take (length vs) vs2
            _ -> __IMPOSSIBLE__
      Lit l      -> do
        lt <- litType l
        compareType cmp lt t
        return $ Lit l
      Lam ai vb  -> do
        (a, b, endpoints) <- shouldBePiOrPath t
        ai <- checkArgInfo action ai $ domInfo a
        let name = suggests [ Suggestion vb , Suggestion b ]
        v' <- addContext (name, a) $ do
          Lam ai . Abs (absName vb) <$> checkInternal' action (absBody vb) cmp (absBody b)
        whenJust endpoints $ checkPathLambdaEndpoints b vb
        return v'
      Pi a b     -> do
        s <- shouldBeSort t
        reportSDoc "tc.check.internal" 30 $ "pi type should have sort" <+> prettyTCM s
        when (s == SizeUniv) $ typeError $ FunctionTypeInSizeUniv v
        experimental <- optExperimentalIrrelevance <$> pragmaOptions
        let sa  = getSort a
            sb  = getSort (unAbs b)
            mkDom v = El sa v <$ a
            mkRng v = fmap (v <$) b
            -- Preserve NoAbs
            goInside = case b of
              Abs{}   -> addContext $ (absName b,) $
                inverseApplyPolarity (withStandardLock UnusedPolarity) $
                applyWhen experimental (mapRelevance irrelevantToShapeIrrelevant) a
              NoAbs{} -> id
        a <- applyWhenM (optPolarity <$> pragmaOptions) (applyPolarityToContext negativePolarity) $
               mkDom <$> checkInternal' action (unEl $ unDom a) CmpLeq (sort sa)
        v' <- goInside $ Pi a . mkRng <$> checkInternal' action (unEl $ unAbs b) CmpLeq (sort sb)
        s' <- sortOf v -- Issue #6205: do not use v' since it might not be valid syntax
        reportSDoc "tc.check.internal" 30 $
          "checking if sort" <+> prettyTCM s' <+>
          "of pi type" <+> prettyTCM v <+>
          "fits in given sort" <+> prettyTCM s
        -- Pi types do not contain enough information to reconstruct their
        -- sort uniquely. Specifically, the pi might have originally been
        -- level-dependent and so ended up in Setω, but now that level
        -- dependency has vanished (in an ideal world we would track the
        -- fact the pi is level dependent in the pi type itself, but
        -- we do not live in an ideal world).
        -- Therefore, the double checker needs to check pi sorts in a relaxed.
        -- way. For simplicity, we over-approximate this by using 'CmpLeq'.
        compareSort CmpLeq s' s
        return v'
      Sort s     -> do
        reportSDoc "tc.check.internal" 30 $ "checking sort" <+> prettyTCM s
        s <- inferInternal' action s
        s' <- inferUnivSort s
        s'' <- shouldBeSort t
        reportSDoc "tc.check.internal" 30 $
          "checking if sort" <+> prettyTCM s' <+>
          "of universe type" <+> prettyTCM v <+>
          "fits in" <+> prettyTCM t
        compareSort cmp s' s''
        return $ Sort s
      Level l    -> do
        l <- inferInternal' action l
        lt <- levelType'
        compareType cmp lt t
        return $ Level l
      DontCare v -> DontCare <$> checkInternal' action v cmp t
      -- Jesper, 2023-02-23: these can appear because of eta-expansion of
      -- records with irrelevant fields
      Dummy s _ -> return v -- __IMPOSSIBLE_VERBOSE__ s

-- | @checkArgInfo actual expected@.
--
--   The @expected@ 'ArgInfo' comes from the type.
--   The @actual@ 'ArgInfo' comes from the term and can be updated
--   by an action.
checkArgInfo :: Action -> ArgInfo -> ArgInfo -> TCM ArgInfo
checkArgInfo action ai ai' = do
  checkHiding    (getHiding ai)     (getHiding ai')
  mod <- checkModality action (getModality ai)  (getModality ai')
  return $ setModality mod ai

checkHiding :: Hiding -> Hiding -> TCM ()
checkHiding h h' = unless (sameHiding h h') $ typeError $ HidingMismatch h h'

-- | @checkRelevance action term type@.
--
--   The @term@ 'Relevance' can be updated by the @action@.
checkModality :: Action -> Modality -> Modality -> TCM Modality
checkModality action mod mod' = do
  let (r,r') = (getRelevance mod, getRelevance mod')
      (q,q') = (getQuantity  mod, getQuantity  mod')
  unless (sameModality mod mod') $ typeError $ if
    | not (sameRelevance r r') -> RelevanceMismatch r r'
    | not (sameQuantity q q')  -> QuantityMismatch  q q'
    | otherwise -> __IMPOSSIBLE__ -- add more cases when adding new modalities
  return $ modalityAction action mod' mod  -- Argument order for actions: @type@ @term@

-- | Infer type of a neutral term.
infer :: Term -> TCM Type
infer u = do
  reportSDoc "tc.check.internal" 20 $ "CheckInternal.infer" <+> prettyTCM u
  case u of
    Var i es -> do
      a <- typeOfBV i
      fst3 <$> inferSpine defaultAction a (Var i) es
    Def f es -> do
      whenJustM (isRelevantProjection f) $ \_ -> nonInferable
      def <- getConstInfo f
      a <- fst3 <$> inferSpine defaultAction (defType def) (Def f) es
      checkCubicalSideCondition def es
      return a
    MetaV x es -> do -- we assume meta instantiations to be well-typed
      a <- metaType x
      fst3 <$> inferSpine defaultAction a (MetaV x) es
    _ -> nonInferable
  where
    nonInferable :: MonadDebug m => m a
    nonInferable = __IMPOSSIBLE_VERBOSE__ $ unlines
      [ "CheckInternal.infer: non-inferable term:"
      , "  " ++ prettyShow u
      ]

instance CheckInternal Elims where
  checkInternal' action es cmp (t , hd) = snd3 <$> inferSpine action t hd es

-- | @inferSpine action t hd es@ checks that spine @es@ eliminates
--   value @hd []@ of type @t@ and returns the remaining type
--   (target of elimination), the transformed eliminations, and the
--   transformed term.
--
--   The transformed term is /not/ simply @hd@ applied to the transformed
--   eliminations: 'elimViewAction' brings prefix applications of
--   projection-like functions into post-fix form, and that has to be undone
--   when rebuilding the term, or we hand back a term in a representation
--   the conversion checker cannot relate to the original one
--   (issues #8336 and #8771).
inferSpine :: Action -> Type -> (Elims -> Term) -> Elims -> TCM (Type, Elims, Term)
inferSpine action t hd es = loop t hd id hd es
  where
  loop t hd accEs accTm = \case
    [] -> return (t , accEs [] , accTm [])
    (e : es) -> do
      let self = hd []
      reportSDoc "tc.check.internal" 30 $ sep
        [ "inferring spine: "
        , "type t = " <+> prettyTCM t
        , "self  = " <+> prettyTCM self
        , "eliminated by e = " <+> prettyTCM e
        ]
      case e of
        IApply x y r -> do
          -- The head can have a function type @(i : I) → A@ instead of
          -- a path type.  The reason: 'etaOnce' (also called by
          -- 'instantiateFull') does not know the type of a lambda, so it
          -- also contracts a path lambda @λ i → f i@ to @f@.  If we then
          -- substitute @f@ for a path variable @p@ in @p i@, we get an
          -- 'IApply' with head @f@.  The conversion checker also accepts
          -- such terms, see 'compareElims'.
          -- Test case: test/Succeed/DoubleCheckEtaContractedPathLambda.agda.
          -- For a head @f@ with a function type, the endpoints are
          -- @f i0@ and @f i1@.
          izero <- primIZero
          ione  <- primIOne
          (a, b, endpoints) <- ifPiTypeB t
            (\ a b -> do
              let at i = self `apply` [Arg (domInfo a) i]
              return (a, b, Just (at izero, at ione)))
            (shouldBePath . ignoreBlocking)
          r' <- checkInternal' action r CmpLeq (unDom a)
          x' <- checkInternal' action x CmpLeq (b `absApp` izero)
          y' <- checkInternal' action y CmpLeq (b `absApp` ione)
          -- Issue #8689: the endpoints stored in the elimination
          -- have to be the endpoints of the head,
          -- because @self i0@ reduces to @x@ and @self i1@ to @y@.
          whenJust endpoints \ (x0, y0) -> do
            equalTerm (b `absApp` izero) x x0
            equalTerm (b `absApp` ione)  y y0
          let e' = IApply x' y' r'
          loop (b `absApp` r) (hd . (e:)) (accEs . (e':)) (accTm . (e':)) es
        Apply (Arg ai v) -> do
          (a, b) <- shouldBePi t
          ai <- checkArgInfo action ai $ domInfo a
          v' <- applyDomToContext a $ checkInternal' action v CmpLeq $ unDom a
          let e' = Apply (Arg ai v')
          loop (b `absApp` v) (hd . (e:)) (accEs . (e':)) (accTm . (e':)) es
        -- case: projection or projection-like
        Proj o f -> do
          t' <- shouldBeProjectible self t o f
          -- Jesper, issue #8336: turn projection-like functions back into Defs.
          -- Andreas, issue #8771: this has to happen for the transformed term
          -- as well, not just for @hd@, or the two get out of sync.
          proj <- fromMaybe __IMPOSSIBLE__ <$> isProjection f
          let applyProj :: (Elims -> Term) -> (Elims -> Term)
              applyProj h
                | isProperProjection_ proj = h . (e:)
                | otherwise = Def f . (Apply (projFromType proj $> h []) :)
          loop t' (applyProj hd) (accEs . (e:)) (applyProj accTm) es

checkSpine ::
     Action
  -> Type       -- ^ Type of the head @self@.
  -> (Elims -> Term) -- ^ The head @hd@.
  -> Elims      -- ^ The eliminations @es@.
  -> Comparison -- ^ Check (@CmpLeq@) or infer (@CmpEq@) the final type.
  -> Type       -- ^ Expected type of the application @self es@.
  -> TCM Term   -- ^ The application after modification by the @Action@.
checkSpine action a hd es cmp t = do
  reportSDoc "tc.check.internal" 20 $ sep
    [ "checking spine "
    , nest 2 $ sep [ parens (sep [ prettyTCM (hd []) <+> ":"
                                 , nest 2 $ prettyTCM a ])
                   , nest 4 $ prettyTCM es <+> ":"
                   , nest 2 $ prettyTCM t ] ]
  (t' , _es' , v') <- inferSpine action a hd es
  (t2, checkEndpoints) <- pathAsFunctionType (hd es) t' t
  reportSDoc "tc.check.internal" 30 $ sep
    [ "checking if "
    , prettyTCM t'
    , "is a subtype of"
    , prettyTCM t2
    ]
  reportSDoc "tc.check.internal" 70 $ sep
    [ "checking if (raw)"
    , pretty =<< instantiate t'
    , "is a subtype of (raw)"
    , pretty =<< instantiate t2
    ]
  coerceSize cmp (hd es) t' t2
  checkEndpoints
  return v'

-- | @pathAsFunctionType v t' t@ changes the expected type @t@ of the
--   term @v@ where the inferred type @t'@ is a function type and @t@ is
--   a path type @PathP A x y@: it replaces the path type by
--   @(i : I) → A i@.  It also does this in the codomains of function
--   types and path types.
--
--   It also returns a check of the endpoints of @v@ for each replaced
--   path type: @v i0 = x : A i0@ and @v i1 = y : A i1@ (issue #8689).
--   For a path lambda, 'checkPathLambdaEndpoints' does the same check.
--   The caller has to run the check after it has compared @t'@ with
--   the new type, because only then is @v i0@ well-typed.
--
--   A term can have a function type @(i : I) → B@ where we expect a
--   path type.  The reason: 'etaOnce' (also called by 'instantiateFull')
--   does not know the type of a lambda, so it also contracts a path
--   lambda @λ i → f i@ to @f@.  The conversion checker accepts such a
--   term at a path type, because it eta-expands terms at a path type
--   (see 'compareTerm'').
--
--   Test case: test/Succeed/DoubleCheckEtaContractedPathLambda.agda.
pathAsFunctionType :: Term -> Type -> Type -> TCM (Type, TCM ())
pathAsFunctionType v t' t =
  -- Path types exist only if 'optCubical' is set (by --cubical or
  -- --erased-cubical).  This option is infective, so imported modules
  -- cannot bring path types into a module without it.
  caseMaybeM (optCubical <$> pragmaOptions) (return (t, return ())) $ \ _ ->
    fromMaybe (t, return ()) <$> loop v t' t
  where
    -- Returns 'Nothing' if there is no path type to replace.
    loop :: Term -> Type -> Type -> TCM (Maybe (Type, TCM ()))
    loop w inferred expected =
      ifNotPiType inferred (\ _ -> return Nothing) $ \ dom' b' -> do
      -- The term under the binder.
      let body = raise 1 w `apply` [Arg (domInfo dom') (var 0)]
      reduce expected >>= \case
        El s (Pi a b) -> do
          m <- addContext (absName b, a) $ loop body (absBody b') (absBody b)
          return $ flip fmap m \ (c, check) ->
            (El s $ Pi a $ Abs (absName b) c, addContext (absName b, a) check)
        u -> (pathViewAsPi'whnf <*> pure u) >>= \case
          Right _ -> return Nothing
          Left ((a, b), (x, y)) -> do
            m <- addContext (absName b, a) $ loop body (absBody b') (absBody b)
            izero <- primIZero
            ione  <- primIOne
            let at i = w `apply` [Arg (domInfo dom') i]
                check = do
                  reportSDoc "tc.check.internal.cubical" 30 $ sep
                    [ "checking endpoints of eta-contracted path lambda"
                    , nest 2 $ prettyTCM w
                    ]
                  equalTerm (b `absApp` izero) (at izero) x
                  equalTerm (b `absApp` ione)  (at ione)  y
                  whenJust m $ addContext (absName b, a) . snd
            return $ Just
              (El (getSort u) $ Pi a $ Abs (absName b) $ maybe (absBody b) fst m, check)

-- * Cubical boundaries and side conditions (issue #8689)

-- The following checks look at the subterms before the 'Action' changes
-- them.  (They see the term after 'preAction' and 'elimViewAction' at
-- the current node, but the recursive calls have not yet changed its
-- subterms.)  The types of subterms come from these unchanged subterms
-- too (see e.g. 'inferSpine').  Thus an 'Action' that replaces
-- subterms, like the one of 'Agda.TypeChecking.Abstract.abstractTerm',
-- does not make these checks fail.

-- | @checkPathLambdaEndpoints b u (x, y)@ checks that the path lambda
--   with body @u@ has the endpoints @x@ and @y@ of its type
--   @PathP (λ i → b) x y@:
--   @u[i0] = x : b[i0]@ and @u[i1] = y : b[i1]@.
--
--   The type checker checks the same in
--   'Agda.TypeChecking.Rules.Term.checkPath'.
checkPathLambdaEndpoints :: Abs Type -> Abs Term -> (Term, Term) -> TCM ()
checkPathLambdaEndpoints b u (x, y) = do
  izero <- primIZero
  ione  <- primIOne
  reportSDoc "tc.check.internal.cubical" 30 $ sep
    [ "checking endpoints of path lambda"
    , nest 2 $ prettyTCM (Lam defaultArgInfo u)
    ]
  equalTerm (b `absApp` izero) (u `absApp` izero) x
  equalTerm (b `absApp` ione)  (u `absApp` ione)  y

-- | Check the side condition of a cubical primitive applied to the
--   eliminations, if the definition is one.
--
--   The arguments of the primitive are the 'Apply' eliminations at
--   the start.  Other eliminations can follow them, for example a
--   projection-like function that 'elimViewAction' put into postfix
--   form.
--
--   The type checker checks these side conditions in
--   'Agda.TypeChecking.Rules.Application.checkHeadApplication'.
--   It rejects a primitive that is not applied to enough arguments.
--   Here we skip the check in this case, as there is nothing to check.
checkCubicalSideCondition :: Definition -> Elims -> TCM ()
checkCubicalSideCondition def es = case theDef def of
  Primitive{ primName } | Just side <- cubicalSideCondition primName ->
    whenJustM (side $ fst $ splitApplyElims es) \ sc -> do
      reportSDoc "tc.check.internal.cubical" 30 $
        "checking side condition of" <+> prettyTCM (Def (defName def) es)
      sideConditionCheck sc
  _ -> return ()

instance CheckInternal Sort where
  checkInternal' action s cmp _ = case s of
    Univ u l -> Univ u <$> inferInternal' action l
    Inf u n  -> return $ Inf u n
    SizeUniv -> return SizeUniv
    LockUniv -> return LockUniv
    LevelUniv -> return LevelUniv
    IntervalUniv -> return IntervalUniv
    PiSort c dom s1 s2 -> do
      let a = unDom dom
      s1' <- inferInternal' action s1
      a' <- checkInternal' action a CmpLeq $ sort s1'
      let dom' = dom $> a'
      s2' <- mapAbstraction (El s1' <$> dom') (inferInternal' action) s2
      return $ PiSort c dom' s1' s2'
    FunSort s1 s2 -> do
      s1' <- inferInternal' action s1
      s2' <- inferInternal' action s2
      return $ FunSort s1' s2'
    UnivSort s -> UnivSort <$> inferInternal' action s
    MetaS x es -> do -- we assume sort meta instantiations to be well-formed
      a <- metaType x
      MetaS x <$> checkInternal' action es cmp (a , Sort . MetaS x)
    DefS d es -> do
      a <- defType <$> getConstInfo d
      DefS d <$> checkInternal' action es cmp (a , Sort . DefS d)
    DummyS s -> __IMPOSSIBLE_VERBOSE__ s

instance CheckInternal Level where
  checkInternal' action (Max n ls) _ _ = Max n <$> mapM (inferInternal' action) ls

instance CheckInternal PlusLevel where
  checkInternal' action (Plus k l) _ _ = Plus k <$> checkLevelAtom l
    where
    checkLevelAtom l = do
      lvl <- levelType'
      checkInternal' action l CmpLeq lvl

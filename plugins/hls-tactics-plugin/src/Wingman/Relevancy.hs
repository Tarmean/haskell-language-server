{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
module Wingman.Relevancy where

import GHC
import UniqSet
import qualified UniqSet as Uniq
import OccName
import Wingman.Types
import Data.List (sortOn, partition)
import Control.Monad.Reader
import Type (varType, splitTyConApp_maybe)
import Data.Maybe (maybeToList, mapMaybe)
import Refinery.Tactic
import Development.IDE (unsafePrintSDoc)
import Outputable (ppr)
import Wingman.GHC
import Data.Generics ( gmapQl, everything, extQ, something )
import Generics.SYB (mkQ)
import Unique
import qualified Data.IntMap as IM
import Data.Function (on)
import Data.Ord (comparing)
import Data.Data (Data)
import           Data.Generics.Labels ()
import SrcLoc (containsSpan)
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.State
import Bag (bagToList)
import Control.Lens
import GHC.Generics (Generic)
import TysWiredIn (anyTyCon)
import qualified Wingman.ArgMatch as ArgMatch
import TyCoRep (Type(..))
import TyCon ( isDataTyCon, tyConName )
import qualified Data.Text as T
import InstEnv (InstEnvs (ie_global, ie_local), instEnvElts, orphNamesOfClsInst, ClsInst (is_cls_nm))
import GhcPlugins (nameSetElemsStable)
type Tags = UniqSet TyCon
data TypTags = TypTags { argCount :: Int, posCtor :: UniqSet TyCon, negCtor :: UniqSet TyCon, constraintTags :: UniqSet TyCon }

-- This is currently dead code because I am experimenting with unification based matching
data PatContext = PatContext {
    resultTags :: Tags,
    appliedCount :: Int,
    appliedTags :: Tags,
    localTags :: Tags,
    localContext :: Tags,
    localConstraints :: Tags,
    resultImpl :: Tags,
    moduleContext :: Tags
}
instance Show PatContext where
    show PatContext {..}
      =  "PatContext { resultTags=" ++  showUS resultTags
      ++ ", applidCount=" ++ show appliedCount
      ++ ", appliedTags=" ++ showUS appliedTags
      ++ ", localTags=" ++ showUS localTags
      ++ ", localContext=" ++ showUS localContext
      ++"}"
        where
          showUS = unsafePrintSDoc . Uniq.pprUniqSet ppr

newtype Freqs = Freqs { getFreqs :: IM.IntMap Int}
observe :: TyCon -> Freqs
observe u = Freqs $ IM.singleton (getKey $ getUnique u) 1
instance Semigroup Freqs where
   Freqs a <> Freqs b = Freqs (IM.unionWith (+) a b)
instance Monoid Freqs where
   mempty = Freqs IM.empty

addTagFreqs :: Tags -> Freqs -> Freqs
addTagFreqs a (Freqs f0) = Freqs $ nonDetFoldUniqSet insSingle f0 a
  where
    insSingle k m = IM.alter inc (getKey $ getUnique k) m
    inc Nothing = Just 1
    inc (Just i) = Just (i+1)
typFreqs :: TypTags -> Freqs
typFreqs (TypTags _ a b c) = foldr addTagFreqs mempty [a,b,c]
zScore :: Freqs -> TyCon -> Double
zScore (Freqs f) = \k -> (getVal k - mean) / stdDev
  where
    getVal k = fromIntegral (IM.findWithDefault 1 (getKey $ getUnique k) f)
    mean :: Double
    mean = fromIntegral (sum $ map (+1) $ IM.elems f) / n
    n = max 1 $ fromIntegral (IM.size f)

    stdDevSqrd = sum [ abs (1+ fromIntegral e - mean) ** 2 | e <- IM.elems f ] / n
    stdDev = sqrt stdDevSqrd
-- myUniqToInt :: UniqSet a -> Int
-- myUniqToInt a = [wingman|guess;assumption|]

-- data Rarity = M.Map Unique Int
instance Show TypTags where
  show (TypTags argCount us us' us2) = "TypTags { argCount= " <> show argCount <> ", posCtor="<> showUS us <> ", negCtor=" <> showUS us' <> ", constraintTags= " <> showUS us2 <> "}"
    where
      showUS = unsafePrintSDoc . Uniq.pprUniqSet ppr
instance Semigroup TypTags where
  (TypTags ac set set' set2) <> (TypTags ac2 set3 set4 set5)
    = TypTags {argCount = max ac ac2, posCtor = set <> set3, negCtor = set' <> set4, constraintTags = set2 <> set5}
instance Monoid TypTags where
  mempty
    = TypTags
        {argCount = 0, posCtor = mempty, negCtor = mempty, constraintTags = mempty}

foo :: ()
foo = ()
  where
    bar :: M.Map Int String -> [String]
    bar m = map show $ bar m

mkPos :: TyCon -> TypTags
mkPos a = mempty { posCtor = unitUniqSet a }
mkNeg :: TyCon -> TypTags
mkNeg a = mempty { negCtor = unitUniqSet a }
mkConstraint :: TyCon -> TypTags
mkConstraint a = mempty { constraintTags = unitUniqSet a }
mkArgCount :: Int -> TypTags
mkArgCount ac = mempty {argCount = ac}
flipTyTags :: TypTags -> TypTags
flipTyTags (TypTags ac a b c) = TypTags {argCount = ac, posCtor = b, negCtor = a, constraintTags = c}

hidePos :: TypTags -> TypTags
hidePos (TypTags _ _ b c) = TypTags {argCount = 0, posCtor = mempty, negCtor = b, constraintTags = c}

gatherTy :: Type -> TypTags
gatherTy  ty
  | (_vars, theta, args@(_:_), res) <- tacticsSplitFunTy ty
  = mkArgCount (length args) <> go res <> hidePos (flipTyTags $ foldMap go args) <> foldMap gatherConstraints theta
  | otherwise = go ty
  where
    go :: Type -> TypTags
    go ty
      | (_vars, _theta, _:_,ks) <- tacticsSplitFunTy ty = mempty -- go ks
      | Just (k,ks) <- splitTyConApp_maybe ty =
        if k == anyTyCon
        then mempty
        else mkPos k <> foldMap go ks
      | otherwise = gmapQl mappend mempty (mkQ mempty go) ty

gatherConstraints :: PredType -> TypTags
gatherConstraints = everything (<>) (mkQ mempty mkConstraint)

-- I've been playing around with a replacement for typed holes that abuses the external package state and GlobalRdrEnv to get a list of types and names. Hopefully whatever is relevant to the current module is already loaded there, but I usually used typed holes to figure out the combinator name in context for something I'm using. Maybe something more hoogle-y or something that uses hiedb would be cleaner, but hiedb doesn't store type signatures and hoogle's heuristics don't quie fit. The idea to search for combinators with similar type constructors as the context from hoogle still works great, though.

--     hole: Maybe (TyCon, Any Type)
--     hyps: [Type,Type -> TypTags]
--     PatContext { resultTags={->, Maybe, TYPE, Any, (,), 'LiftedRep, TyCon, Type}, applidCount=1, appliedTags={Type}, localTags={TypTags, Type}, localContext={}})
--     !!!guess::guesses: [(-86.66666666666667,splitTyConApp_maybe,HasDebugCallStack => Type -> Maybe (TyCon, [Type])),...


-- which then promptly fails to apply because `Any` isn't `[]`. Similar things happen with other default types like Int->Integer.
-- I suppose there might be a way to patch this by rewriting the expected goal type to match the guess when a default is suspected? This very well might be a horrendous idea.
-- The heuristics work very well when the arguments are applied to the hole, 
-- type Score = Double
data ScoreF a = Score { goalCost :: a, unwantedResultCtor :: a, sigNotInLocalCost :: a, ifPolymorphic :: a, argCheck :: a, sTags :: TypTags }
  deriving (Foldable, Show)
getScore :: Score -> Double
getScore = sum
instance Eq Score where
  (==) = (==) `on` getScore
instance Ord Score where
  compare = comparing getScore
type Score = ScoreF Double
scoreTags :: PatContext -> TypTags -> Score
scoreTags goal try
    =
    Score
    { goalCost =  25 * costForGoal,
      unwantedResultCtor = unwantedResult,
      sigNotInLocalCost = 10 *  costSigNotInLocal,
      ifPolymorphic = if hasGoal && isPolymorphic then -5 else 0, -- [NOTE polymorphic bonus]
      argCheck =  enoughArgs,
      sTags = try
    }
    -- + fromIntegral (argCount try)
    -- + 15 * (countArgsNotInSig $ appliedTags goal) / (succ $ fromIntegral $ sizeUniqSet $ appliedTags goal)
  where
    hasGoal :: Bool
    hasGoal = not $ Uniq.isEmptyUniqSet (resultTags goal)
    isPolymorphic = Uniq.isEmptyUniqSet (posCtor try)
    enoughArgs
      | argCount try >= appliedCount goal = 0
      | isPolymorphic = 50
      | otherwise = 9001

    unwantedResult
      | Uniq.isEmptyUniqSet (resultTags goal) = 0
      | all (`Uniq.elementOfUniqSet` resultTags goal) (nonDetEltsUniqSet $ posCtor try) = 0
      | otherwise = 50


    costForGoal = sum [goalResScale a * costForResTag a | a <- nonDetEltsUniqSet (resultTags goal)]
    goalResScale = scaleByArity (resultTags goal)
    costForResTag :: TyCon -> Double
    costForResTag tc
      | Uniq.isEmptyUniqSet (posCtor try) = 0
      | Just _ <- Uniq.lookupUniqSet (posCtor try) tc = -1
      | otherwise = 1

    costSigNotInLocal = sum [sigScale a * costForSigArg a | a <- nonDetEltsUniqSet (negCtor try)]

    sigScale = scaleByArity (negCtor try)
    canTakeExtraArgs = argCount try > appliedCount goal
    costForSigArg :: TyCon -> Double
    costForSigArg tc
      |Just _ <- Uniq.lookupUniqSet (appliedTags goal) tc = -1
      |Just _ <- Uniq.lookupUniqSet (localTags goal) tc
      , canTakeExtraArgs = -0.5
      | otherwise = 10

-- Often, the goal type is our most reliable source of information, especially
-- for top-down development if the user gives nice types. Give it huge influence on the results!
-- But if we can't find a good way to build the result type (because the arguments don't fit)
-- then unusably bad ways to build the result type might win over good ways to consume the
-- arguments, like a fold with a polymorphic result type.
-- Give such polymorphic combinators a consolation price so `UniqSet.foldWithKey` is
-- offered if we need to consume a map even though the result type would give
-- no points and there are other many other ways to build '[String]'!
--
-- But if the type inference breaks down or we are in a do-block, our result type is polymorphic
-- Do not do this if the goal type is ambiguous, though, otherwise we get `forall a. a -> a -> a` nonsense


scaleByArity :: UniqSet TyCon -> TyCon -> Double
scaleByArity us
  | totalSigArity == 0 = const 1
  | otherwise = \x -> arityMult x / totalSigArity
  where
    argsInSig :: [TyCon]
    -- argsInSig = nonDetEltsUniqSet us 
    argsInSig = nonDetEltsUniqSet us
    arityMult :: TyCon -> Double
    arityMult = fromIntegral . succ . tyConArity
    totalSigArity :: Double
    totalSigArity = sum (map arityMult argsInSig)


-- foo :: UniqSet TyCon -> [TyCon]
-- foo us = [wingman|guess|]


scoreContext :: S.Set TyVar  -> [(OccName, CType)] -> [HyInfo CType] -> CType -> [(Double, HyInfo CType, ArgMatch.ParsedMatch)]
scoreContext skolems ls hyps goal
  | traceX "scoreContext ctx" ctx False = undefined
  | otherwise = sortOn (\(a,_,_) -> a) [ (cost, HyInfo candidate UserPrv ct, matches)| (candidate, ct) <- ls, (cost, matches) <- maybeToList (ArgMatch.runMatcher ctx ct) ]
  -- = sortOn (\(a,_,_) -> a) [ ( scoreTags patCtx candidate, n, typ) | (n, typ) <- ls, let candidate = gatherCTy typ ]  where
  --   TypTags { posCtor=localTags } =  foldMap gatherCTy ctx
  --   TypTags {argCount =argCount, posCtor = resTags, negCtor = appliedTags} = gatherCTy goal
  --   patCtx = PatContext resTags argCount appliedTags localTags mempty mempty mempty mempty
  --   gatherCTy (CType c) = gatherTy c
  where
    ctx = ArgMatch.mkContext skolems hyps goal

bestContext :: String -> TacticsM [(Double, HyInfo CType, ArgMatch.ParsedMatch)]
bestContext lab = do
  compItems <- asks ctx_complEnv
  -- traceMX "some tys" $ take 100 $ concatMap (getTy . snd) $ nonDetUFMToList tyEnv
  def <- asks (fmap fst . ctxDefiningFuncs)
  traceMX "curDef " def
  jdg <- goal
  traceM "hyps0"
  traceMX "hyps " (_jHypothesis jdg)
  traceMX "compItems " $  map snd compItems
  let gType = _jGoal jdg

      nonRec RecursivePrv = False
      nonRec (DisallowedPrv _ RecursivePrv) = False
      nonRec _ = True
      hypType = filter (nonRec . hi_provenance) $ unHypothesis $ _jHypothesis jdg
      recHypTypes = S.fromList $ map (show . hi_name) $ filter (not . nonRec . hi_provenance) $ unHypothesis $ _jHypothesis jdg
      tyConsInScope = foldMap (tyCons . unCType .  hi_type) hypType
      (_, _, directArgs, resTy) = tacticsSplitFunTy $ unCType gType
      resCons = tyCons resTy
      dirTyCons = foldMap tyCons directArgs

      appCons
        | null directArgs = resCons <> tyConsInScope
        | otherwise = resCons <> dirTyCons
      checkDirTyCons a = overlaps appCons a
  insts <- asks ctxInstEnvs
  let
     -- maybe normalize so Int doesn't bring in all the scopes?
     instanceTags :: S.Set Name
     instanceTags =
         S.fromList [ is_cls_nm ispec
         | ispec <- instEnvElts (ie_local insts) <> instEnvElts (ie_global insts)
         , n <- nameSetElemsStable $ orphNamesOfClsInst ispec
         , S.member  n appCons
         ]
     fullTags = S.union appCons instanceTags
  traceMX "filter tags" appCons
  traceMX "instance tags" instanceTags
  let
    pairings =
         [ (occ, CType ty)
         | (CType ty, compLab) <- compItems
         , T.pack lab `T.isPrefixOf` compLab
         , overlaps fullTags ty
         , let occ = mkVarOcc (T.unpack compLab)
         , not (show occ `S.member` recHypTypes)
         ]
  let ctx =  pairings
  traceMX "candidate names"  $ map fst ctx
  skolems <- gets ts_skolems
  pure $ scoreContext skolems ctx hypType gType


-- overlaps :: S.Set Name -> Type -> Bool
-- overlaps is t = intersec
overlaps :: S.Set Name -> Type -> Bool
overlaps is t = not $ S.null $ S.intersection is (tyCons t)
tyCons :: Type -> S.Set Name
tyCons (TyVarTy _) = mempty
tyCons (AppTy l r) = S.union (tyCons l) (tyCons r)
tyCons (TyConApp tc tys) = inj tc <> foldMap tyCons tys
  where
    inj a
      | isDataTyCon a = S.singleton (tyConName a)
      | otherwise = mempty
tyCons (ForAllTy _ ty) = tyCons ty
tyCons (FunTy _ ty ty2) = tyCons ty <> tyCons ty2
-- tyCons (FunTy _ _ ty) = tyCons ty
tyCons (LitTy _) = mempty
tyCons (CastTy ty _) = tyCons ty
tyCons (CoercionTy _) = mempty


gatherIds :: Data a => a -> [Id]
gatherIds = everything (<>) (mkQ [] pure)

getVarTy :: Id -> Type
getVarTy = idType

guardLoc :: RealSrcSpan -> GenLocated SrcSpan e -> Maybe e
guardLoc _ (L (UnhelpfulSpan _) _)  = Nothing
guardLoc l (L (RealSrcSpan l') e)
 | l' `containsSpan` l  = Just e
 | otherwise = Nothing
gatherHole :: RealSrcSpan -> HsBindLR GhcTc GhcTc -> [HyInfo CType]
gatherHole inLoc (FunBind _ext _lfundid (MG _xmg lgroups _ori) _co_wrap _ticks)
  | not $ null relevant = bound
  | otherwise = []
  where
    groups :: [LMatch GhcTc (LHsExpr GhcTc)]
    groups = unLoc lgroups
    relevant :: [Match GhcTc (LHsExpr GhcTc)]
    relevant = mapMaybe (guardLoc inLoc) groups
    grabOccName match = occName $ unLoc $ mc_fun (m_ctxt match)
    bound = [HyInfo (occName var) (LocalArgPrv (grabOccName rel)) (CType $ idType var)| rel <- relevant, pat <- m_pats rel, var <- gatherIds (unLoc pat) ]
gatherHole _ _ = []


-- | Readability helper to recurse into each child
-- Combine all results with the monoid action
-- Only recurses in the mismatch case. Allows for easy short-circuiting at each level
--
-- recurse = skipLevel recurse `extQ` case1 `extQ` case2 `extQ` case3 
-- case1 (Foo (Bar a)) = Sum 3
-- case1 a = skipLevel recurse a
--
data AnaState = AS {
        occCount :: M.Map OccName Int, -- ^ How often has this OccName been used?
        holeParents :: S.Set OccName,  -- ^ Direct parents of this hole, using them would be (directly) recursive
        depOnHoleParents :: S.Set OccName, -- contain indirect calls to parents of hole, using them could be mutually recursive
        scopeSet :: M.Map OccName (CType, Provenance) -- more detailed  prov information for occnames in scope
    }
    deriving (Generic)

data AnaConf = AC { bindDepth :: Int, holeLoc :: RealSrcSpan, inScopeAtHole :: S.Set OccName }
    deriving (Generic)
type M = ReaderT AnaConf (State AnaState)


runAna :: Data d => RealSrcSpan -> S.Set OccName -> d -> AnaState
runAna sp s d0 = execState (runReaderT (deepBinds d) (AC 0 sp s)) (AS mempty mempty mempty mempty)
  where
   d :: HsBindLR GhcTc GhcTc
   Just d = something (Nothing `mkQ` guardLoc sp) d0

skipLevel :: (Data a) => (forall d. Data d => d -> M ()) -> a -> M ()
skipLevel = gmapQl (>>) (pure ())

deepBinds :: forall a. (Data a) => a -> M ()
deepBinds = skipLevel deepBinds `extQ` varUsage `extQ` maybeRecBindBag



-- pattern guards, do notations, etc

isLocRelevant :: RealSrcSpan -> GenLocated SrcSpan e -> Bool
isLocRelevant loc lm
  | Just _ <- guardLoc loc lm = True
  | otherwise = False



guessName :: HsBindLR GhcTc GhcTc -> Maybe OccName
guessName (FunBind _ gl _ _ _) = Just $ getOccName gl
guessName PatBind {} = Nothing
guessName (VarBind _ ip _ _) = Just $ getOccName ip
guessName AbsBinds {} = Nothing
guessName (PatSynBind _ _) = Nothing
guessName (XHsBindsLR xhbl) =   noExtCon xhbl

maybeRecBindBag :: LHsBindsLR GhcTc GhcTc -> M ()
maybeRecBindBag hs = do
   hl <- asks holeLoc
   let
      binds :: [LHsBindLR GhcTc GhcTc]
      binds = bagToList hs
      (lrels, lsiblings) = partition (isLocRelevant hl) binds
   forM_ lrels $ \lrel ->
       case guessName (unLoc lrel) of
         Just n -> do
           #holeParents <>= S.singleton n
           #depOnHoleParents <>= S.singleton n
         Nothing -> pure ()
   recBindings (map unLoc lsiblings)
   forM_ lrels $ \lrel -> deepBinds (unLoc lrel)

recBindings :: [HsBindLR GhcTc GhcTc] -> M ()
recBindings ls = do
  initRec <- gets holeParents
  s <- asks inScopeAtHole
  let occs = flip map ls $ \l ->  (guessName l, countUsages s l)
      occsWithName = [(k,v) | (Just k,v) <- occs]
      step :: S.Set OccName -> S.Set OccName
      step s = S.fromList [k | (k,v) <- occsWithName, any (`M.member` v) s ]

      fixRec want have
          | have == have' = have
          | otherwise = fixRec (S.union want have') have'
        where
          have' = step want
      shouldDeclareRecursive = fixRec initRec S.empty

      allUsages = foldr (M.unionWith (+)) M.empty [v | (_,v) <- occs]
  #depOnHoleParents <>= shouldDeclareRecursive
  #occCount %= M.unionWith (+) allUsages
-- handleLExpr :: LHsExpr GhcTc -> M ()
-- handleLExpr = handleLoc
-- handleLMatch :: LMatch GhcTc GhcTc -> M ()
-- handleLMatch = handleLoc
-- handleLoc :: (Data a) => Located a -> ReaderT AnaConf (State AnaState) ()
-- handleLoc s = do
--    loc <- asks holeLoc
--    case guardLoc loc s of
--      Just a -> deepBinds a
--      Nothing -> do
--        onlyUsages s
varUsage :: Id -> M ()
varUsage = onlyUsages
onlyUsages :: Data a => a -> M ()
onlyUsages a = do
    s <- asks inScopeAtHole
    let o = countUsages s a
    #occCount %= M.unionWith (+) o

-- bar :: M.Map Int String -> [String]
-- bar = t


-- ^ takes a set of 'important' identifiers, and counts how often each of them was used
-- If some binding isn't used yet it's more likely that it's relevant at the current hole.
-- So we check which local OccNames are already used in other codeblocks.
-- This data is also used to compute data dependencies and decide which bindings
-- would cause cycles
countUsages :: Data a => S.Set OccName -> a -> M.Map OccName Int
countUsages s = everything (M.unionWith (+)) (mkQ M.empty step)
  where
    step :: Id -> M.Map OccName Int
    step a
      | occName a `S.member` s = M.singleton (occName a) 1
      | otherwise = M.empty

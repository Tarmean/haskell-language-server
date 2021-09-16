{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE DeriveGeneric #-}
module Wingman.ArgMatch where




import Type
import OccName (OccName)
import Control.Monad.State.Strict ( gets, StateT, forM_, execStateT )
import qualified Data.Map.Strict as M
import Wingman.GHC (tryUnifyUnivarsButNotSkolems, tacticsSplitFunTy)
import Control.Lens ((%=), (?=), at, (<+=), use, iso)
import GHC.Generics (Generic)
import Data.Generics.Labels ()
import qualified Data.Set as S
import Wingman.Types (CType(CType, unCType), HyInfo (HyInfo))
import Control.Applicative (empty, Alternative ((<|>)))
import Data.Foldable (asum)
import Control.Monad (replicateM_, guard, when, unless, forM)
import TyCon (TyCon)
import Data.Generics.Schemes (everything)
import Data.Generics (mkQ)
import Data.Maybe (isJust)
import Wingman.Machinery (substCTy)
import Unify (tcUnifyTy)
import Data.Containers.ListUtils (nubOrd)
import Wingman.Debug (traceMX)
import Control.Monad.Trans.Writer
import Data.List.Extra (minimumOn, sortOn)
import Util (ordNub)
import Data.Unique (Unique)
import GhcPlugins (getUnique)
import Data.Data (Data)
import Data.Ord (Down(Down))












-- Goals:
-- - functions with polymorphic result like folds need unification for good matching
-- - constraints should be considered
-- - higher order arguments should be treated specially because they are usually written after the function
-- - if there are two arguments and exactly two locals of that type that is more promising than two arguments and only one local
--
-- Try going full unification and scoring monadically

-- Things in scope, will contain constraints in the future
data InScope = Occ OccName | Arg ArgPos
  deriving (Show, Eq, Ord, Generic, Data)
newtype EnvGroup = EG { unEG :: [(CType, [InScope])] }
  deriving (Show, Generic)
data Context = Ctx { env :: !EnvGroup, appliedCount :: Int, holeTy :: !ResultTy, skolem :: S.Set TyVar }
  deriving Show
type ResultTy = CType
newtype ArgPos = AP Int
  deriving (Eq, Ord, Show, Data)
-- Arguments, most concrete types come first
newtype ArgGroup = AG { unAG :: M.Map CType [ArgPos] }
  deriving Show

type PMatch = [MOcc]
data MOcc = NestedHole CType | Exact InScope
  deriving (Eq, Ord, Show)
data ParsedMatch = PerfectMatch Int [Either CType [OccName]] | ReorderMatch Int Int [PMatch]
  deriving (Show, Eq, Ord, Generic)
unusedCount :: ParsedMatch -> Int
unusedCount PerfectMatch {} = 0
unusedCount (ReorderMatch _ i _)  = i

parseMatch :: Int -> [PMatch] -> ParsedMatch
parseMatch argCount pm
  | Just ls <- traverse withoutPositional noArg
  , checkPerfectArgs = PerfectMatch argCount ls
  | otherwise = ReorderMatch argCount (argCount - usedArgs) pm
  where
    argLen = length pm
    (noArg, args) = splitAt (argLen - argCount) pm
    checkPerfectArgs = length perfectArgs == length args && and (zipWith elem perfectArgs args)
    perfectArgs = [Exact (Arg (AP i)) | i <- [0..argCount-1] ]
    usedArgs = length $ nubOrd [ap | m <- pm, Exact (Arg ap) <- m]

-- either grab the hole types or all occnames that could occur
-- If there are any positional arguments here then they don't follow the
-- application order and we need to lambda abstract
withoutPositional :: PMatch -> Maybe (Either CType [OccName])
withoutPositional pm = gatherOccs pm []
  where
    gatherOccs (Exact (Arg _):_) _ = Nothing
    gatherOccs (Exact (Occ occ):rs) occs = gatherOccs rs (occ : occs)
    gatherOccs (NestedHole ct:rs) _ = foundHole ct rs
    gatherOccs [] occs = Just (Right occs)

    foundHole _ (Exact (Arg _) :_) = Nothing
    foundHole ct (_ :a) = foundHole ct a
    foundHole ct [] = Just (Left ct)

data MState = MState {
    openEnv :: !EnvGroup,
    haveCount :: M.Map CType Int,
    cost :: !Double,
    maxCost :: !Double,
    unifier :: !TCvSubst,
    matchOut :: !(M.Map ArgPos PMatch),
    skolems :: S.Set TyVar
}
  deriving Generic

type M = StateT MState []

mkContext :: S.Set TyVar -> [HyInfo CType] -> CType -> Context
mkContext  skolems hys goal = Ctx eg (M.size dirArgs) (CType res) skolems'
  where
    eg = EG $ M.toList $ M.unionWith (<>) occArgs dirArgs
    occArgs =   M.fromListWith (<>) [(t, [Occ occ]) | HyInfo occ _ t  <- hys]
    dirArgs =  M.fromListWith (<>) [(CType t, [Arg (AP idx)]) |  (idx, t) <- zip [0..] directArg]
    -- FIXME: use theta
    (tyVar, _theta, directArg, res) = tacticsSplitFunTy $ unCType goal

    skolems' = S.union (S.fromList tyVar) skolems


-- TODO: sort by concreteness
runMatcher :: Context -> CType -> Maybe (Double, ParsedMatch)
runMatcher c (CType t) = case execStateT (tellC (thetaCost theta) *> matchArgs c ag (CType res)) (mState0 $ env c) of
               [] -> Nothing
               ls -> Just $  minimumOn fst $ map rateByCost $ take 20 ls
  where
    -- TODO: take constraints into account
    (_vars, theta, args, res) = tacticsSplitFunTy t
    ag =  AG $ M.fromListWith (<>) [(CType t, [AP i]) | (t, i) <- zip args [0..]]
    rateByCost x =
             let parsed =  parseMatch (appliedCount c) [ M.findWithDefault [NestedHole (CType typ)] (AP idx) (matchOut x) | (typ, idx) <- zip args [0..] ]
                 unusedArgs =  unusedCount parsed
             in (cost x + parsedCost parsed + unusedArgCost unusedArgs,parsed)


mState0 :: EnvGroup -> MState
mState0 eg= MState {
    openEnv = eg,
    haveCount = M.fromList [  (k, length vs) | (k, vs) <- unEG eg],
    cost=0,
    maxCost = defMaxCost,
    unifier = emptyTCvSubst,
    matchOut = mempty,
    skolems = mempty
  }
  where defMaxCost = 15

forAltsM_ :: Alternative f => [a] -> (a -> f ()) -> f ()
forAltsM_ ls f = () <$ asum (map f ls)
matchArgs :: Context -> ArgGroup -> ResultTy -> M ()
matchArgs Ctx { holeTy } (AG wantedArgs) resultTy = do
  unify holeTy resultTy
  unless (isPolyTy holeTy || isPolyTy resultTy)
         (tellC uniqMatchCost)

  forM_ (sortByConcrete $ M.toList wantedArgs) $ \(want, poss) -> do
    let wantPoly = isPolyTy want
    orHole resultTy want poss $ do
        EG env <- use #openEnv
        -- traceMX "matchWith" (poss, want, env)
        forAltsM_ (sortByConcrete env) $ \(given, occs) -> do
         -- traceMX "tryMatch" (poss, want, occs, given)
         unify given want
         dropEnv given
         scoreGroups (wantPoly || isPolyTy given) want poss occs

sortByConcrete :: Data a => [a] -> [a]
sortByConcrete = sortOn (Down . length . allTyCons)


-- >>> foo

foo :: [[(Int, Char)]]
foo = (execWriterT $ forM_ [1,2] $ \i -> forAltsM_ ['a', 'b'] $ \j -> tell [(i,j)]) :: [[(Int, Char)]]


dropEnv :: CType -> M ()
dropEnv ct = #openEnv . iso unEG EG  %= filter ((/= ct) . fst)

orHole :: CType -> CType -> [ArgPos] -> M () -> M ()
orHole origGoal ty poss m = m <|> fallBack
  where
   fallBack = do
      when (isJust $ tcUnifyTy (unCType origGoal) (unCType ty)) (tellC 10)
      mapM_ mkHole poss
   mkHole p = do
      -- traceMX "orHole" (ty, p)
      tellC (allMissingCost ty)
      #matchOut . at p ?= [NestedHole ty]

scoreGroups :: Bool -> CType -> [ArgPos] -> [InScope] -> StateT MState [] ()
scoreGroups isPoly ty [p] [o] = do
   -- special case - really prefer this function if there is no branching
   if isTyVarTy $ unCType ty
   then pure ()
   else if isPoly
   then tellC uniqMatchPolyCost
   else tellC uniqMatchCost
   #matchOut . at p ?= [Exact o]
scoreGroups _ typ ps os = do
   forM_ got $ \i -> tellC $ useCost i
   tellC (choiceCost (length ps) (length os))
   replicateM_ missing (tellC $ someMissingCost typ)
   forM_ ps $ \p -> #matchOut . at p ?= (maybeHole <> map Exact os)
  where
    got = take (length ps) os
    missing = length ps - length os

    -- if we have too few arguments, consider the possiblity of leaving a hole for each position
    maybeHole
      | missing > 0 = [NestedHole typ]
      | otherwise =[]

isPolyTy :: CType -> Bool
isPolyTy = null . allTyCons . unCType
allTyCons :: (Data a2) => a2 -> [TyCon]
allTyCons = everything (<>) (mkQ mempty pure)

tellC :: Double -> M ()
tellC a = do
  newCost <- #cost <+= a
  upperBound <- use #maxCost
  guard (newCost <= upperBound)

-- we have more arguments that slots so there is extra nondeterminism
choiceCost :: Int -> Int -> Double
choiceCost wanted got
  | wanted > got = fromIntegral (wanted - got)
  | wanted == got = -2 -- this is adhoc, if useful extract
  | otherwise = 0

-- we have some matches, but too few
-- Would have to use locals non-linearly or generate new arguments
someMissingCost, allMissingCost :: CType -> Double
someMissingCost (CType t)
  | isFunTy t = 0.3
  | otherwise = 4
allMissingCost (CType t)
  | isFunTy t = 0.3
  | otherwise = 4
polyTypeCost :: Double
polyTypeCost = 0.1
useCost :: InScope -> Double
useCost _ = 0
uniqMatchPolyCost :: Double
uniqMatchPolyCost = -3
uniqMatchCost :: Double
uniqMatchCost = -5

thetaCost :: Foldable t => t a -> Double
thetaCost a = 0.1 * fromIntegral (length a)

parsedCost :: ParsedMatch -> Double
parsedCost (PerfectMatch i _)
  | i > 0 = -8
parsedCost _ = 0

unusedArgCost :: Int -> Double
unusedArgCost s = fromIntegral $ s * 50

unify :: CType -> CType -> M ()
unify goal inst0 = do
  when (isPolyTy goal || isPolyTy inst0) (tellC polyTypeCost)
  subst <- use #unifier
  let inst = substCTy subst inst0
  skol <- gets skolems
  -- traceMX "unify" (goal, inst0, inst, skol)
  case tryUnifyUnivarsButNotSkolems skol goal inst of
    Just subst -> do
      -- traceMX "unify succ" (goal, inst, subst)
      #unifier %= unionTCvSubst subst
    Nothing -> do
      -- traceMX "unify failed" (goal, inst)
      empty

-- tc_unify_tys_fg :: Bool
--                 -> (TyVar -> BindFlag)
--                 -> [Type] -> [Type]
--                 -> UnifyResult
-- tc_unify_tys_fg match_kis bind_fn tys1 tys2
--   = do { (env, _) <- tc_unify_tys bind_fn True False match_kis env
--                                   emptyTvSubstEnv emptyCvSubstEnv
--                                   tys1 tys2
--        ; return $ niFixTCvSubst env }
--   where
--     vars = tyCoVarsOfTypes tys1 `unionVarSet` tyCoVarsOfTypes tys2
--     env  = mkRnEnv2 $ mkInScopeSet vars
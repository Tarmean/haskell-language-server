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
import Control.Lens ((%=), (?=), at, (<+=), use)
import GHC.Generics (Generic)
import Data.Generics.Labels ()
import qualified Data.Set as S
import Wingman.Types (CType(CType, unCType), HyInfo (HyInfo))
import Control.Applicative (empty, Alternative ((<|>)))
import Data.Foldable (asum)
import Control.Monad (replicateM_, guard, when, unless)
import Wingman.Debug


-- Goals:
-- - functions with polymorphic result like folds need unification for good matching
-- - constraints should be considered
-- - higher order arguments should be treated specially because they are usually written after the function
-- - if there are two arguments and exactly two locals of that type that is more promising than two arguments and only one local
--
-- Try going full unification and scoring monadically

-- Things in scope, will contain constraints in the future
type InScope = OccName
newtype EnvGroup = EG { unEG :: [(CType, [InScope])] }
  deriving Show
data Context = Ctx { env :: !EnvGroup, holeTy :: !ResultTy, skolem :: S.Set TyVar }
  deriving Show
type ResultTy = CType
newtype ArgPos = AP Int
  deriving (Eq, Ord, Show)
-- Arguments, most concrete types come first
newtype ArgGroup = AG { unAG :: M.Map CType [ArgPos] }
  deriving Show

type Match = [MOcc]
data MOcc = NestedHole CType | Exact InScope
  deriving (Eq, Ord, Show)


data MState = MState {
    openEnv :: !EnvGroup,
    cost :: !Double,
    maxCost :: !Double,
    unifier :: !TCvSubst,
    matchOut :: !(M.Map ArgPos Match),
    skolems :: S.Set TyVar
}
  deriving Generic

type M = StateT MState []

mkContext :: S.Set TyVar -> [HyInfo CType] -> CType -> Context
mkContext  skolems hys goal = Ctx  eg goal skolems
  where
    eg =  EG $ M.toList $ M.fromListWith (<>) [(t, [occ]) | HyInfo occ _ t  <- hys]

-- TODO: sort by concreteness
runMatcher :: Context -> CType -> Maybe (Double, [Match])
runMatcher c (CType t) = case execStateT (matchArgs c ag (CType res)) (mState0 $ env c) of
               (x:_) -> Just (cost x, [ M.findWithDefault [NestedHole (CType typ)] (AP idx) (matchOut x) | (typ, idx) <- zip args [0] ])
               [] -> Nothing
  where
    -- TODO: take constraints into account
    (_vars, _theta, args, res) = tacticsSplitFunTy t
    ag =  AG $ M.fromListWith (<>) [(CType t, [AP i]) | (t, i) <- zip args [0..]]

mState0 :: EnvGroup -> MState
mState0 eg= MState { openEnv = eg, cost=0, maxCost = defMaxCost, unifier = emptyTCvSubst, matchOut = mempty, skolems = mempty }
  where defMaxCost = 15

forAltsM_ :: Alternative f => [a] -> (a -> f ()) -> f ()
forAltsM_ ls f = () <$ asum (map f ls)
matchArgs :: Context -> ArgGroup -> ResultTy -> M ()
matchArgs Ctx { env=EG env, holeTy } (AG wantedArgs) resultTy = do
  unify holeTy resultTy
  forM_ (M.toList wantedArgs) $ \(want, poss) -> do
    orHole want poss $ 
      forAltsM_ env $ \(given, occs) -> do
       unify given want
       scoreGroups want poss occs

orHole :: CType -> [ArgPos] -> M () -> M ()
orHole ty poss m = m <|> mapM_ mkHole poss
  where
   mkHole p = do
      -- traceMX "orHole" (ty, p)
      tellC (allMissingCost ty) 
      #matchOut . at p ?= [NestedHole ty]

scoreGroups :: CType -> [ArgPos] -> [InScope] -> StateT MState [] ()
scoreGroups (CType ty) [p] [o] = do
   unless (isTyVarTy ty) $ tellC uniqMatchCost
   #matchOut . at p ?= [Exact o]
scoreGroups typ ps os = do
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
  | isFunTy t = 0
  | otherwise = 4
allMissingCost (CType t) 
  | isFunTy t = 0
  | otherwise = 4
polyTypeCost :: Double
polyTypeCost = 0.3
useCost :: InScope -> Double
useCost _ = 0
uniqMatchCost :: Double
uniqMatchCost = -5


unify :: CType -> CType -> M ()
unify goal inst = do
  when (isTyVarTy (unCType inst)) (tellC polyTypeCost)
  -- traceMX "unify" (goal, inst)
  skol <- gets skolems
  case tryUnifyUnivarsButNotSkolems skol goal inst of
    Just subst -> do
      #unifier %= unionTCvSubst subst
    Nothing -> empty

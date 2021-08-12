{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

-- | A plugin that uses tactics to synthesize code
module Wingman.Plugin
  ( descriptor
  , tacticTitle
  , TacticCommand (..)
  ) where

import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.Maybe
import           Data.Aeson
import           Data.Data
import           Data.Foldable (for_)
import           Data.Maybe
import qualified Data.Text as T
import           Development.IDE.Core.Shake (IdeState (..), ShakeExtras (clientCapabilities), getIdeOptionsIO)
import           Development.IDE.Core.UseStale (Tracked, TrackedStale(..), unTrack, mapAgeFrom, unsafeMkCurrent, Age (Current))
import           Development.IDE.GHC.Compat
import           Development.IDE.GHC.ExactPrint
import           Generics.SYB.GHC
import           Ide.Types
import           Language.LSP.Server
import           Language.LSP.Types
import           Language.LSP.Types.Capabilities
import           OccName
import           Prelude hiding (span)
import           System.Timeout
import           Wingman.CaseSplit
import           Wingman.EmptyCase
import           Wingman.GHC
import           Wingman.Judgements (jNeedsToBindArgs)
import           Wingman.LanguageServer
import           Wingman.LanguageServer.Metaprogram (hoverProvider)
import           Wingman.LanguageServer.TacticProviders
import           Wingman.Machinery (scoreSolution)
import           Wingman.Range
import           Wingman.StaticPlugin
import           Wingman.Tactics
import           Wingman.Types
import qualified Language.LSP.Server as LSP
import qualified Data.Set as Set
import qualified Data.Map as Map
import Development.IDE.Plugin.Completions.Types (anyQualCompls, getCompletionsConfig)
import qualified Language.LSP.VFS                             as VFS
import Development.IDE
    ( uriToFilePath',
      toNormalizedFilePath',
      useWithStaleFast,
      GetParsedModule(GetParsedModule),
      runIdeAction )
import Development.IDE.Plugin.Completions (LocalCompletions(LocalCompletions), NonLocalCompletions (NonLocalCompletions))
import qualified Ide.Plugin.Config as Plugin
import Control.Applicative (Alternative(empty))
import Language.LSP.Types (TextDocumentEdit(_textDocument), DocumentSymbolOptions (_label))
import qualified Data.Map as M


descriptor :: PluginId -> PluginDescriptor IdeState
descriptor plId = (defaultPluginDescriptor plId)
  { pluginCommands
      = mconcat
          [ fmap (\tc ->
              PluginCommand
                (tcCommandId tc)
                (tacticDesc $ tcCommandName tc)
                (tacticCmd (commandTactic tc) plId))
                [minBound .. maxBound]
          , pure $
              PluginCommand
              emptyCaseLensCommandId
              "Complete the empty case"
              workspaceEditHandler
          ]
  , pluginHandlers = mconcat
      [ mkPluginHandler STextDocumentCodeAction codeActionProvider
      , mkPluginHandler STextDocumentCodeLens codeLensProvider
      , mkPluginHandler STextDocumentHover hoverProvider
      , mkPluginHandler STextDocumentCompletion getCompletionsWingman
      ]
  , pluginRules = wingmanRules plId
  , pluginConfigDescriptor =
      defaultConfigDescriptor {configCustomConfig = mkCustomConfig properties}
  , pluginModifyDynflags = staticPlugin
  }


codeActionProvider :: PluginMethodHandler IdeState TextDocumentCodeAction
codeActionProvider state plId (CodeActionParams _ _ (TextDocumentIdentifier uri) (unsafeMkCurrent -> range) _ctx)
  | Just nfp <- uriToNormalizedFilePath $ toNormalizedUri uri = do
      cfg <- getTacticConfig plId
      liftIO $ fromMaybeT (Right $ List []) $ do
        HoleJudgment{..} <- judgementForHole state nfp range cfg
        actions <- lift $
          -- This foldMap is over the function monoid.
          foldMap commandProvider [minBound .. maxBound] $ TacticProviderData
            { tpd_dflags = hj_dflags
            , tpd_config = cfg
            , tpd_plid   = plId
            , tpd_uri    = uri
            , tpd_range  = range
            , tpd_jdg    = hj_jdg
            , tpd_hole_sort = hj_hole_sort
            }
        pure $ Right $ List actions
codeActionProvider _ _ _ = pure $ Right $ List []


showUserFacingMessage
    :: MonadLsp cfg m
    => UserFacingMessage
    -> m (Either ResponseError a)
showUserFacingMessage ufm = do
  showLspMessage $ mkShowMessageParams ufm
  pure $ Left $ mkErr InternalError $ T.pack $ show ufm


tacticCmd
    :: (T.Text -> TacticsM ())
    -> PluginId
    -> CommandFunction IdeState TacticParams
tacticCmd tac pId state (TacticParams uri range var_name)
  | Just nfp <- uriToNormalizedFilePath $ toNormalizedUri uri = do
      let stale a = runStaleIde "tacticCmd" state nfp a

      ccs <- getClientCapabilities
      cfg <- getTacticConfig pId
      res <- liftIO $ runMaybeT $ do
        HoleJudgment{..} <- judgementForHole state nfp range cfg
        let span = fmap (rangeToRealSrcSpan (fromNormalizedFilePath nfp)) hj_range
        TrackedStale pm pmmap <- stale GetAnnotatedParsedSource
        pm_span <- liftMaybe $ mapAgeFrom pmmap span
        let t = tac var_name

        timingOut (cfg_timeout_seconds cfg * seconds) $ do
          res <- liftIO $ runTactic hj_ctx hj_jdg t
          pure $ join $ case res of
            Left errs ->  do
              traceMX "errs" errs
              Left TacticErrors
            Right rtr ->
              case rtr_extract rtr of
                L _ (HsVar _ (L _ rdr)) | isHole (occName rdr) ->
                  Left NothingToDo
                _ -> pure $ mkTacticResultEdits pm_span hj_dflags ccs uri pm rtr

      case res of
        Nothing -> do
          showUserFacingMessage TimedOut
        Just (Left ufm) -> do
          showUserFacingMessage ufm
        Just (Right edit) -> do
          _ <- sendRequest
            SWorkspaceApplyEdit
            (ApplyWorkspaceEditParams Nothing edit)
            (const $ pure ())
          pure $ Right Null
tacticCmd _ _ _ _ =
  pure $ Left $ mkErr InvalidRequest "Bad URI"


------------------------------------------------------------------------------
-- | The number of microseconds in a second
seconds :: Num a => a
seconds = 1e6


timingOut
    :: Int  -- ^ Time in microseconds
    -> IO a    -- ^ Computation to run
    -> MaybeT IO a
timingOut t m = MaybeT $ timeout t m


mkErr :: ErrorCode -> T.Text -> ResponseError
mkErr code err = ResponseError code err Nothing


------------------------------------------------------------------------------
-- | Turn a 'RunTacticResults' into concrete edits to make in the source
-- document.
mkTacticResultEdits
    :: Tracked age RealSrcSpan
    -> DynFlags
    -> ClientCapabilities
    -> Uri
    -> Tracked age (Annotated ParsedSource)
    -> RunTacticResults
    -> Either UserFacingMessage WorkspaceEdit
mkTacticResultEdits (unTrack -> span) dflags ccs uri (unTrack -> pm) rtr = do
  for_ (rtr_other_solns rtr) $ \soln -> do
    traceMX "other solution" $ syn_val soln
    traceMX "with score" $ scoreSolution soln (rtr_jdg rtr) []
  traceMX "solution" $ rtr_extract rtr
  mkWorkspaceEdits dflags ccs uri pm $ graftHole (RealSrcSpan span) rtr


------------------------------------------------------------------------------
-- | Graft a 'RunTacticResults' into the correct place in an AST. Correctly
-- deals with top-level holes, in which we might need to fiddle with the
-- 'Match's that bind variables.
graftHole
    :: SrcSpan
    -> RunTacticResults
    -> Graft (Either String) ParsedSource
graftHole span rtr
  | _jIsTopHole (rtr_jdg rtr)
      = genericGraftWithSmallestM
            (Proxy @(Located [LMatch GhcPs (LHsExpr GhcPs)])) span
      $ \dflags matches ->
          everywhereM'
            $ mkBindListT $ \ix ->
              graftDecl dflags span ix $ \name pats ->
              splitToDecl
                (case not $ jNeedsToBindArgs (rtr_jdg rtr) of
                   -- If the user has explicitly bound arguments, use the
                   -- fixity they wrote.
                   True -> matchContextFixity . m_ctxt . unLoc
                             =<< listToMaybe matches
                   -- Otherwise, choose based on the name of the function.
                   False -> Nothing
                )
                (occName name)
            $ iterateSplit
            $ mkFirstAgda (fmap unXPat pats)
            $ unLoc
            $ rtr_extract rtr
graftHole span rtr
  = graft span
  $ rtr_extract rtr


matchContextFixity :: HsMatchContext p -> Maybe LexicalFixity
matchContextFixity (FunRhs _ l _) = Just l
matchContextFixity _ = Nothing


------------------------------------------------------------------------------
-- | Helper function to route 'mergeFunBindMatches' into the right place in an
-- AST --- correctly dealing with inserting into instance declarations.
graftDecl
    :: DynFlags
    -> SrcSpan
    -> Int
    -> (RdrName -> [Pat GhcPs] -> LHsDecl GhcPs)
    -> LMatch GhcPs (LHsExpr GhcPs)
    -> TransformT (Either String) [LMatch GhcPs (LHsExpr GhcPs)]
graftDecl dflags dst ix make_decl (L src (AMatch (FunRhs (L _ name) _ _) pats _))
  | dst `isSubspanOf` src = do
      L _ dec <- annotateDecl dflags $ make_decl name pats
      case dec of
        ValD _ (FunBind { fun_matches = MG { mg_alts = L _ alts@(first_match : _)}
                  }) -> do
          -- For whatever reason, ExactPrint annotates newlines to the ends of
          -- case matches and type signatures, but only allows us to insert
          -- them at the beginning of those things. Thus, we need want to
          -- insert a preceeding newline (done in 'annotateDecl') on all
          -- matches, except for the first one --- since it gets its newline
          -- from the line above.
          when (ix == 0) $
            setPrecedingLinesT first_match 0 0
          pure alts
        _ -> lift $ Left "annotateDecl didn't produce a funbind"
graftDecl _ _ _ _ x = pure $ pure x


-- foo :: Int -> M.Map Int String -> String
-- foo i m = min

--     baz :: a -> Tracked 'Current a
--     baz a = unsafeMkCurrent a
-- -- -- foo p = _end p
-- | Generate code actions.
-- LocalCompletions
-- NonLocalCompletions
getCompletionsWingman
    :: IdeState
    -> PluginId
    -> CompletionParams
    -> LSP.LspM  Plugin.Config (Either ResponseError (ResponseResult TextDocumentCompletion))
getCompletionsWingman state pId
  CompletionParams{_textDocument=TextDocumentIdentifier uri
                  ,_position=pos
                  ,_context=_completionContext}
  | Just nfp <- uriToNormalizedFilePath $ toNormalizedUri uri = do
      cfg <- getTacticConfig pId
      mres <- liftIO $ runMaybeT $ do
        traceMX "Wingman::completion" nfp
        (word, HoleJudgment{..}) <- judgementFor state nfp (unsafeMkCurrent $ Range (pos{_character = _character pos - 1}) pos) cfg
        traceMX "Wingman::hole" hj_jdg
        let t = guess 10 (show word)

        timingOut (cfg_timeout_seconds cfg * seconds) $ do
          res <- liftIO $ runTactic hj_ctx hj_jdg t
          pure $ join $ case res of
            Left errs ->  do
              traceMX "errs" errs
              Left TacticErrors
            Right rtr ->
              case rtr_extract rtr of
                L _ (HsVar _ (L _ rdr)) | isHole (occName rdr) ->
                  Left NothingToDo
                _ -> do
                  pure $ Right $ InL $ List $ mkCompletions rtr
      case mres of
       Just (Right a) -> pure $ Right a
       _ -> pure $ Right $ InL $ List []
getCompletionsWingman _ _ _ = pure $ Left $ mkErr InvalidRequest "Bad URI"


mkCompletions :: RunTacticResults  -> [CompletionItem]
mkCompletions r = map mkCompletion ( rtr_extract r : (map syn_val $ rtr_other_solns r ))
  where
   mkCompletion :: LHsExpr GhcPs -> CompletionItem
   mkCompletion ci = CompletionItem
                  {_label = text,
                   _kind = Just CiText,
                   _tags = Nothing,
                   _detail = Nothing,
                   _documentation = Nothing,
                   _deprecated = Nothing,
                   _preselect = Nothing,
                   _sortText = Just ("aaa" <> text),
                   _filterText = Nothing,
                   _insertText = Just text,
                   _insertTextFormat = Just Snippet,
                   _insertTextMode = Nothing,
                   _textEdit = Nothing,
                   _additionalTextEdits = Nothing,
                   _commitCharacters = Nothing,
                   _command = Nothing,
                   _xdata = Nothing}
     where
        text = T.pack $ show (unLoc ci)


{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE CPP #-}
module DumpCore(plugin) where

import GhcPlugins hiding (TB)
import Unique(unpkUnique)
import Demand
import Outputable
import CoreStats
import CoreMonad(getHscEnv)
import HscTypes(CgGuts(..))


import qualified Data.Aeson as JS
import qualified Data.Aeson.Types as JS
import           Data.Aeson ((.=), ToJSON(toJSON))
import           Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Char8 as BS8
import           Data.Maybe(mapMaybe)
import           MonadLib
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Control.Monad(unless)
import           System.FilePath
import           System.Directory

import Paths_dump_core

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todo =
  return (todo ++ [ CoreDoPluginPass "DumpCore" (liftIO . dumpIn opts) ])

dumpIn :: [CommandLineOption] -> ModGuts -> IO ModGuts
dumpIn opts guts =
  do let mod        = cvtM guts
         file       = moduleNameString (moduleName (mg_module guts))
         htmlDir    = case opts of
                        []    -> "dump-core"
                        x : _ -> x

     installLibFiles htmlDir

     let jsDir = htmlDir </> "js"
     createDirectoryIfMissing True jsDir

     let js_file = jsDir </> file <.> "js"
     BS.writeFile js_file ("var it = " `BS.append` JS.encode mod)

     -- The wrapper assumes `js` and `lib` as sub-directories of html
     let html_file  = htmlDir </> file <.> "html"
     BS8.writeFile html_file (htmlWrapper file)

     return guts


installLibFiles :: FilePath -> IO ()
installLibFiles libDir =
  mapM_ (copyLibFile libDir) [ "ui/see.js"
                             , "ui/see.css"
                             , "ui/jquery.js"
                             , "ui/fonts/FiraMono-Regular.ttf"
                             , "ui/fonts/FiraMono-Bold.ttf" ]

copyLibFile :: FilePath -> FilePath -> IO ()
copyLibFile outDir file =
  do path <- getDataFileName file
     let outFile = outDir </> file
     done <- doesFileExist outFile
     unless done $ do createDirectoryIfMissing True (takeDirectory outFile)
                      copyFile path outFile


--------------------------------------------------------------------------------

type CvtM = ReaderT RO (StateT Int Maybe)

data RO = RO
  { roVars :: Map Var V    -- ^ Mapping from GHC vars to V
  , roTxt  :: Map Text Int -- ^ how many times is this string in scope
  }


data M = M Module [TB]

data E = EVar V
       | EGlob Var
       | ELit Literal
       | EApp E [E]
       | ELam [BindVar] E
       | ELet B E
       | ECase E BindVar [A]

data V       = V Int Var Text
data BindVar = BindVar Int BindingSite Var Text

data A  = A AltCon [BindVar] E
data B  = B Bool [(BindVar,E)]
data TB = TB Bool [(BindVar,CoreStats,E)]

cvtM :: ModGuts -> M
cvtM gs = M (mg_module gs) (foldr jn [] bs)
  where
  jn (TB False xs) (TB False ys : more) = TB False (xs ++ ys) : more
  jn x y                                = x : y

  mkBV x = BindVar 0 LetBind x (txtName x)

  mkBind (NonRec x _) = [mkBV x]
  mkBind (Rec xs)     = map (mkBV . fst) xs

  act = let bs = map mkBind (mg_binds gs)
        in withBindVars (concat bs) $ \_ -> mapM cvtTB (mg_binds gs)

  ro0 = RO { roVars = Map.empty, roTxt = Map.empty }
  bs  = case runStateT 1 (runReaderT ro0 act) of
               Nothing    -> []
               Just (a,_) -> a

txtName :: Var -> Text
txtName = Text.pack . occNameString . nameOccName . varName



newBindVar :: BindingSite -> Var -> CvtM BindVar
newBindVar bs v =
  do i <- sets $ \i -> (i,i+1)
     return (BindVar i bs v "")

withBindVar :: BindVar -> (BindVar -> CvtM a) -> CvtM a
withBindVar b@(BindVar i s v _) m =
  do scope <- ask
     let txt = txtName v
         nm = case mp Map.! txt of
                1 -> txt
                n -> txt `Text.append` Text.pack ("_" ++ show n)
         mp = Map.insertWith (+) txt 1 (roTxt scope)
         ro = RO { roVars = Map.insert v (V i v nm) (roVars scope)
                 , roTxt  = mp
                 }
     local ro (m (BindVar i s v nm))

withBindVars :: [BindVar] -> ([BindVar] -> CvtM a) -> CvtM a
withBindVars bs m =
  case bs of
    []     -> m []
    x : xs -> withBindVar  x  $ \x1 ->
              withBindVars xs $ \xs1 -> m (x1:xs1)


cvtE :: CoreExpr -> CvtM E
cvtE expr =
  case expr of

    Var x ->
      do scope <- ask
         case Map.lookup x (roVars scope) of
           Nothing -> return (EGlob x)
           Just v  -> return (EVar v)

    Lit l -> return (ELit l)

    App {} -> cvtApp expr []

    Lam x e
      | isTyVar x -> cvtE e
      | otherwise ->
        do b <- newBindVar LambdaBind x
           withBindVar b $ \b1 ->
             do e' <- cvtE e
                case e' of
                  ELam xs e'' -> return (ELam (b1:xs) e'')
                  _ -> return (ELam [b1] e')

    Let b e ->
      do B isRec defs <- cvtB b
         withBindVars (map fst defs) $ \defs1 ->
            do let newDefs = zip defs1 (map snd defs)
               e' <- cvtE e
               case e' of
                 ELet (B False moreDefs) e'' | not isRec ->
                    return (ELet (B False (newDefs ++ moreDefs)) e'')
                 _ -> return (ELet (B isRec newDefs) e')

    Case e x _ as ->
      do e'  <- cvtE e
         x'  <- newBindVar CaseBind x
         withBindVar x' $ \x1 -> do as' <- mapM cvtA as
                                    return (ECase e' x1 as')

    Cast x _    -> cvtE x

    Tick _ e    -> cvtE e

    Type _      -> inBase Nothing

    Coercion _  -> inBase Nothing


cath :: CvtM a -> CvtM (Maybe a)
cath m =
  do r <- ask
     s <- get
     case runStateT s (runReaderT r m) of
       Nothing -> return Nothing
       Just (a,s1) -> set s1 >> return (Just a)

cvtTB :: CoreBind -> CvtM TB
cvtTB b =
  case b of
    NonRec x e -> do b' <- cvtSE (x,e)
                     return (TB False [b'])
    Rec cs     -> do bs' <- mapM cvtSE cs
                     return (TB True bs')
  where
  cvtSE (x,e) = do scope <- ask
                   let V i v t = roVars scope Map.! x
                   e' <- cvtE e
                   return (BindVar i LetBind v t, exprStats e, e')

cvtB :: CoreBind -> CvtM B
cvtB bnd =
  case bnd of
    NonRec x e -> do x' <- newBindVar LetBind x
                     e' <- cvtE e
                     return (B False [(x',e')])
    Rec xs ->
      do bs <- mapM (newBindVar LetBind) (map fst xs)
         withBindVars bs $ \bs1 ->
           do es' <- mapM (cvtE . snd) xs
              return (B True (zip bs1 es'))


cvtA :: CoreAlt -> CvtM A
cvtA (con,bs,e) =
  do xs <- mapM (newBindVar CaseBind) bs
     withBindVars xs $ \xs1 -> do e' <- cvtE e
                                  return (A con xs1 e')

cvtApp :: CoreExpr -> [E] -> CvtM E
cvtApp (App x y) rest =
  do mb <- cath (cvtE y)
     case mb of
       Nothing -> cvtApp x rest
       Just y' -> cvtApp x (y' : rest)
cvtApp e rest =
  do e' <- cvtE e
     case rest of
       [] -> return e'
       _  -> return (EApp e' rest)

--------------------------------------------------------------------------------


--------------------------------------------------------------------------------

tag :: Text -> [JS.Pair] -> JS.Value
tag x xs = JS.object ("tag" .= x : xs)

jsText :: Text -> JS.Value
jsText = toJSON

jsOut :: Outputable a => a -> JS.Value
jsOut = toJSON . showSDocUnsafe . ppr

jsBinder :: Var -> JS.Value
jsBinder v =
  JS.object
    [ "poly" .= map jsOut qVars
    , "args" .= zipWith jsArg args sArgs
    , "term" .= jsOut sRes
    , "result" .= jsOut (mkFunTys otherArgs rest)
    , "usage" .= JS.object
                   [ "demand"  .= jsOut (demandInfo info)
                   , "occ"     .= jsOut (occInfo info)
                   , "callAr"  .= callArityInfo info
                   , "oneShot" .= jsOut (oneShotInfo info)
                   ]
    ]

  where
  ty               = idType v
  (qVars,tyBody)   = splitForAllTys ty
  (allArgs,rest)   = splitFunTys tyBody

  (args,otherArgs) = splitAt (arityInfo info) allArgs

  info             = idInfo v
  (sArgs,sRes) = splitStrictSig (strictnessInfo info)

  jsArg t i = JS.object [ "type"   .= jsOut t
                        , "strict" .= jsOut (getStrDmd i) -- XXX
                        , "use"    .= jsOut (getUseDmd i) -- XXX
                        ]

instance ToJSON OccInfo where
  toJSON = jsOut

instance ToJSON StrictSig where
  toJSON = jsOut

instance ToJSON M where
  toJSON (M m bs) = JS.object [ "mod" .= m, "binds" .= bs ]

instance ToJSON Module where
  toJSON = toJSON . moduleNameString . moduleName

instance ToJSON TB where
  toJSON (TB rec xs) = JS.object [ "rec"   .= rec
                                 , "binds"  .= map js xs ]
    where js (x,s,e) = JS.object [ "var" .= x, "def" .= e
                                 , "terms" .= cs_tm s ]




instance ToJSON B where
  toJSON (B rec xs) = JS.object [ "rec"   .= rec
                              , "binds" .= map js xs ]
    where js (x,e) = JS.object [ "var" .= x, "def" .= e ]

instance ToJSON Var where
  toJSON v = JS.object [ "name" .= varName v
                       , "id" .= (x : '-' : show y)
                       , "info" .= jsOut v
                       , "module" .= nameModule_maybe (varName v)
                       ]
    where (x,y) = unpkUnique (varUnique v)

instance ToJSON V where
  toJSON (V i v t) = JS.object [ "name" .= t, "id" .= mkId i v ]

instance ToJSON BindVar where
   toJSON (BindVar i s v t) =
    JS.object [ "name" .= t
              , "id" .= mkId i v
              , "info" .= if isId v then jsBinder v else JS.Null
              ]

mkId :: Int -> Var -> String
mkId i v = x : '-' : show i ++ ['-'] ++ show y
  where
  (x,y) = unpkUnique (varUnique v)

instance ToJSON Name where
  toJSON = toJSON . nameOccName

instance ToJSON OccName where
  toJSON = toJSON . Text.pack . occNameString

instance ToJSON E where
  toJSON expr =
   case expr of
     EVar i       -> tag "Var"  [ "var" .= i ]
     EGlob i      -> tag "Glob" [ "var" .= i ]
     ELit l       -> tag "Lit" [ "lit" .= l ]
     EApp e as    -> tag "App" [ "fun" .= e, "args" .= as ]
     ELam xs e    -> tag "Lam" [ "args" .= xs, "body" .= e ]
     ELet x e     -> tag "Let" [ "defs" .= x, "body" .= e ]
     ECase e x as -> tag "Case" [ "expr" .= e , "val" .= x
                                , "alts" .= as ]


instance ToJSON A where
  toJSON (A c bs e) = JS.object [ "con" .= c
                                , "binds" .= bs, "rhs" .= e ]

instance ToJSON AltCon where
  toJSON con =
    case con of
      DataAlt x -> tag "DataAlt" [ "con" .= x ]
      LitAlt x  -> tag "LitAlt" [ "lit" .= x ]
      DEFAULT   -> tag "DEFAULT" []

instance ToJSON Literal where
  toJSON lit =
    case lit of
      MachChar c -> mk "char" (show c)
      MachStr bs -> mk "string" (show bs)
      MachNullAddr -> mk "null" ""
#if __GLASGOW_HASKELL__ < 806
      MachInt i -> mk "int" (show i)
      MachInt64 i -> mk "int64" (show i)
      MachWord i -> mk "word" (show i)
      MachWord64 i -> mk "word64" (show i)
      LitInteger i _t -> mk "integer" (show i)
#else
      LitNumber num_type i _t ->
        case num_type of
          LitNumInteger -> mk "integer" (show i)
          LitNumNatural -> mk "natural" (show i)
          LitNumInt -> mk "int" (show i)
          LitNumInt64 -> mk "int64" (show i)
          LitNumWord -> mk "word" (show i)
#endif
      MachFloat r -> mk "float" (show r)
      MachDouble r -> mk "double" (show r)
      MachLabel fs _ _ -> mk "label" (show fs)

    where
    mk :: Text -> String -> JS.Value
    mk x s = JS.object [ "lit" .= s, "type" .= x ]

instance ToJSON DataCon where
  toJSON x = JS.object [ "name" .= nm, "module" .= nameModule_maybe nm ]
    where nm = dataConName x

-------------------------------------------------------------------------------

htmlWrapper :: String -> BS8.ByteString
htmlWrapper name = BS8.unlines
  [ "<!DOCTYPE html>"
  , "<html>"
  , "<head>"
  , "<script src=\"ui/jquery.js\"></script>"
  , BS8.concat [ "<script src=\"js/", BS8.pack name, ".js\"></script>" ]
  , "<script src=\"ui/see.js\"></script>"
  , "<link href=\"ui/see.css\" rel=\"stylesheet\">"
  , "<script>"
  , "$(document).ready(function() {"
  , "  var b = $('body')"
  , "  b.append(seeMod(it))"
  , "})"
  , "</script>"
  , "</head>"
  , "<body>"
  , "<div id=\"all-details\">"
  , "<div id=\"details-short\"></div>"
  , "<div id=\"details-long\"></div>"
  , "</div>"
  , "</body>"
  , "</html>"
  ]

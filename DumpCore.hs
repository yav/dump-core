{-# LANGUAGE OverloadedStrings #-}
module DumpCore(plugin) where

import GhcPlugins hiding (TB)
import Unique(unpkUnique)
import Demand
import Outputable
import CoreStats


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

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo =
  do reinitializeGlobals
     return (todo ++ [ CoreDoPluginPass "DumpCore" pass ])

pass ::  PluginPass
pass guts =
  do df <- getDynFlags
     let mod = cvtM guts
         f   = moduleNameString (moduleName (mg_module guts)) ++ ".js"
         js  = JS.encode mod
     liftIO (BS.writeFile f ("var it = " `BS.append` js))
     return guts


type CvtM = ReaderT (Map Var V) (StateT Int Maybe)



data M = M Module [TB]

data E = EVar V
       | EGlob Var
       | ELit Literal
       | EApp E [E]
       | ELam [BindVar] E
       | ELet B E
       | ECase E BindVar [A]

data V       = V Int Var
data BindVar = BindVar Int BindingSite Var

data A  = A AltCon [BindVar] E
data B  = B Bool [(BindVar,E)]
data TB = TB Bool [(BindVar,CoreStats,E)]

cvtM :: ModGuts -> M
cvtM gs = M (mg_module gs) (foldr jn [] bs)
  where
  jn (TB False xs) (TB False ys : more) = TB False (xs ++ ys) : more
  jn x y                                = x : y

  mkBV = BindVar 0 LetBind

  mkBind (NonRec x _) = [mkBV x]
  mkBind (Rec xs)     = map (mkBV . fst) xs

  act = let bs = map mkBind (mg_binds gs)
        in withBindVars (concat bs) (mapM cvtTB (mg_binds gs))

  bs = case runStateT 1 (runReaderT Map.empty act) of
        Nothing    -> []
        Just (a,_) -> a



newBindVar :: BindingSite -> Var -> CvtM BindVar
newBindVar bs v =
  do i <- sets $ \i -> (i, i + 1)
     return (BindVar i bs v)

withBindVar :: BindVar -> CvtM a -> CvtM a
withBindVar b@(BindVar i _ v) m =
  do scope <- ask
     local (Map.insert v (V i v) scope) m

withBindVars :: [BindVar] -> CvtM a -> CvtM a
withBindVars bs m = foldr withBindVar m bs


cvtE :: CoreExpr -> CvtM E
cvtE expr =
  case expr of

    Var x ->
      do scope <- ask
         case Map.lookup x scope of
           Nothing -> return (EGlob x)
           Just v  -> return (EVar v)

    Lit l -> return (ELit l)

    App {} -> cvtApp expr []

    Lam x e
      | isTyVar x -> cvtE e
      | otherwise ->
        do b <- newBindVar LambdaBind x
           withBindVar b $
             do e' <- cvtE e
                case e' of
                  ELam xs e'' -> return (ELam (b:xs) e'')
                  _ -> return (ELam [b] e')

    Let b e ->
      do B isRec defs <- cvtB b
         withBindVars (map fst defs) $
            do e' <- cvtE e
               case e' of
                 ELet (B False moreDefs) e'' | not isRec ->
                    return (ELet (B False (defs ++ moreDefs)) e'')
                 _ -> return (ELet (B isRec defs) e')

    Case e x _ as ->
      do e'  <- cvtE e
         x'  <- newBindVar CaseBind x
         as' <- withBindVar x' (mapM cvtA as)
         return (ECase e' x' as')

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
  cvtSE (x,e) = do mp <- ask
                   let V i v = mp Map.! x
                   e' <- cvtE e
                   return (BindVar i LetBind v, exprStats e, e')

cvtB :: CoreBind -> CvtM B
cvtB bnd =
  case bnd of
    NonRec x e -> do x' <- newBindVar LetBind x
                     e' <- cvtE e
                     return (B False [(x',e')])
    Rec xs ->
      do bs <- mapM (newBindVar LetBind) (map fst xs)
         withBindVars bs $
           do es' <- mapM (cvtE . snd) xs
              return (B True (zip bs es'))


cvtA :: CoreAlt -> CvtM A
cvtA (con,bs,e) =
  do xs <- mapM (newBindVar CaseBind) bs
     withBindVars xs $ do e' <- cvtE e
                          return (A con xs e')

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
  toJSON (V i v) = JS.object [ "name" .= varName v, "id" .= mkId i v ]

instance ToJSON BindVar where
   toJSON (BindVar i s v) =
    JS.object [ "name" .= varName v
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
      MachInt i -> mk "int" (show i)
      MachInt64 i -> mk "int64" (show i)
      MachWord i -> mk "word" (show i)
      MachWord64 i -> mk "word64" (show i)
      MachFloat r -> mk "float" (show r)
      MachDouble r -> mk "double" (show r)
      MachLabel fs _ _ -> mk "label" (show fs)
      LitInteger i _t -> mk "integer" (show i)

    where
    mk :: Text -> String -> JS.Value
    mk x s = JS.object [ "lit" .= s, "type" .= x ]

instance ToJSON DataCon where
  toJSON = toJSON . dataConName


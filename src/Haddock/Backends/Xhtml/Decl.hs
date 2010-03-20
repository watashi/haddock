-----------------------------------------------------------------------------
-- |
-- Module      :  Haddock.Backends.Html.Decl
-- Copyright   :  (c) Simon Marlow   2003-2006,
--                    David Waern    2006-2009,
--                    Mark Lentczner 2010
-- License     :  BSD-like
--
-- Maintainer  :  haddock@projects.haskell.org
-- Stability   :  experimental
-- Portability :  portable
-----------------------------------------------------------------------------

module Haddock.Backends.Xhtml.Decl where

import Haddock.Backends.Xhtml.DocMarkup
import Haddock.Backends.Xhtml.Layout
import Haddock.Backends.Xhtml.Names
import Haddock.Backends.Xhtml.Types
import Haddock.Backends.Xhtml.Util
import Haddock.GhcUtils
import Haddock.Types

import           Control.Monad         ( join )
import qualified Data.Map as Map
import           Data.Maybe
import           Text.XHtml hiding     ( name, title, p, quote )

import BasicTypes            ( IPName(..), Boxity(..) )
import GHC
import Name
import Outputable            ( ppr, showSDoc, Outputable )


-- TODO: use DeclInfo DocName or something
ppDecl' :: Bool -> LinksInfo -> LHsDecl DocName -> 
          DocForDecl DocName -> [DocInstance DocName] -> [(DocName, DocForDecl DocName)] -> Bool -> Html
ppDecl' s k l m i d u = vanillaTable << ppDecl s k l m i d u

ppDecl :: Bool -> LinksInfo -> LHsDecl DocName -> 
          DocForDecl DocName -> [DocInstance DocName] -> [(DocName, DocForDecl DocName)] -> Bool -> HtmlTable
ppDecl summ links (L loc decl) (mbDoc, fnArgsDoc) instances subdocs unicode = case decl of
  TyClD d@(TyFamily {})          -> ppTyFam summ False links loc mbDoc d unicode
  TyClD d@(TyData {})
    | Nothing <- tcdTyPats d     -> ppDataDecl summ links instances subdocs loc mbDoc d unicode
    | Just _  <- tcdTyPats d     -> ppDataInst summ links loc mbDoc d 
  TyClD d@(TySynonym {})
    | Nothing <- tcdTyPats d     -> ppTySyn summ links loc (mbDoc, fnArgsDoc) d unicode
    | Just _  <- tcdTyPats d     -> ppTyInst summ False links loc mbDoc d unicode
  TyClD d@(ClassDecl {})         -> ppClassDecl summ links instances loc mbDoc subdocs d unicode
  SigD (TypeSig (L _ n) (L _ t)) -> ppFunSig summ links loc (mbDoc, fnArgsDoc) n t unicode
  ForD d                         -> ppFor summ links loc (mbDoc, fnArgsDoc) d unicode
  InstD _                        -> emptyTable
  _                              -> error "declaration not supported by ppDecl"

ppFunSig :: Bool -> LinksInfo -> SrcSpan -> DocForDecl DocName ->
            DocName -> HsType DocName -> Bool -> HtmlTable
ppFunSig summary links loc doc docname typ unicode =
  ppTypeOrFunSig summary links loc docname typ doc
    (ppTypeSig summary occname typ unicode, ppBinder False occname, dcolon unicode) unicode
  where
    occname = docNameOcc docname

ppTypeOrFunSig :: Bool -> LinksInfo -> SrcSpan -> DocName -> HsType DocName ->
                  DocForDecl DocName -> (Html, Html, Html) -> Bool -> HtmlTable
ppTypeOrFunSig summary links loc docname typ (doc, argDocs) (pref1, pref2, sep) unicode
  | summary || Map.null argDocs = declWithDoc summary links loc docname doc pref1
  | otherwise = topDeclBox links loc docname pref2 </>
    (tda [theclass "body"] << vanillaTable <<  (
      do_args 0 sep typ </>
        (case doc of
          Just d -> ndocBox (docToHtml d)
          Nothing -> emptyTable)
        ))
  where 
    argDocHtml n = case Map.lookup n argDocs of
                    Just adoc -> docToHtml adoc
                    Nothing -> noHtml

    do_largs n leader (L _ t) = do_args n leader t  
    do_args :: Int -> Html -> (HsType DocName) -> HtmlTable
    do_args n leader (HsForAllTy Explicit tvs lctxt ltype)
      = (argBox (
          leader <+> 
          hsep (forallSymbol unicode : ppTyVars tvs ++ [dot]) <+>
          ppLContextNoArrow lctxt unicode)
            <-> rdocBox noHtml) </> 
            do_largs n (darrow unicode) ltype
    do_args n leader (HsForAllTy Implicit _ lctxt ltype)
      | not (null (unLoc lctxt))
      = (argBox (leader <+> ppLContextNoArrow lctxt unicode)
          <-> rdocBox noHtml) </> 
          do_largs n (darrow unicode) ltype
      -- if we're not showing any 'forall' or class constraints or
      -- anything, skip having an empty line for the context.
      | otherwise
      = do_largs n leader ltype
    do_args n leader (HsFunTy lt r)
      = (argBox (leader <+> ppLFunLhType unicode lt) <-> rdocBox (argDocHtml n))
          </> do_largs (n+1) (arrow unicode) r
    do_args n leader t
      = argBox (leader <+> ppType unicode t) <-> rdocBox (argDocHtml n)


ppTyVars :: [LHsTyVarBndr DocName] -> [Html]
ppTyVars tvs = map ppTyName (tyvarNames tvs)


tyvarNames :: [LHsTyVarBndr DocName] -> [Name]
tyvarNames = map (getName . hsTyVarName . unLoc)
  

ppFor :: Bool -> LinksInfo -> SrcSpan -> DocForDecl DocName -> ForeignDecl DocName -> Bool -> HtmlTable
ppFor summary links loc doc (ForeignImport (L _ name) (L _ typ) _) unicode
  = ppFunSig summary links loc doc name typ unicode
ppFor _ _ _ _ _ _ = error "ppFor"


-- we skip type patterns for now
ppTySyn :: Bool -> LinksInfo -> SrcSpan -> DocForDecl DocName -> TyClDecl DocName -> Bool -> HtmlTable
ppTySyn summary links loc doc (TySynonym (L _ name) ltyvars _ ltype) unicode
  = ppTypeOrFunSig summary links loc name (unLoc ltype) doc 
                   (full, hdr, spaceHtml +++ equals) unicode
  where
    hdr  = hsep ([keyword "type", ppBinder summary occ] ++ ppTyVars ltyvars)
    full = hdr <+> equals <+> ppLType unicode ltype
    occ  = docNameOcc name
ppTySyn _ _ _ _ _ _ = error "declaration not supported by ppTySyn"


ppTypeSig :: Bool -> OccName -> HsType DocName  -> Bool -> Html
ppTypeSig summary nm ty unicode = ppBinder summary nm <+> dcolon unicode <+> ppType unicode ty


ppTyName :: Name -> Html
ppTyName name
  | isNameSym name = parens (ppName name)
  | otherwise = ppName name


--------------------------------------------------------------------------------
-- Type families
--------------------------------------------------------------------------------


ppTyFamHeader :: Bool -> Bool -> TyClDecl DocName -> Bool -> Html
ppTyFamHeader summary associated decl unicode =

  (case tcdFlavour decl of
     TypeFamily
       | associated -> keyword "type"
       | otherwise  -> keyword "type family"
     DataFamily
       | associated -> keyword "data"
       | otherwise  -> keyword "data family"
  ) <+>

  ppTyClBinderWithVars summary decl <+>

  case tcdKind decl of
    Just kind -> dcolon unicode  <+> ppKind kind 
    Nothing -> empty


ppTyFam :: Bool -> Bool -> LinksInfo -> SrcSpan -> Maybe (Doc DocName) ->
              TyClDecl DocName -> Bool -> HtmlTable
ppTyFam summary associated links loc mbDoc decl unicode
  
  | summary = declWithDoc summary links loc docname mbDoc 
              (ppTyFamHeader True associated decl unicode)
  
  | associated, isJust mbDoc         = header_ </> bodyBox << doc 
  | associated                       = header_ 
  | null instances, isJust mbDoc     = header_ </> bodyBox << doc
  | null instances                   = header_
  | isJust mbDoc                     = header_ </> bodyBox << (doc </> instancesBit)
  | otherwise                        = header_ </> bodyBox << instancesBit

  where
    docname = tcdName decl

    header_ = topDeclBox links loc docname (ppTyFamHeader summary associated decl unicode)

    doc = ndocBox . docToHtml . fromJust $ mbDoc 

    instId = collapseId (getName docname)

    instancesBit = instHdr instId </>
          tda [theclass "body"] << 
            collapsed thediv instId (
              spacedTable1 << (
                aboves (map (ppDocInstance unicode) instances)
              )
            )

    -- TODO: get the instances
    instances = []


--------------------------------------------------------------------------------
-- Indexed data types
--------------------------------------------------------------------------------


ppDataInst :: a
ppDataInst = undefined


--------------------------------------------------------------------------------
-- Indexed newtypes
--------------------------------------------------------------------------------

-- TODO
-- ppNewTyInst = undefined


--------------------------------------------------------------------------------
-- Indexed types
--------------------------------------------------------------------------------

 
ppTyInst :: Bool -> Bool -> LinksInfo -> SrcSpan -> Maybe (Doc DocName) ->
            TyClDecl DocName -> Bool -> HtmlTable
ppTyInst summary associated links loc mbDoc decl unicode
  
  | summary = declWithDoc summary links loc docname mbDoc
              (ppTyInstHeader True associated decl unicode)
  
  | isJust mbDoc = header_ </> bodyBox << doc 
  | otherwise    = header_

  where
    docname = tcdName decl

    header_ = topDeclBox links loc docname (ppTyInstHeader summary associated decl unicode)

    doc = case mbDoc of
      Just d -> ndocBox (docToHtml d)
      Nothing -> emptyTable


ppTyInstHeader :: Bool -> Bool -> TyClDecl DocName -> Bool -> Html
ppTyInstHeader _ _ decl unicode =
  keyword "type instance" <+>
  ppAppNameTypes (tcdName decl) typeArgs unicode
  where
    typeArgs = map unLoc . fromJust . tcdTyPats $ decl


--------------------------------------------------------------------------------
-- Associated Types
--------------------------------------------------------------------------------
    

ppAssocType :: Bool -> LinksInfo -> DocForDecl DocName -> LTyClDecl DocName -> Bool -> HtmlTable
ppAssocType summ links doc (L loc decl) unicode = 
  case decl of
    TyFamily  {} -> ppTyFam summ True links loc (fst doc) decl unicode
    TySynonym {} -> ppTySyn summ links loc doc decl unicode
    _            -> error "declaration type not supported by ppAssocType" 


--------------------------------------------------------------------------------
-- TyClDecl helpers
--------------------------------------------------------------------------------


-- | Print a type family / newtype / data / class binder and its variables 
ppTyClBinderWithVars :: Bool -> TyClDecl DocName -> Html
ppTyClBinderWithVars summ decl = 
  ppAppDocNameNames summ (unLoc $ tcdLName decl) (tyvarNames $ tcdTyVars decl)


--------------------------------------------------------------------------------
-- Type applications
--------------------------------------------------------------------------------


-- | Print an application of a DocName and a list of HsTypes
ppAppNameTypes :: DocName -> [HsType DocName] -> Bool -> Html
ppAppNameTypes n ts unicode = ppTypeApp n ts ppDocName (ppParendType unicode)


-- | Print an application of a DocName and a list of Names 
ppAppDocNameNames :: Bool -> DocName -> [Name] -> Html
ppAppDocNameNames summ n ns = 
  ppTypeApp n ns (ppBinder summ . docNameOcc) ppTyName


-- | General printing of type applications
ppTypeApp :: DocName -> [a] -> (DocName -> Html) -> (a -> Html) -> Html
ppTypeApp n (t1:t2:rest) ppDN ppT
  | operator, not . null $ rest = parens opApp <+> hsep (map ppT rest)
  | operator                    = opApp
  where
    operator = isNameSym . getName $ n
    opApp = ppT t1 <+> ppDN n <+> ppT t2

ppTypeApp n ts ppDN ppT = ppDN n <+> hsep (map ppT ts)


-------------------------------------------------------------------------------
-- Contexts 
-------------------------------------------------------------------------------


ppLContext, ppLContextNoArrow :: Located (HsContext DocName) -> Bool -> Html
ppLContext        = ppContext        . unLoc
ppLContextNoArrow = ppContextNoArrow . unLoc


ppContextNoArrow :: HsContext DocName -> Bool -> Html
ppContextNoArrow []  _ = empty
ppContextNoArrow cxt unicode = pp_hs_context (map unLoc cxt) unicode


ppContextNoLocs :: [HsPred DocName] -> Bool -> Html
ppContextNoLocs []  _ = empty
ppContextNoLocs cxt unicode = pp_hs_context cxt unicode <+> darrow unicode


ppContext :: HsContext DocName -> Bool -> Html
ppContext cxt unicode = ppContextNoLocs (map unLoc cxt) unicode


pp_hs_context :: [HsPred DocName] -> Bool -> Html
pp_hs_context []  _       = empty
pp_hs_context [p] unicode = ppPred unicode p
pp_hs_context cxt unicode = parenList (map (ppPred unicode) cxt)


ppPred :: Bool -> HsPred DocName -> Html
ppPred unicode (HsClassP n ts) = ppAppNameTypes n (map unLoc ts) unicode
ppPred unicode (HsEqualP t1 t2) = ppLType unicode t1 <+> toHtml "~" <+> ppLType unicode t2
ppPred unicode (HsIParam (IPName n) t)
  = toHtml "?" +++ ppDocName n <+> dcolon unicode <+> ppLType unicode t


-------------------------------------------------------------------------------
-- Class declarations
-------------------------------------------------------------------------------


ppClassHdr :: Bool -> Located [LHsPred DocName] -> DocName
           -> [Located (HsTyVarBndr DocName)] -> [Located ([DocName], [DocName])]
           -> Bool -> Html
ppClassHdr summ lctxt n tvs fds unicode = 
  keyword "class" 
  <+> (if not . null . unLoc $ lctxt then ppLContext lctxt unicode else empty)
  <+> ppAppDocNameNames summ n (tyvarNames $ tvs)
        <+> ppFds fds unicode


ppFds :: [Located ([DocName], [DocName])] -> Bool -> Html
ppFds fds unicode =
  if null fds then noHtml else 
        char '|' <+> hsep (punctuate comma (map (fundep . unLoc) fds))
  where
        fundep (vars1,vars2) = hsep (map ppDocName vars1) <+> arrow unicode <+>
                               hsep (map ppDocName vars2)

ppShortClassDecl :: Bool -> LinksInfo -> TyClDecl DocName -> SrcSpan -> [(DocName, DocForDecl DocName)] -> Bool -> HtmlTable
ppShortClassDecl summary links (ClassDecl lctxt lname tvs fds sigs _ ats _) loc subdocs unicode = 
  if null sigs && null ats
    then (if summary then declBox else topDeclBox links loc nm) hdr
    else (if summary then declBox else topDeclBox links loc nm) (hdr <+> keyword "where")
            </> 
      (
                                bodyBox <<
                                        aboves
                                        (
                                                [ ppAssocType summary links doc at unicode | at <- ats
                                                , let doc = lookupAnySubdoc (tcdName $ unL at) subdocs ]  ++

                                                [ ppFunSig summary links loc doc n typ unicode
                                                | L _ (TypeSig (L _ n) (L _ typ)) <- sigs
                                                , let doc = lookupAnySubdoc n subdocs ] 
                                        )
                                )
  where
    hdr = ppClassHdr summary lctxt (unLoc lname) tvs fds unicode
    nm  = unLoc lname
ppShortClassDecl _ _ _ _ _ _ = error "declaration type not supported by ppShortClassDecl"
    


ppClassDecl :: Bool -> LinksInfo -> [DocInstance DocName] -> SrcSpan
            -> Maybe (Doc DocName) -> [(DocName, DocForDecl DocName)]
            -> TyClDecl DocName -> Bool -> HtmlTable
ppClassDecl summary links instances loc mbDoc subdocs
        decl@(ClassDecl lctxt lname ltyvars lfds lsigs _ ats _) unicode
  | summary = ppShortClassDecl summary links decl loc subdocs unicode
  | otherwise = classheader </> bodyBox << (classdoc </> body_ </> instancesBit)
  where 
    classheader
      | null lsigs = topDeclBox links loc nm (hdr unicode)
      | otherwise  = topDeclBox links loc nm (hdr unicode <+> keyword "where")

    nm   = unLoc $ tcdLName decl

    hdr = ppClassHdr summary lctxt (unLoc lname) ltyvars lfds
    
    classdoc = case mbDoc of
      Nothing -> emptyTable
      Just d -> ndocBox (docToHtml d)

    body_
      | null lsigs, null ats = emptyTable
      | null ats  = s8 </> methHdr </> bodyBox << methodTable
      | otherwise = s8 </> atHdr </> bodyBox << atTable </> 
                    s8 </> methHdr </> bodyBox << methodTable 
 
    methodTable =
      abovesSep s8 [ ppFunSig summary links loc doc n typ unicode
                   | L _ (TypeSig (L _ n) (L _ typ)) <- lsigs
                   , let doc = lookupAnySubdoc n subdocs ]

    atTable = abovesSep s8 $ [ ppAssocType summary links doc at unicode | at <- ats
                             , let doc = lookupAnySubdoc (tcdName $ unL at) subdocs ]

    instId = collapseId (getName nm)
    instancesBit
      | null instances = emptyTable
      | otherwise 
        =  s8 </> instHdr instId </>
           tda [theclass "body"] << 
             collapsed thediv instId (
               spacedTable1 << aboves (map (ppDocInstance unicode) instances)
             )
ppClassDecl _ _ _ _ _ _ _ _ = error "declaration type not supported by ppShortClassDecl"


-- | Print a possibly commented instance. The instance header is printed inside
-- an 'argBox'. The comment is printed to the right of the box in normal comment
-- style.
ppDocInstance :: Bool -> DocInstance DocName -> HtmlTable
ppDocInstance unicode (instHead, maybeDoc) =
  argBox (ppInstHead unicode instHead) <-> maybeRDocBox maybeDoc


ppInstHead :: Bool -> InstHead DocName -> Html
ppInstHead unicode ([],   n, ts) = ppAppNameTypes n ts unicode
ppInstHead unicode (ctxt, n, ts) = ppContextNoLocs ctxt unicode <+> ppAppNameTypes n ts unicode


lookupAnySubdoc :: (Eq name1) =>
                   name1 -> [(name1, DocForDecl name2)] -> DocForDecl name2
lookupAnySubdoc n subdocs = case lookup n subdocs of
  Nothing -> noDocForDecl
  Just docs -> docs
      


-- -----------------------------------------------------------------------------
-- Data & newtype declarations


-- TODO: print contexts
ppShortDataDecl :: Bool -> LinksInfo -> SrcSpan -> TyClDecl DocName -> Bool -> Html
ppShortDataDecl summary links loc dataDecl unicode

  | [lcon] <- cons, ResTyH98 <- resTy = 
    ppDataHeader summary dataDecl unicode
    <+> equals <+> ppShortConstr summary (unLoc lcon) unicode

  | [] <- cons = ppDataHeader summary dataDecl unicode

  | otherwise = vanillaTable << (
      case resTy of 
        ResTyH98 -> dataHeader </> 
          tda [theclass "body"] << vanillaTable << (
            aboves (zipWith doConstr ('=':repeat '|') cons)
          )
        ResTyGADT _ -> dataHeader </> 
          tda [theclass "body"] << vanillaTable << (
            aboves (map doGADTConstr cons)
          )
    )
  
  where
    dataHeader = 
      (if summary then declBox else topDeclBox links loc docname)
      ((ppDataHeader summary dataDecl unicode) <+> 
      case resTy of ResTyGADT _ -> keyword "where"; _ -> empty)

    doConstr c con = declBox (toHtml [c] <+> ppShortConstr summary (unLoc con) unicode)
    doGADTConstr con = declBox (ppShortConstr summary (unLoc con) unicode)

    docname   = unLoc . tcdLName $ dataDecl
    cons      = tcdCons dataDecl
    resTy     = (con_res . unLoc . head) cons 

ppDataDecl :: Bool -> LinksInfo -> [DocInstance DocName] ->
              [(DocName, DocForDecl DocName)] ->
              SrcSpan -> Maybe (Doc DocName) -> TyClDecl DocName -> Bool -> HtmlTable
ppDataDecl summary links instances subdocs loc mbDoc dataDecl unicode
  
  | summary = declWithDoc summary links loc docname mbDoc 
              (ppShortDataDecl summary links loc dataDecl unicode)
  
  | otherwise
      = (if validTable then (</>) else const) header_ $
              tda [theclass "body"] << vanillaTable << (
                      datadoc </> 
                      constrBit </>
                      instancesBit
        )


  where
    docname   = unLoc . tcdLName $ dataDecl
    cons      = tcdCons dataDecl
    resTy     = (con_res . unLoc . head) cons 
      
    header_ = topDeclBox links loc docname (ppDataHeader summary dataDecl unicode
             <+> whereBit)

    whereBit 
      | null cons = empty 
      | otherwise = case resTy of 
        ResTyGADT _ -> keyword "where"
        _ -> empty                         

    constrTable
      | any isRecCon cons = spacedTable5
      | otherwise         = spacedTable1

    datadoc = case mbDoc of
      Just doc -> ndocBox (docToHtml doc)
      Nothing -> emptyTable

    constrBit 
      | null cons = emptyTable
      | otherwise = constrHdr </> ( 
          tda [theclass "body"] << constrTable << 
          aboves (map (ppSideBySideConstr subdocs unicode) cons)
        )

    instId = collapseId (getName docname)

    instancesBit
      | null instances = emptyTable
      | otherwise 
        = instHdr instId </>
          tda [theclass "body"] << 
          collapsed thediv instId (
            spacedTable1 << aboves (map (ppDocInstance unicode) instances
            )
          )

    validTable = isJust mbDoc || not (null cons) || not (null instances)


isRecCon :: Located (ConDecl a) -> Bool
isRecCon lcon = case con_details (unLoc lcon) of 
  RecCon _ -> True
  _ -> False


ppShortConstr :: Bool -> ConDecl DocName -> Bool -> Html
ppShortConstr summary con unicode = case con_res con of 
  ResTyH98 -> case con_details con of 
    PrefixCon args -> header_ unicode +++ hsep (ppBinder summary occ : map (ppLParendType unicode) args)
    RecCon fields -> header_ unicode +++ ppBinder summary occ <+>
                                              doRecordFields fields
    InfixCon arg1 arg2 -> header_ unicode +++ 
      hsep [ppLParendType unicode arg1, ppBinder summary occ, ppLParendType unicode arg2]    

  ResTyGADT resTy -> case con_details con of 
    -- prefix & infix could use hsConDeclArgTys if it seemed to
    -- simplify the code.
    PrefixCon args -> doGADTCon args resTy
    -- display GADT records with the new syntax,
    -- Constr :: (Context) => { field :: a, field2 :: b } -> Ty (a, b)
    -- (except each field gets its own line in docs, to match
    -- non-GADT records)
    RecCon fields -> ppBinder summary occ <+> dcolon unicode <+> hsep [
                            ppForAll forall ltvs lcontext unicode,
                            doRecordFields fields,
                            arrow unicode <+> ppLType unicode resTy ]
    InfixCon arg1 arg2 -> doGADTCon [arg1, arg2] resTy 
    
  where
    doRecordFields fields = braces (vanillaTable <<
                        aboves (map (ppShortField summary unicode) fields))
    doGADTCon args resTy = ppBinder summary occ <+> dcolon unicode <+> hsep [
                             ppForAll forall ltvs lcontext unicode,
                             ppLType unicode (foldr mkFunTy resTy args) ]

    header_  = ppConstrHdr forall tyVars context
    occ      = docNameOcc . unLoc . con_name $ con
    ltvs     = con_qvars con
    tyVars   = tyvarNames ltvs 
    lcontext = con_cxt con
    context  = unLoc (con_cxt con)
    forall   = con_explicit con
    mkFunTy a b = noLoc (HsFunTy a b)

-- ppConstrHdr is for (non-GADT) existentials constructors' syntax
ppConstrHdr :: HsExplicitForAll -> [Name] -> HsContext DocName -> Bool -> Html
ppConstrHdr forall tvs ctxt unicode
 = (if null tvs then noHtml else ppForall)
   +++
   (if null ctxt then noHtml else ppContextNoArrow ctxt unicode <+> darrow unicode +++ toHtml " ")
  where
    ppForall = case forall of 
      Explicit -> forallSymbol unicode <+> hsep (map ppName tvs) <+> toHtml ". "
      Implicit -> empty

ppSideBySideConstr :: [(DocName, DocForDecl DocName)] -> Bool -> LConDecl DocName -> HtmlTable
ppSideBySideConstr subdocs unicode (L _ con) = case con_res con of 
 
  ResTyH98 -> case con_details con of 

    PrefixCon args -> 
      argBox (hsep ((header_ unicode +++ ppBinder False occ) : map (ppLParendType unicode) args)) 
      <-> maybeRDocBox mbDoc  

    RecCon fields -> 
      argBox (header_ unicode +++ ppBinder False occ) <->
      maybeRDocBox mbDoc
      </>
      doRecordFields fields

    InfixCon arg1 arg2 -> 
      argBox (hsep [header_ unicode+++ppLParendType unicode arg1, ppBinder False occ, ppLParendType unicode arg2])
      <-> maybeRDocBox mbDoc
 
  ResTyGADT resTy -> case con_details con of
    -- prefix & infix could also use hsConDeclArgTys if it seemed to
    -- simplify the code.
    PrefixCon args -> doGADTCon args resTy
    cd@(RecCon fields) -> doGADTCon (hsConDeclArgTys cd) resTy
                                          </> doRecordFields fields
    InfixCon arg1 arg2 -> doGADTCon [arg1, arg2] resTy 

 where 
    doRecordFields fields =
        (tda [theclass "body"] << spacedTable1 <<
        aboves (map (ppSideBySideField subdocs unicode) fields))
    doGADTCon args resTy = argBox (ppBinder False occ <+> dcolon unicode <+> hsep [
                               ppForAll forall ltvs (con_cxt con) unicode,
                               ppLType unicode (foldr mkFunTy resTy args) ]
                            ) <-> maybeRDocBox mbDoc


    header_ = ppConstrHdr forall tyVars context
    occ     = docNameOcc . unLoc . con_name $ con
    ltvs    = con_qvars con
    tyVars  = tyvarNames (con_qvars con)
    context = unLoc (con_cxt con)
    forall  = con_explicit con
    -- don't use "con_doc con", in case it's reconstructed from a .hi file,
    -- or also because we want Haddock to do the doc-parsing, not GHC.
    -- 'join' is in Maybe.
    mbDoc = join $ fmap fst $ lookup (unLoc $ con_name con) subdocs
    mkFunTy a b = noLoc (HsFunTy a b)

ppSideBySideField :: [(DocName, DocForDecl DocName)] -> Bool -> ConDeclField DocName ->  HtmlTable
ppSideBySideField subdocs unicode (ConDeclField (L _ name) ltype _) =
  argBox (ppBinder False (docNameOcc name)
    <+> dcolon unicode <+> ppLType unicode ltype) <-> maybeRDocBox mbDoc
  where
    -- don't use cd_fld_doc for same reason we don't use con_doc above
    mbDoc = join $ fmap fst $ lookup name subdocs

{-
ppHsFullConstr :: HsConDecl -> Html
ppHsFullConstr (HsConDecl _ nm tvs ctxt typeList doc) = 
     declWithDoc False doc (
        hsep ((ppHsConstrHdr tvs ctxt +++ 
                ppHsBinder False nm) : map ppHsBangType typeList)
      )
ppHsFullConstr (HsRecDecl _ nm tvs ctxt fields doc) =
   td << vanillaTable << (
     case doc of
       Nothing -> aboves [hdr, fields_html]
       Just _  -> aboves [hdr, constr_doc, fields_html]
   )

  where hdr = declBox (ppHsConstrHdr tvs ctxt +++ ppHsBinder False nm)

        constr_doc      
          | isJust doc = docBox (docToHtml (fromJust doc))
          | otherwise  = emptyTable

        fields_html = 
           td << 
              table ! [width "100%", cellpadding 0, cellspacing 8] << (
                   aboves (map ppFullField (concat (map expandField fields)))
                )
-}

ppShortField :: Bool -> Bool -> ConDeclField DocName -> HtmlTable
ppShortField summary unicode (ConDeclField (L _ name) ltype _)
  = tda [theclass "recfield"] << (
      ppBinder summary (docNameOcc name)
      <+> dcolon unicode <+> ppLType unicode ltype
    )

{-
ppFullField :: HsFieldDecl -> Html
ppFullField (HsFieldDecl [n] ty doc) 
  = declWithDoc False doc (
        ppHsBinder False n <+> dcolon <+> ppHsBangType ty
    )
ppFullField _ = error "ppFullField"

expandField :: HsFieldDecl -> [HsFieldDecl]
expandField (HsFieldDecl ns ty doc) = [ HsFieldDecl [n] ty doc | n <- ns ]
-}

-- | Print the LHS of a data\/newtype declaration.
-- Currently doesn't handle 'data instance' decls or kind signatures
ppDataHeader :: Bool -> TyClDecl DocName -> Bool -> Html
ppDataHeader summary decl unicode
  | not (isDataDecl decl) = error "ppDataHeader: illegal argument"
  | otherwise = 
    -- newtype or data
    (if tcdND decl == NewType then keyword "newtype" else keyword "data") <+> 
    -- context
    ppLContext (tcdCtxt decl) unicode <+>
    -- T a b c ..., or a :+: b
    ppTyClBinderWithVars summary decl


-- ----------------------------------------------------------------------------
-- Types and contexts


ppKind :: Outputable a => a -> Html
ppKind k = toHtml $ showSDoc (ppr k)


{-
ppForAll Implicit _ lctxt = ppCtxtPart lctxt
ppForAll Explicit ltvs lctxt = 
  hsep (keyword "forall" : ppTyVars ltvs ++ [dot]) <+> ppCtxtPart lctxt 
-}


ppBang :: HsBang -> Html
ppBang HsNoBang = empty 
ppBang HsStrict = toHtml "!"
ppBang HsUnbox  = toHtml "!" -- unboxed args is an implementation detail,
                             -- so we just show the strictness annotation


tupleParens :: Boxity -> [Html] -> Html
tupleParens Boxed   = parenList
tupleParens Unboxed = ubxParenList 
{-
ppType :: HsType DocName -> Html
ppType t = case t of
  t@(HsForAllTy expl ltvs lcontext ltype) -> ppForAllTy t <+> ppLType ltype
  HsTyVar n -> ppDocName n
  HsBangTy HsStrict lt -> toHtml "!" <+> ppLType lt
  HsBangTy HsUnbox lt -> toHtml "!!" <+> ppLType lt
  HsAppTy a b -> ppLType a <+> ppLType b 
  HsFunTy a b -> hsep [ppLType a, toHtml "->", ppLType b]
  HsListTy t -> brackets $ ppLType t
  HsPArrTy t -> toHtml "[:" +++ ppLType t +++ toHtml ":]"
  HsTupleTy Boxed ts -> parenList $ map ppLType ts
  HsTupleTy Unboxed ts -> ubxParenList $ map ppLType ts
  HsOpTy a n b -> ppLType a <+> ppLDocName n <+> ppLType b
  HsParTy t -> parens $ ppLType t
  HsNumTy n -> toHtml (show n)
  HsPredTy p -> ppPred p
  HsKindSig t k -> hsep [ppLType t, dcolon, ppKind k]
  HsSpliceTy _ -> error "ppType"
  HsDocTy t _ -> ppLType t
-}


--------------------------------------------------------------------------------
-- Rendering of HsType 
--------------------------------------------------------------------------------


pREC_TOP, pREC_FUN, pREC_OP, pREC_CON :: Int

pREC_TOP = (0 :: Int)   -- type in ParseIface.y in GHC
pREC_FUN = (1 :: Int)   -- btype in ParseIface.y in GHC
                        -- Used for LH arg of (->)
pREC_OP  = (2 :: Int)   -- Used for arg of any infix operator
                        -- (we don't keep their fixities around)
pREC_CON = (3 :: Int)   -- Used for arg of type applicn:
                        -- always parenthesise unless atomic

maybeParen :: Int           -- Precedence of context
           -> Int           -- Precedence of top-level operator
           -> Html -> Html  -- Wrap in parens if (ctxt >= op)
maybeParen ctxt_prec op_prec p | ctxt_prec >= op_prec = parens p
                               | otherwise            = p


ppLType, ppLParendType, ppLFunLhType :: Bool -> Located (HsType DocName) -> Html
ppLType       unicode y = ppType unicode (unLoc y)
ppLParendType unicode y = ppParendType unicode (unLoc y) 
ppLFunLhType  unicode y = ppFunLhType unicode (unLoc y)


ppType, ppParendType, ppFunLhType :: Bool -> HsType DocName -> Html
ppType       unicode ty = ppr_mono_ty pREC_TOP ty unicode 
ppParendType unicode ty = ppr_mono_ty pREC_CON ty unicode 
ppFunLhType  unicode ty = ppr_mono_ty pREC_FUN ty unicode


-- Drop top-level for-all type variables in user style
-- since they are implicit in Haskell

ppForAll :: HsExplicitForAll -> [Located (HsTyVarBndr DocName)]
         -> Located (HsContext DocName) -> Bool -> Html
ppForAll expl tvs cxt unicode
  | show_forall = forall_part <+> ppLContext cxt unicode
  | otherwise   = ppLContext cxt unicode
  where
    show_forall = not (null tvs) && is_explicit
    is_explicit = case expl of {Explicit -> True; Implicit -> False}
    forall_part = hsep (forallSymbol unicode : ppTyVars tvs) +++ dot 


ppr_mono_lty :: Int -> LHsType DocName -> Bool -> Html
ppr_mono_lty ctxt_prec ty unicode = ppr_mono_ty ctxt_prec (unLoc ty) unicode 


ppr_mono_ty :: Int -> HsType DocName -> Bool -> Html
ppr_mono_ty ctxt_prec (HsForAllTy expl tvs ctxt ty) unicode 
  = maybeParen ctxt_prec pREC_FUN $
    hsep [ppForAll expl tvs ctxt unicode, ppr_mono_lty pREC_TOP ty unicode]

-- gaw 2004
ppr_mono_ty _         (HsBangTy b ty)     u = ppBang b +++ ppLParendType u ty
ppr_mono_ty _         (HsTyVar name)      _ = ppDocName name
ppr_mono_ty ctxt_prec (HsFunTy ty1 ty2)   u = ppr_fun_ty ctxt_prec ty1 ty2 u
ppr_mono_ty _         (HsTupleTy con tys) u = tupleParens con (map (ppLType u) tys)
ppr_mono_ty _         (HsKindSig ty kind) u = parens (ppr_mono_lty pREC_TOP ty u <+> dcolon u <+> ppKind kind)
ppr_mono_ty _         (HsListTy ty)       u = brackets (ppr_mono_lty pREC_TOP ty u)
ppr_mono_ty _         (HsPArrTy ty)       u = pabrackets (ppr_mono_lty pREC_TOP ty u)
ppr_mono_ty _         (HsPredTy p)        u = parens (ppPred u p)
ppr_mono_ty _         (HsNumTy n)         _ = toHtml (show n) -- generics only
ppr_mono_ty _         (HsSpliceTy _)      _ = error "ppr_mono_ty HsSpliceTy"
ppr_mono_ty _         (HsSpliceTyOut _)   _ = error "ppr_mono_ty HsSpliceTyOut"
ppr_mono_ty _         (HsRecTy _)         _ = error "ppr_mono_ty HsRecTy"


ppr_mono_ty ctxt_prec (HsAppTy fun_ty arg_ty) unicode 
  = maybeParen ctxt_prec pREC_CON $
    hsep [ppr_mono_lty pREC_FUN fun_ty unicode, ppr_mono_lty pREC_CON arg_ty unicode]

ppr_mono_ty ctxt_prec (HsOpTy ty1 op ty2) unicode 
  = maybeParen ctxt_prec pREC_FUN $
    ppr_mono_lty pREC_OP ty1 unicode <+> ppr_op <+> ppr_mono_lty pREC_OP ty2 unicode
  where
    ppr_op = if not (isSymOcc occName) then quote (ppLDocName op) else ppLDocName op
    occName = docNameOcc . unLoc $ op

ppr_mono_ty ctxt_prec (HsParTy ty) unicode 
--  = parens (ppr_mono_lty pREC_TOP ty)
  = ppr_mono_lty ctxt_prec ty unicode

ppr_mono_ty ctxt_prec (HsDocTy ty _) unicode 
  = ppr_mono_lty ctxt_prec ty unicode


ppr_fun_ty :: Int -> LHsType DocName -> LHsType DocName -> Bool -> Html 
ppr_fun_ty ctxt_prec ty1 ty2 unicode
  = let p1 = ppr_mono_lty pREC_FUN ty1 unicode
        p2 = ppr_mono_lty pREC_TOP ty2 unicode
    in
    maybeParen ctxt_prec pREC_FUN $
    hsep [p1, arrow unicode <+> p2]


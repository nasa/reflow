-- Notices:
-- Copyright 2023 United States Government as represented by the Administrator of the National Aeronautics and Space Administration. All Rights Reserved.

-- This software calls the NASA Software named “PRECiSA with Instrumented Code Generation” LAR-19739-1, which is not bundled or redistributed with this software, but users of this software must obtain their own NASA license, which is subject to the terms and conditions of the applicable at the time.

-- Disclaimers
-- No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE. THIS AGREEMENT DOES NOT, IN ANY MANNER, CONSTITUTE AN ENDORSEMENT BY GOVERNMENT AGENCY OR ANY PRIOR RECIPIENT OF ANY RESULTS, RESULTING DESIGNS, HARDWARE, SOFTWARE PRODUCTS OR ANY OTHER APPLICATIONS RESULTING FROM USE OF THE SUBJECT SOFTWARE.  FURTHER, GOVERNMENT AGENCY DISCLAIMS ALL WARRANTIES AND LIABILITIES REGARDING THIRD-PARTY SOFTWARE, IF PRESENT IN THE ORIGINAL SOFTWARE, AND DISTRIBUTES IT "AS IS."

-- Waiver and Indemnity:  RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS AGAINST THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT.  IF RECIPIENT'S USE OF THE SUBJECT SOFTWARE RESULTS IN ANY LIABILITIES, DEMANDS, DAMAGES, EXPENSES OR LOSSES ARISING FROM SUCH USE, INCLUDING ANY DAMAGES FROM PRODUCTS BASED ON, OR RESULTING FROM, RECIPIENT'S USE OF THE SUBJECT SOFTWARE, RECIPIENT SHALL INDEMNIFY AND HOLD HARMLESS THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW.  RECIPIENT'S SOLE REMEDY FOR ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL TERMINATION OF THIS AGREEMENT.


module FramaC.GenerateACSL where

import Prelude hiding (pred)
import AbsPVSLang
import AbsSpecLang
import AbstractDomain
import Common.TypesUtils
import Common.TypeConversions
import Data.Bifunctor (bimap)
import qualified FramaC.ACSLlang as ACSL
import qualified FramaC.ACSLTypes as ACSL
import FramaC.Types (HasConditionals,IsMaybeType)
import Operators
import Translation.Float2Real (fae2real)
import Utils (fst3,snd3,elimDuplicates,listFst3)
import Transformation (isTauMinus, isTauPlus)
import Data.Maybe (fromJust)
import qualified Data.Map as Map

conds2pred :: [Condition] -> ACSL.Pred
conds2pred [] = error "conds2pred: empty list of conditions."
conds2pred conditions = foldl1 ACSL.PredOr (map cond2acsl conditions)
   where
     cond2acsl cond = ACSL.PredAnd (ACSL.PredBExpr  $ bexpr2acsl (realPathCond cond))
                     (ACSL.PredAnd (ACSL.PredFBExpr $ fbexpr2acsl (fpPathCond cond))
                     (ACSL.PredAnd (ACSL.PredBExpr  $ bexpr2acsl (realCond cond))
                                   (ACSL.PredFBExpr $ fbexpr2acsl (fpCond cond))))

pathcond2pred :: [Condition] -> ACSL.Pred
pathcond2pred [] = error "conds2pred: empty list of conditions."
pathcond2pred conditions = foldl1 ACSL.PredOr (map cond2acsl conditions)
   where
     cond2acsl cond = ACSL.PredAnd (ACSL.PredBExpr  $ bexpr2acsl (realPathCond cond))
                                   (ACSL.PredFBExpr $ fbexpr2acsl (fpPathCond cond))

namePredStablePaths :: Maybe PredAbs -> String -> String
namePredStablePaths (Just TauPlus)  g = g ++ "_tauplus_stable_paths"
namePredStablePaths (Just TauMinus) g = g ++ "_tauminus_stable_paths"
namePredStablePaths _       g = g ++ "_stable_paths"

generateStablePathPred :: Maybe PredAbs
                       -> PVSType
                       -> String
                       -> [Arg]
                       -> Map.Map ResultField [Condition]
                       -> [(VarName, FAExpr, FAExpr)]
                       -> ACSL.PredDecl
generateStablePathPred predAbs fp f args listStableCond forIdxs
  | Map.keys listStableCond == [ResValue] = ACSL.PredDecl (namePredStablePaths predAbs f) (realArgs++fpArgs)
                                            (quantifyIdx forIdxs $ conds2pred listStableCondResValue)
  | otherwise = error "numPostCondition: record field not supported yet"
    where
      listStableCondResValue = fromJust $ Map.lookup ResValue listStableCond
      realArgs = map args2ACSL $ filter (\a -> not (isArgArray a || isArgInt a)) args
      fpArgs   = map (args2ACSL . argCast fp) args

makeValuePath :: ACSL.Type -> ACeb -> ACSL.FBExpr
makeValuePath resType aceb = ACSL.FAnd (fbexpr2acsl $ fpConds $ conds aceb) (foldl1 ACSL.FOr (map makeResEq (fDeclRes $ fpExprs aceb)))
  where
    makeResEq fpExpr = ACSL.FRel Eq (ACSL.FVar resType "result") (faexpr2acsl fpExpr)

forFpFunName :: String -> Int -> String
forFpFunName f n = "for_value_"++ f ++ show n

assignsNothing :: ACSL.Pred
assignsNothing = ACSL.Assigns []

errorVarPrecond :: [VarName] -> [ACSL.Pred]
errorVarPrecond errVars =
  posErrorPrecond errVars
  ++
  [ACSL.Assigns []]
  where
    posErrorPrecond [] = []
    posErrorPrecond evs = [ACSL.Requires (requirePositive evs)]

requirePositive :: [VarName] -> ACSL.Pred
requirePositive [] = error "requirePositive: empty list."
requirePositive vars = ACSL.PredFBExpr $ foldl1 ACSL.FAnd (map positiveVar vars)
  where
    positiveVar e = ACSL.FRel LtE (ACSL.FTypeCast (ACSL.Int) (ACSL.Float DoublePrec) (ACSL.FInt 0)) (ACSL.FVar (ACSL.Float DoublePrec) e)

fpFunName :: FunName -> FunName
fpFunName f = f ++ "_fp"

checkIsFiniteList :: [FAExpr] -> ACSL.Pred
checkIsFiniteList exprList = foldl1 ACSL.PredAnd (map (ACSL.IsFiniteFP . faexpr2acsl) exprList)

isFiniteHypothesis :: [FAExpr] -> ACSL.Pred
isFiniteHypothesis [] = ACSL.PredBExpr ACSL.BTrue
isFiniteHypothesis list = checkIsFiniteList list

behaviorStructure :: IsMaybeType
                  -> ACSL.Type
                  -> FunName
                  -> [Arg]
                  -> [VarName]
                  -> ACSL.Pred
behaviorStructure isMaybe targetFPType f fpArgs errVars
  = ACSL.Ensures formula
  where
    args = map (ACSL.arg2fpvar . args2ACSL) fpArgs
    isFinitePred = isFiniteHypothesis (map (FVar FPDouble) errVars)
                  -- ACSL.PredAnd (ACSL.IsFiniteFP $ acslResultPrefix ACSL.FResult)
                                -- (isFiniteHypothesis isFiniteExprList)
    acslResultPrefix = if (isMaybe f) then ACSL.FValue else id
    consequence = ACSL.PredFBExpr $ ACSL.EqualFP (acslResultPrefix ACSL.FResult)
                                                 (ACSL.FEFun (fpFunName f) ResValue targetFPType args)
    formula = if isFinitePred == (ACSL.PredBExpr ACSL.BTrue)
              then ACSL.Implies (ACSL.IsValid ACSL.Result) consequence
              else ACSL.Implies (ACSL.PredAnd (ACSL.IsValid ACSL.Result) isFinitePred) consequence

behaviorStructurePred :: IsMaybeType
                      -> ACSL.Type
                      -> PredAbs
                      -> FunName
                      -> [Arg]
                      -> [Arg]
                      -> [(VarName, FAExpr, FBExpr)]
                      -> ACSL.Pred
behaviorStructurePred isMaybe t predAbs f rArgs fpArgs errArgs
  = ACSL.Ensures $ if null rArgs
      then structBehaPred predAbs
      else ACSL.Forall (zip (map argName rArgs) (repeat ACSL.Real))
                       (structBehaPred predAbs)
  where
    errVars = listFst3 errArgs
    fpActArgs = map (ACSL.arg2fpvar . args2ACSL) fpArgs
    realActArgs = map (ACSL.arg2var . args2ACSL) $  filter (\a -> not (isArgArray a || isArgInt a)) rArgs
    res = (if (isMaybe f) then ACSL.Value else id) ACSL.Result

    structBehaPred predAbd = ACSL.Implies
      (let finiteHyps = isFiniteHypothesis (map (FVar FPDouble) errVars) in
        if (isMaybe f)
          then (if finiteHyps == ACSL.PredBExpr ACSL.BTrue
                then id
                else flip ACSL.PredAnd finiteHyps) (ACSL.IsValid ACSL.Result)
          else ACSL.PredAnd (ACSL.IsValid ACSL.Result) finiteHyps)
      (if errVarConstraints errArgs == ACSL.PredBExpr ACSL.BTrue
       then structBehaCons predAbs
       else ACSL.Implies
        (errVarConstraints errArgs) (structBehaCons predAbs))

    structBehaCons TauPlus =
        (ACSL.Implies
        (ACSL.AExprPred $ res)
        (ACSL.PredAnd (ACSL.AExprPred (ACSL.EFun  f ResValue ACSL.Real realActArgs))
        (ACSL.FAExprPred $ ACSL.FEFun (fpFunName f) ResValue t fpActArgs)))

    structBehaCons TauMinus =
      (ACSL.Implies
        (ACSL.AExprPred $ res)
        (ACSL.PredAnd (ACSL.PredNot $ ACSL.AExprPred (ACSL.EFun f ResValue ACSL.Real realActArgs))
                      (ACSL.PredNot $ ACSL.FAExprPred $ ACSL.FEFun (fpFunName f) ResValue t fpActArgs)))

    structBehaCons _ =
      (ACSL.PredAnd
      (ACSL.Implies
        (ACSL.AExprPred $ res)
        (ACSL.PredAnd (ACSL.AExprPred (ACSL.EFun  f ResValue ACSL.Real realActArgs))
        (ACSL.FAExprPred $ ACSL.FEFun (fpFunName f) ResValue t fpActArgs)))
      (ACSL.Implies
        (ACSL.PredNot $ ACSL.AExprPred $ res)
        (ACSL.PredAnd (ACSL.PredNot $ ACSL.AExprPred (ACSL.EFun f ResValue ACSL.Real realActArgs))
                      (ACSL.PredNot $ ACSL.FAExprPred $ ACSL.FEFun (fpFunName f) ResValue t fpActArgs))))

behaviorStablePaths :: FunName
                    -> Maybe PredAbs
                    -> ACSL.Type
                    -> [Arg]
                    -> [(VarName,FAExpr,FBExpr)]
                    -> [(VarName,FAExpr)]
                    -> [(VarName, FAExpr, FAExpr)]
                    -> [VarName]
                    -> ACSL.Pred
behaviorStablePaths f predAbs targetFPType args errArgs locVars forIdxs errVars
  = ACSL.Ensures $
      if null realArgs
      then acslPred
      else ACSL.Forall (zip (map argName realArgs) (repeat ACSL.Real)) acslPred
  where
    acslPred = defineLocalandErrVars errArgs locVars
                   (ACSL.Implies
                   (ACSL.PredAnd (isFiniteHypothesis (map (FVar FPDouble) errVars))
                                 (ACSL.IsValid ACSL.Result))
                   (quantifyIdx forIdxs stablePathpred))
    stablePathpred =  (ACSL.Pred (namePredStablePaths predAbs f) actArgs)
    realArgs = filter (\a -> not (isArgArray a || isArgInt a)) args
    actArgs = map (ACSL.arg2varWithType ACSL.Real . args2ACSL) realArgs ++ map (ACSL.arg2varWithType targetFPType . args2ACSL) args

behaviorSymbolic :: FunName -> PVSType -> [Arg] -> AExpr -> [(VarName,FAExpr,FBExpr)] -> [(VarName,FAExpr)] -> ACSL.Pred
behaviorSymbolic f fp realArgs errorExpr errArgs locVars = ACSL.Ensures $ defLocalVars errArgs locVars acslPred
  where
    realVarArgs = filter (\a -> not (isArgArray a || isArgInt a)) realArgs
    inputVarNames = map argName realVarArgs
    funErrorBound = ACSL.ErrorDiseq (ACSL.FValue ACSL.FResult)
                                    (ACSL.EFun f ResValue ACSL.Real (map (ACSL.arg2var . args2ACSL) realArgs))
                                    (expr2acsl errorExpr)
    acslPred = ACSL.Implies (ACSL.PredAnd (ACSL.PredAnd (inputErrorBounds inputVarNames)
                                                        (errVarConstraints errArgs))
                                          (ACSL.IsValid ACSL.Result))
                            funErrorBound
    inputErrorBounds [] = ACSL.PredBExpr ACSL.BTrue
    inputErrorBounds varNames = foldl1 ACSL.PredAnd (map makeInputErrorBound varNames)
    makeInputErrorBound x = ACSL.ErrorDiseq (ACSL.FVar (fprec2acsl fp) x)
                                            (ACSL.Var ACSL.Real x)
                                            (ACSL.ErrorMark x (ACSL.format $ fprec2acsl fp))

defineLocalandErrVars :: [(VarName,FAExpr,FBExpr)] -> [(VarName,FAExpr)] -> ACSL.Pred -> ACSL.Pred
defineLocalandErrVars [] [] acslPred = acslPred
defineLocalandErrVars errVars locVars acslPred =
  ACSL.Implies (errVarConstraints errVars)
               (defLocalVars errVars locVars acslPred)

defLocalVars :: [(VarName,FAExpr,FBExpr)] -> [(VarName,FAExpr)] -> ACSL.Pred -> ACSL.Pred
defLocalVars [] [] acslPred = acslPred
defLocalVars errVars locVars acslPred = foldr defLocalVar acslPred vars
  where
    vars = reverse . elimDuplicates $ concatMap (aux . snd3) errVars
    aux var@(FVar _ x) = case lookup x locVars of
      Just ae -> (var,ae):concatMap aux (varList ae)
      Nothing -> []
    aux _ = []
    defLocalVar  (FVar t x,ae) accPred = ACSL.PredLet x (expr2acsl $ fae2real ae)
                                        (ACSL.FPredLet (fprec2acsl t) x (faexpr2acsl ae) accPred)
    defLocalVar ae _ = error $ "defLocalVars not defined for " ++ show ae

errVarConstraints :: [(VarName,FAExpr,FBExpr)] -> ACSL.Pred
errVarConstraints [] = ACSL.PredBExpr ACSL.BTrue
errVarConstraints errVars = foldl1 ACSL.PredAnd (map errVarConstraint errVars)

errVarConstraint :: (VarName,FAExpr,FBExpr) -> ACSL.Pred
errVarConstraint (errorVar, expr, FBTrue) = makeErrVarDiseq errorVar expr
errVarConstraint (errorVar, expr, be)     = ACSL.Implies (ACSL.PredFBExpr $ fbexpr2acsl be)
                                                         (makeErrVarDiseq errorVar expr)

quantifyIdx :: [(VarName, FAExpr, FAExpr)] -> ACSL.Pred -> ACSL.Pred
quantifyIdx [] acslPred = acslPred
quantifyIdx indexList acslPred = ACSL.Forall (zip (map fst3 indexList) (repeat ACSL.Int))
                                             (ACSL.Implies (ACSL.PredFBExpr $ idxRanges indexList) acslPred)

idxRanges :: [(VarName, FAExpr, FAExpr)] -> ACSL.FBExpr
idxRanges [] = ACSL.FBTrue
idxRanges indexList  = foldl1 ACSL.FAnd (map idxRange indexList)
  where
    idxRange (x,FInt n,FInt m) = ACSL.FBetween (ACSL.FInt n) (ACSL.FVar ACSL.Int x) (ACSL.FInt m)
    idxRange (x,ToFloat _ (Int n), ToFloat _ (Int m)) = ACSL.FBetween (ACSL.FInt n) (ACSL.FVar ACSL.Int x) (ACSL.FInt m)
    idxRange var = error $ "idxRanges not defined for " ++ show var

makeErrVarDiseq :: VarName -> FAExpr -> ACSL.Pred
makeErrVarDiseq errorVar expr = declareLetVars letList $ ACSL.FErrorDiseq (faexpr2acsl exprWithoutLet)
                                                         (expr2acsl $ fae2real exprWithoutLet)
                                                         (ACSL.FVar (ACSL.Float DoublePrec) errorVar)
  where
    letList = listLetElems expr
    exprWithoutLet = removeLetInFAExpr expr
    declareLetVars :: [FLetElem] -> ACSL.Pred -> ACSL.Pred
    declareLetVars [] pred = pred
    declareLetVars ((x,t,ae):rest) pred = ACSL.FPredLet (fprec2acsl t) x (faexpr2acsl ae)
                                        $ ACSL.PredLet  x (expr2acsl $ fae2real ae)
                                        $ declareLetVars rest pred

args2ACSL :: Arg -> ACSL.Arg
args2ACSL (Arg x fp) = ACSL.Arg (fprec2acsl fp) x

genAxiomaticRealFun :: Bool-> RDecl -> ACSL.Decl
genAxiomaticRealFun isRec (RDecl fp f args expr) = ACSL.Decl isRec (fprec2acsl fp) f (map args2ACSL args) (expr2acsl expr)
genAxiomaticRealFun _     (RPred    f args expr) = ACSL.RPred f (map args2ACSL args) (bexprStm2acsl expr)

genAxiomaticFPFun :: Bool-> Decl -> ACSL.FPDecl
genAxiomaticFPFun isRec (Decl _ fp f args expr) = ACSL.FPDecl isRec (fprec2acsl fp)
                                                                    (fpFunName f)
                                                                    (map args2ACSL args)
                                                                    (faexpr2acsl expr)
genAxiomaticFPFun _ (Pred _ _ f args expr) = ACSL.FPPred (fpFunName f)
                                                         (map args2ACSL args)
                                                         (fbexprStm2acsl expr)

letElem2acsl :: LetElem -> ACSL.LetElem
letElem2acsl letElem = (x,fprec2acsl t,expr2acsl ae)
  where
    x  = letVar  letElem
    t  = letType letElem
    ae = letExpr letElem

fletElem2acsl :: FLetElem -> ACSL.FLetElem
fletElem2acsl (x,t,ae) = (x,fprec2acsl t,faexpr2acsl ae)

faexpr2acsl :: FAExpr -> ACSL.FAExpr
faexpr2acsl (FInt i)       = ACSL.FInt i
faexpr2acsl (FCnst fp rat) = ACSL.FCnst (fprec2acsl fp) rat
faexpr2acsl (FVar  fp x)   = ACSL.FVar  (fprec2acsl fp) x
faexpr2acsl (Value expr)   = ACSL.FValue (faexpr2acsl expr)
-- faexpr2acsl (FArrayElem fp size v exprs) = ACSL.FArrayElem (fprec2acsl fp) size v (map faexpr2acsl exprs)
faexpr2acsl (TypeCast fp1 fp2 expr) = ACSL.FTypeCast (fprec2acsl fp1) (fprec2acsl fp2) (faexpr2acsl expr)
faexpr2acsl (ToFloat  fp      expr) = ACSL.ToFloat   (fprec2acsl fp)                   (expr2acsl expr)
faexpr2acsl (FEFun _ f field fp args) = ACSL.FEFun (fpFunName f) field (fprec2acsl fp) (map faexpr2acsl args)
faexpr2acsl (BinaryFPOp op fp expr1 expr2) = ACSL.BinaryFPOp op (fprec2acsl fp) (faexpr2acsl expr1) (faexpr2acsl expr2)
faexpr2acsl (UnaryFPOp  op fp expr)        = ACSL.UnaryFPOp op (fprec2acsl fp) (faexpr2acsl expr)
faexpr2acsl (FFma fp expr1 expr2 expr3)    = ACSL.FFma (fprec2acsl fp) (faexpr2acsl expr1) (faexpr2acsl expr2) (faexpr2acsl expr3)
faexpr2acsl (FMin ees) = ACSL.FMin (map faexpr2acsl ees)
faexpr2acsl (FMax ees) = ACSL.FMax (map faexpr2acsl ees)
faexpr2acsl (Let letElems body)  = ACSL.FLet (map fletElem2acsl letElems) (faexpr2acsl body)
faexpr2acsl (Ite be  thenExpr elseExpr) = ACSL.FIte (fbexpr2acsl be) (faexpr2acsl thenExpr) (faexpr2acsl elseExpr)
faexpr2acsl (ListIte listThen elseExpr) = ACSL.FListIte (map (bimap fbexpr2acsl faexpr2acsl) listThen)
                                                        (faexpr2acsl elseExpr)
faexpr2acsl a = error $ "faexpr2acsl niy for " ++ show a

bexprStm2acsl :: BExprStm -> ACSL.BExprStm
bexprStm2acsl (RBLet letElems body) = ACSL.RBLet (map letElem2acsl letElems) (bexprStm2acsl body)
bexprStm2acsl (RBIte be stmThen stmElse) = ACSL.RBIte (bexpr2acsl be)
                                                      (bexprStm2acsl stmThen)
                                                      (bexprStm2acsl stmElse)
bexprStm2acsl (RBListIte listThen stmElse) = ACSL.RBListIte (map (bimap bexpr2acsl bexprStm2acsl) listThen)
                                                            (bexprStm2acsl stmElse)
bexprStm2acsl (RBExpr be) = ACSL.RBExpr $ bexpr2acsl be

fbexprStm2acsl :: FBExprStm -> ACSL.FBExprStm
fbexprStm2acsl (BLet letElems body) = ACSL.BLet (map fletElem2acsl letElems) (fbexprStm2acsl body)
fbexprStm2acsl (BIte be stmThen stmElse) = ACSL.BIte (fbexpr2acsl be)
                                                     (fbexprStm2acsl stmThen)
                                                     (fbexprStm2acsl stmElse)
fbexprStm2acsl (BListIte listThen stmElse) = ACSL.BListIte (map (bimap fbexpr2acsl fbexprStm2acsl) listThen)
                                                           (fbexprStm2acsl stmElse)
fbexprStm2acsl (BExpr be) = ACSL.BExpr $ fbexpr2acsl be
fbexprStm2acsl BUnstWarning = error "fbexprStm2acsl undefined for BUnstWarning."

fbexpr2acsl :: FBExpr -> ACSL.FBExpr
fbexpr2acsl FBTrue  = ACSL.FBTrue
fbexpr2acsl FBFalse = ACSL.FBFalse
fbexpr2acsl (FOr  be1 be2) = ACSL.FOr  (fbexpr2acsl be1) (fbexpr2acsl be2)
fbexpr2acsl (FAnd be1 be2) = ACSL.FAnd (fbexpr2acsl be1) (fbexpr2acsl be2)
fbexpr2acsl (FNot be)      = ACSL.FNot (fbexpr2acsl be)
fbexpr2acsl (FRel rel expr1 expr2) = ACSL.FRel rel (faexpr2acsl expr1) (faexpr2acsl expr2)
fbexpr2acsl (FEPred _ predAbs p args) = ACSL.FEPred predAbs (fpFunName p) (map faexpr2acsl args)
fbexpr2acsl be     = error $ "fbexpr2acsl not defined for " ++ show be

expr2acsl :: AExpr -> ACSL.AExpr
expr2acsl (Int i)                      = ACSL.IntCnst i
expr2acsl (Rat rat)                    = ACSL.RatCnst rat
expr2acsl (ErrRat rat)                 = ACSL.ErrorCnst (fromRational rat)
expr2acsl (Var fp x)                   = ACSL.Var (fprec2acsl fp) x
expr2acsl (RealMark x ResValue)        = ACSL.Var ACSL.Real x
expr2acsl (ErrorMark x ResValue fp)             = ACSL.ErrorMark x (ACSL.format $ fprec2acsl fp)
-- expr2acsl (ArrayElem _ _ v args)       = ACSL.ArrayElem v (map expr2acsl args)
expr2acsl (EFun f field fp args)       = ACSL.EFun f field (fprec2acsl fp) (map expr2acsl args)
expr2acsl (BinaryOp op expr1 expr2)    = ACSL.BinaryOp op (expr2acsl expr1) (expr2acsl expr2)
expr2acsl (UnaryOp  op expr)           = ACSL.UnaryOp  op (expr2acsl expr)
expr2acsl (FromFloat fp (FInt i))      = ACSL.FromFloat (ACSL.format $ fprec2acsl fp) (ACSL.IntCnst i)
expr2acsl (FromFloat fp (FCnst _ rat)) = ACSL.FromFloat (ACSL.format $ fprec2acsl fp) (ACSL.RatCnst rat)
expr2acsl (FromFloat _ ae)             = error $ "expr2acsl: fromFloat not defined for " ++ show ae
expr2acsl (Min exprs)                  = ACSL.Min (map expr2acsl exprs)
expr2acsl (Max exprs)                  = ACSL.Max (map expr2acsl exprs)
expr2acsl (MaxErr exprs)               = ACSL.MaxErr (map expr2acsl exprs)
expr2acsl (RLet letElems stm)          = ACSL.Let (map letElem2acsl letElems) (expr2acsl stm)
expr2acsl (RIte be  thenExpr elseExpr) = ACSL.Ite (bexpr2acsl be)  (expr2acsl thenExpr) (expr2acsl elseExpr)
expr2acsl (RListIte listThen elseExpr) = ACSL.ListIte (zip (map (bexpr2acsl . fst) listThen) (map (expr2acsl . snd) listThen)) (expr2acsl elseExpr)
expr2acsl (ErrBinOp op fp ae1 ee1 ae2 ee2) = ACSL.ErrBinOp op (fprec2acsl fp) (expr2acsl ae1) (expr2acsl ee1) (expr2acsl ae2) (expr2acsl ee2)
expr2acsl (ErrUnOp  op fp ae ee) = ACSL.ErrUnOp op (fprec2acsl fp) (expr2acsl ae) (expr2acsl ee)
expr2acsl (ErrMulPow2R fp n ae) = ACSL.ErrMulPow2R (ACSL.format $ fprec2acsl fp) n (expr2acsl ae)
expr2acsl (ErrMulPow2L fp n ae) = ACSL.ErrMulPow2L (ACSL.format $ fprec2acsl fp) n (expr2acsl ae)
expr2acsl (HalfUlp ae fp)       = ACSL.HalfUlp (ACSL.format $ fprec2acsl fp) (expr2acsl ae)
expr2acsl (ErrCast t1 t2 ae1 ae2) = ACSL.ErrCast (fprec2acsl t1) (fprec2acsl t2) (expr2acsl ae1) (expr2acsl ae2)
expr2acsl RForLoop{} = error "Real valued ForLoop not supported."
-- RForLoop fp idxStart idxEnd initAcc idx acc body
expr2acsl ae = error $ "expr2acsl not defined for " ++ show ae

bexpr2acsl :: BExpr -> ACSL.BExpr
bexpr2acsl BTrue  = ACSL.BTrue
bexpr2acsl BFalse = ACSL.BFalse
bexpr2acsl (Or  be1 be2) = ACSL.Or  (bexpr2acsl be1) (bexpr2acsl be2)
bexpr2acsl (And be1 be2) = ACSL.And (bexpr2acsl be1) (bexpr2acsl be2)
bexpr2acsl (Not be)      = ACSL.Not (bexpr2acsl be)
bexpr2acsl (Rel rel ae1 ae2) = ACSL.Rel rel (expr2acsl ae1) (expr2acsl ae2)
bexpr2acsl (EPred f args) = ACSL.EPred f (map expr2acsl args)

varBinds2BExpr :: [VarBind] -> ACSL.BExpr
varBinds2BExpr [] = ACSL.BTrue
varBinds2BExpr varBinds = foldl1 ACSL.And (map varBind2BExpr varBinds)
  where
    varBind2BExpr (VarBind _ _ _ LInf UInf)
      = ACSL.BTrue
    varBind2BExpr (VarBind x field fp LInf (UBInt n))
      = ACSL.Rel LtE (ACSL.Var (fprec2RealType fp) x) (ACSL.IntCnst n)
    varBind2BExpr (VarBind x field fp LInf (UBDouble r))
      = ACSL.Rel LtE (ACSL.Var (fprec2RealType fp) x) (ACSL.RatCnst r)
    varBind2BExpr (VarBind x field fp (LBInt n) UInf)
      = ACSL.Rel LtE (ACSL.IntCnst n) (ACSL.Var (fprec2RealType fp) x)
    varBind2BExpr (VarBind x field fp (LBDouble r) UInf)
      = ACSL.Rel LtE (ACSL.RatCnst r) (ACSL.Var (fprec2RealType fp) x)
    varBind2BExpr (VarBind x field fp (LBInt lb) (UBInt ub))
      = ACSL.And (ACSL.Rel LtE (ACSL.IntCnst lb) (ACSL.Var (fprec2RealType fp) x))
                 (ACSL.Rel LtE (ACSL.Var (fprec2RealType fp) x) (ACSL.IntCnst ub))
    varBind2BExpr (VarBind x field fp (LBDouble lb) (UBDouble ub))
      = ACSL.And (ACSL.Rel LtE (ACSL.RatCnst lb) (ACSL.Var (fprec2RealType fp) x))
                 (ACSL.Rel LtE (ACSL.Var (fprec2RealType fp) x) (ACSL.RatCnst ub))
    varBind2BExpr (VarBind x field fp (LBInt lb) (UBDouble ub))
      = ACSL.And (ACSL.Rel LtE (ACSL.IntCnst lb) (ACSL.Var (fprec2RealType fp) x))
                 (ACSL.Rel LtE (ACSL.Var (fprec2RealType fp) x) (ACSL.RatCnst ub))
    varBind2BExpr (VarBind x field fp (LBDouble lb) (UBInt ub))
      = ACSL.And (ACSL.Rel LtE (ACSL.RatCnst lb) (ACSL.Var (fprec2RealType fp) x))
                 (ACSL.Rel LtE (ACSL.Var (fprec2RealType fp) x) (ACSL.IntCnst ub))

numPostCondition :: HasConditionals
                 -> FunName
                 -> [ACSL.AExpr]
                 -> Map.Map ResultField Double
                 -> ACSL.Pred
numPostCondition isMaybe f actArgs roErrMap
  | Map.keys roErrMap == [ResValue] = ACSL.PredBExpr $ ACSL.Rel LtE err (ACSL.ErrorCnst roErr)
  | otherwise = error "numPostCondition: record field not supported yet"
    where
      roErr = fromJust $ Map.lookup ResValue roErrMap
      err = ACSL.UnaryOp AbsOp (ACSL.BinaryOp SubOp (if (isMaybe f) then ACSL.Value ACSL.Result else ACSL.Result)
                             (ACSL.EFun f ResValue ACSL.Real actArgs) )

generateNumericProp :: HasConditionals
                    -> Maybe PredAbs
                    -> PVSType
                    -> ACSL.FunName
                    -> [(String, FAExpr, FAExpr)]
                    -> [Arg]
                    -> Map.Map ResultField Double
                    -> [(VarName,FAExpr)]
                    -> [VarBind]
                    -> [FAExpr]
                    -> ACSL.Pred
generateNumericProp isMaybe predAbs fp f indexList fpArgs roErrs locVars varBinds isFiniteExprList =
  ACSL.Ensures (defineLocalandErrVars [] locVars $
                (quantifyVar $ ACSL.Implies (ACSL.PredAnd (initRangesProp varBinds indexList)
                                            (ACSL.PredAnd ((if (isMaybe f)
                                                then (ACSL.PredAnd (ACSL.IsValid ACSL.Result))
                                                else id)
                                                (isFiniteHypothesis isFiniteExprList))
                                               (listInputVarErr notIntArgs) ))
                                            postCond))
  where
    postCond | isPredicate = predPostCond isMaybe (fromJust predAbs) f actArgs
             | otherwise   = numPostCondition isMaybe f actArgs roErrs
    actArgs = map (ACSL.arg2var . args2ACSL) fpArgs
    notIntArgs = filter (not . isArgInt) fpArgs
    quantifyVar = ACSL.Forall (map (\(ACSL.Var t x) -> (x,t)) actArgs)
    listInputVarErr [] = ACSL.PredBExpr $ ACSL.BTrue
    listInputVarErr listNotIntArgs = foldl1 ACSL.PredAnd $ map (makeInputErrorBound . ACSL.arg2fpvarWithType (fprec2acsl fp) . args2ACSL) listNotIntArgs
    makeInputErrorBound var@(ACSL.FVar (ACSL.Float fpvar) x) = ACSL.ErrorDiseq var
                                             (ACSL.Var ACSL.Real x)
                                             (ACSL.HalfUlp fpvar (ACSL.Var ACSL.Real x))
    makeInputErrorBound expr = error $ "makeInputErrorBound not defined for " ++ show expr ++ ""
    isPredicate = predAbs /= Nothing

predPostCond :: HasConditionals -> PredAbs -> ACSL.FunName -> [ACSL.AExpr] -> ACSL.Pred
predPostCond isMaybe predAbs f actArgs
  | isTauPlus  predAbs = ACSL.Implies (ACSL.AExprPred $ (if (isMaybe f) then ACSL.Value else id) ACSL.Result)
                                      (ACSL.AExprPred $ ACSL.EFun f ResValue ACSL.Real actArgs)
  | isTauMinus predAbs = ACSL.Implies (ACSL.AExprPred $ (if (isMaybe f) then ACSL.Value else id) ACSL.Result)
                                      (ACSL.PredNot $ ACSL.AExprPred $ ACSL.EFun f ResValue ACSL.Real actArgs)
  | otherwise = ACSL.Iff (ACSL.AExprPred $ (if (isMaybe f) then ACSL.Value else id) ACSL.Result)
                         (ACSL.AExprPred $ ACSL.EFun f ResValue ACSL.Real actArgs)

initRangesProp :: [VarBind] -> [(VarName, FAExpr, FAExpr)] -> ACSL.Pred
initRangesProp varBinds [] = ACSL.PredBExpr (varBinds2BExpr varBinds)
initRangesProp varBinds indexList = ACSL.Implies idxQuantification (ACSL.PredBExpr $ varBinds2BExpr varBinds)
  where
    idxQuantification = ACSL.Forall (zip (map fst3 indexList) (repeat ACSL.Int)) (ACSL.PredFBExpr (idxRanges indexList))
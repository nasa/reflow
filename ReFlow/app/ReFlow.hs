-- Notices:
-- Copyright 2023 United States Government as represented by the Administrator of the National Aeronautics and Space Administration. All Rights Reserved.

-- This software calls the NASA Software named “PRECiSA with Instrumented Code Generation” LAR-19739-1, which is not bundled or redistributed with this software, but users of this software must obtain their own NASA license, which is subject to the terms and conditions of the applicable at the time.

-- Disclaimers
-- No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE. THIS AGREEMENT DOES NOT, IN ANY MANNER, CONSTITUTE AN ENDORSEMENT BY GOVERNMENT AGENCY OR ANY PRIOR RECIPIENT OF ANY RESULTS, RESULTING DESIGNS, HARDWARE, SOFTWARE PRODUCTS OR ANY OTHER APPLICATIONS RESULTING FROM USE OF THE SUBJECT SOFTWARE.  FURTHER, GOVERNMENT AGENCY DISCLAIMS ALL WARRANTIES AND LIABILITIES REGARDING THIRD-PARTY SOFTWARE, IF PRESENT IN THE ORIGINAL SOFTWARE, AND DISTRIBUTES IT "AS IS."

-- Waiver and Indemnity:  RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS AGAINST THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT.  IF RECIPIENT'S USE OF THE SUBJECT SOFTWARE RESULTS IN ANY LIABILITIES, DEMANDS, DAMAGES, EXPENSES OR LOSSES ARISING FROM SUCH USE, INCLUDING ANY DAMAGES FROM PRODUCTS BASED ON, OR RESULTING FROM, RECIPIENT'S USE OF THE SUBJECT SOFTWARE, RECIPIENT SHALL INDEMNIFY AND HOLD HARMLESS THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW.  RECIPIENT'S SOLE REMEDY FOR ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL TERMINATION OF THIS AGREEMENT.


{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ReFlow
  ( main,
  )
where

import AbsPVSLang (RProgram,FunName,Decl(..),Arg,AExpr,FAExpr)
import AbstractSemantics (SemanticConfiguration(..),fixpointSemantics,botInterp,semantics,stableConditions,maxRoundOffError,unfoldSemantics,)
import AbstractDomain (Conditions)
import Common.DecisionPath (LDecisionPath)
import Common.ControlFlow (ControlFlow(..))
import ErrM (errify)
import PVSTypes (PVSType(..))
import FramaC.PrettyPrint (genFramaCFile)
import FramaC.PrecisaPrelude (precisaPreludeContent)
import Options (Options(..),parseOptions)
import PPExt (render,vcat)
import Kodiak.Runner (KodiakResult(..))
import Kodiak.Paver (SearchParameters(..))
import Prelude hiding ((<>))
import PVSCert (genFpProgFile,genCertFile,genNumCertFile,genExprCertFile,printExprFunCert)
import Parser.Parser (parseFileToRealProgram,parseFileToSpec)
import System.FilePath (dropFileName,takeBaseName)
import Transformation (transformProgramSymb)
import TransformationUtils (computeErrorGuards)
import Translation.Real2Float (real2fpProg)

import qualified PRECiSA (computeAllErrorsInKodiak,computeAllErrorsInKodiakMap)

main :: IO ()
main = do
  options <- parseOptions
  generateCProg options

parseRealProg :: FilePath -> IO RProgram
parseRealProg fileprog = do
  errparseProg <- parseFileToRealProgram fileprog
  errify error errparseProg

generateCProg :: Options -> IO ()
generateCProg
  Options
    { optRealProgramFile     = prog
    , optRealInputRangeFile  = inputs
    , targetFormat           = fprec
    , optMaxDepth            = maxDepth
    , optMinPrec             = minPrec}
  = case fprec of
    "double" ->  real2FPC maxDepth minPrec prog inputs FPDouble
    "single" ->  real2FPC maxDepth minPrec prog inputs FPSingle
    _ -> error ""

normalizeBoolExpr :: Bool
normalizeBoolExpr = True

real2FPC :: Int -> Int ->  FilePath -> FilePath -> PVSType -> IO ()
real2FPC maxBBDepth prec fileprog filespec fp = do
  putStrLn "Parsing..."
  realProg <- parseRealProg fileprog
  putStrLn "..done!\n"

  -- fp progam
  putStrLn "Generating symbolic transformed program..."
  let decls = real2fpProg normalizeBoolExpr fp realProg
  errparseSpec <- parseFileToSpec decls filespec
  spec <- errify fail errparseSpec
  let dpsNone = map initDpsToNone decls
  -- transfromed program --
  let tranProgTuples = transformProgramSymb realProg decls
  putStrLn "..done!\n"

  -- program semantics
  putStrLn "Computing the round-off errors..."

  let progSem = fixpointSemantics decls (botInterp decls) 3 semConf dpsNone
  let maxDepth = fromInteger . toInteger $ maxBBDepth
  let minPrec = fromInteger . toInteger $ prec
  let searchParams = SP { maximumDepth = maxDepth
                        , minimumPrecision = minPrec}
  let unfoldedPgmSem = unfoldSemantics progSem

  let optUnfoldFuns = False

  results <- if optUnfoldFuns
              then PRECiSA.computeAllErrorsInKodiakMap unfoldedPgmSem spec searchParams
              else PRECiSA.computeAllErrorsInKodiak True unfoldedPgmSem spec searchParams
  -- let resultSummary = summarizeAllErrors (getKodiakResults results)

  putStrLn "..done!\n"

    -- numerical round-off errors declarations
  let numROErrorsDecl = summarizeAllStableErrors (getKodiakResults results)
  let progStableConds = map (stableConditions . semantics) progSem
  let progSymbRoundOffErrs = map (maxRoundOffError . semantics) progSem
  -- symbolic round-off errors error vars
  let roErrorsDecl = zip (map fst progSem) (zip progSymbRoundOffErrs progStableConds)

  putStrLn "Computing the new conditions..."

  -- numerical round-off errors error vars
  funErrEnv <- mapM (computeErrorGuards maxDepth minPrec spec unfoldedPgmSem numROErrorsDecl) tranProgTuples
  putStrLn "..done!\n"

  putStrLn "Generating Frama-C program..."
  let framaCfileContent = genFramaCFile fp spec realProg decls tranProgTuples roErrorsDecl numROErrorsDecl funErrEnv progSem
  writeFile framaCfile (render framaCfileContent)
  -- writeFile precisaPreludeFile (render precisaPreludeContent)
  putStrLn "..done!\n"

  putStrLn "Generating PVS files..."
  writeFile pvsProgFile (render $ genFpProgFile fp fpFileName decls)

  let symbCertificate = render $ genCertFile fpFileName certFileName inputFileName decls progSem
  writeFile certFile symbCertificate

  let numCertificate = render $ genNumCertFile certFileName numCertFileName results decls spec maxBBDepth prec True
  writeFile numCertFile numCertificate

  let guardExpressionsCert = render $ genExprCertFile fp inputFileName fpFileName exprCertFileName
                             (vcat (map (printExprFunCert maxBBDepth prec fp) funErrEnv))
  writeFile exprCertFile guardExpressionsCert
  putStrLn "..done!\n"

  putStrLn $ "PRECiSA: instrumented C code and PVS certificate generated in " ++ filePath ++ "."

  return ()
    where
      precisaPreludeFile = filePath ++ "precisa_prelude.c"
      inputFileName = takeBaseName fileprog
      fpFileName = inputFileName ++ "_fp"
      filePath = dropFileName fileprog
      framaCfile = filePath ++ inputFileName ++ ".c"
      pvsProgFile = filePath ++ fpFileName ++ ".pvs"
      certFileName = "cert_" ++ inputFileName
      numCertFileName = inputFileName ++ "_num_cert"
      exprCertFileName = inputFileName ++ "_expr_cert"
      exprCertFile = filePath ++ exprCertFileName ++ ".pvs"
      certFile =  filePath ++ certFileName ++ ".pvs"
      numCertFile =  filePath ++ numCertFileName ++ ".pvs"
      semConf = SemConf { improveError = False
                        , unfoldFunCalls = False
                        , assumeTestStability = True
                        , mergeUnstables = True}

initDpsToNone :: Decl -> (FunName, [LDecisionPath])
initDpsToNone (Decl _ _ f _ _) = (f,[])
initDpsToNone (Pred _ _ f _ _) = (f,[])

getKodiakResults :: [(String,PVSType,[Arg],[(Conditions, LDecisionPath,ControlFlow,KodiakResult,AExpr,[FAExpr],[AExpr])])] -> [(String, [(ControlFlow,KodiakResult)])]
getKodiakResults = map getKodiakResult
  where
     getKodiakResult (f,_,_,errors) = (f, map getKodiakError errors)
     getKodiakError (_,_,cf,err,_,_,_) = (cf,err)

summarizeAllStableErrors :: [(String, [(ControlFlow, KodiakResult)])] -> [(String, Double)]
summarizeAllStableErrors errorMap = map aux errorMap
  where
    aux (f, results) = (f,maximum $ map (maximumUpperBound . snd) (filter ((== Stable) . fst) results))

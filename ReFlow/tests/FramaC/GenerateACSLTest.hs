-- Notices:
-- Copyright 2023 United States Government as represented by the Administrator of the National Aeronautics and Space Administration. All Rights Reserved.

-- This software calls the NASA Software named “PRECiSA with Instrumented Code Generation” LAR-19739-1, which is not bundled or redistributed with this software, but users of this software must obtain their own NASA license, which is subject to the terms and conditions of the applicable at the time.

-- Disclaimers
-- No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE. THIS AGREEMENT DOES NOT, IN ANY MANNER, CONSTITUTE AN ENDORSEMENT BY GOVERNMENT AGENCY OR ANY PRIOR RECIPIENT OF ANY RESULTS, RESULTING DESIGNS, HARDWARE, SOFTWARE PRODUCTS OR ANY OTHER APPLICATIONS RESULTING FROM USE OF THE SUBJECT SOFTWARE.  FURTHER, GOVERNMENT AGENCY DISCLAIMS ALL WARRANTIES AND LIABILITIES REGARDING THIRD-PARTY SOFTWARE, IF PRESENT IN THE ORIGINAL SOFTWARE, AND DISTRIBUTES IT "AS IS."

-- Waiver and Indemnity:  RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS AGAINST THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT.  IF RECIPIENT'S USE OF THE SUBJECT SOFTWARE RESULTS IN ANY LIABILITIES, DEMANDS, DAMAGES, EXPENSES OR LOSSES ARISING FROM SUCH USE, INCLUDING ANY DAMAGES FROM PRODUCTS BASED ON, OR RESULTING FROM, RECIPIENT'S USE OF THE SUBJECT SOFTWARE, RECIPIENT SHALL INDEMNIFY AND HOLD HARMLESS THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW.  RECIPIENT'S SOLE REMEDY FOR ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL TERMINATION OF THIS AGREEMENT.

module FramaC.GenerateACSLTest where

import qualified AbsPVSLang as PVS
import Common.TypesUtils
import FramaC.ACSLTypes
import FramaC.ACSLlang
import FramaC.GenerateACSL
import Operators
import qualified PVSTypes as PVS
import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (Eq)
import AbsPVSLang (ResultField(..))

true = PredBExpr BTrue

test =testGroup  "ACSL Generation" [
   behaviorStructure__test
  ,behaviorStructurePred__test
  ,isFiniteHypothesis__test
  ,predPostCond__test
  ,behaviorStablePaths__test
  ]

behaviorStablePaths__test = testGroup "behaviorStablePaths"
  [ testCase "behaviorStablePaths with let" $
    behaviorStablePaths "greater_than" (Just TauPlus) (Float DoublePrec)
                        [PVS.Arg "a" PVS.Real, PVS.Arg "b" PVS.Real]
                        [("E_0",PVS.Let [("a_minus_b",PVS.FPDouble,PVS.BinaryFPOp SubOp PVS.FPDouble
                        (PVS.FVar PVS.FPDouble "a") (PVS.FVar PVS.FPDouble "b"))](PVS.FVar PVS.FPDouble"a_minus_b"),PVS.FBTrue)]
                        [][]
                        ["a"
                        ,"b"
                        ,"E_0"
                        ,"a_minus_b"]
    @?=
      Ensures (Forall [("a",Real),("b",Real)] (Implies (FPredLet (Float DoublePrec) "a_minus_b" (BinaryFPOp SubOp (Float DoublePrec) (FVar (Float DoublePrec) "a") (FVar (Float DoublePrec) "b")) (PredLet "a_minus_b" (BinaryOp SubOp (Var Real "a") (Var Real "b")) (FErrorDiseq (FVar (Float DoublePrec) "a_minus_b") (Var Real "a_minus_b") (FVar (Float DoublePrec) "E_0")))) (Implies (PredAnd ( (PredAnd (PredAnd (PredAnd (IsFiniteFP (FVar (Float DoublePrec) "a")) (IsFiniteFP (FVar (Float DoublePrec) "b"))) (IsFiniteFP (FVar (Float DoublePrec) "E_0"))) (IsFiniteFP (FVar (Float DoublePrec) "a_minus_b"))) ) (IsValid Result)) (Pred "greater_than_tauplus_stable_paths" [Var Real "a",Var Real "b",Var (Float DoublePrec) "a",Var (Float DoublePrec) "b"]))))
  ]

behaviorStructure__test = testGroup "behaviorStructure"
  [ testCase "no args no conditions no expression list" $
      behaviorStructure (\_ -> False) (Float DoublePrec) "f" [] []
        @?= Ensures (Implies (IsValid Result) (PredFBExpr (EqualFP FResult (FEFun "f_fp" ResValue (Float DoublePrec) [])))),
    testCase "no args conditions no expression list" $
      behaviorStructure (\_ -> True) (Float DoublePrec) "f" [] []
        @?= Ensures (Implies (IsValid Result) (PredFBExpr (EqualFP (FValue FResult) (FEFun "f_fp" ResValue (Float DoublePrec) []))))
  ]

behaviorStructurePred__test = testGroup  "behaviorStructurePred"
  [ testCase "tauplus no args no conditions no expression list" $
      behaviorStructurePred (\_ -> False) (Float DoublePrec) TauPlus "f" [] [] []
        @?= Ensures (Implies (PredAnd (IsValid Result) (PredBExpr BTrue)) (Implies (AExprPred Result) (PredAnd (AExprPred (EFun "f" ResValue Real [])) (FAExprPred (FEFun "f_fp" ResValue (Float DoublePrec) [])))))
  , testCase "tauplus no args with conditions no expression list" $
      behaviorStructurePred (\_ -> True) (Float DoublePrec) TauPlus "f" [] [] []
        @?=
          Ensures (Implies (IsValid Result)
            (Implies (AExprPred (Value Result))
                     (PredAnd (AExprPred (EFun "f" ResValue Real []))
                              (FAExprPred (FEFun "f_fp" ResValue (Float DoublePrec) [])))))
  , testCase "tauminus no args no conditions no expression list" $
      behaviorStructurePred (\_ -> False) (Float DoublePrec) TauMinus "f" [] [] []
        @?= Ensures (Implies (PredAnd (IsValid Result) (PredBExpr BTrue)) (Implies (AExprPred Result) (PredAnd (PredNot (AExprPred (EFun "f" ResValue Real []))) (PredNot (FAExprPred (FEFun "f_fp" ResValue (Float DoublePrec) []))))))
  , testCase "tauminus no args with conditions no expression list" $
      behaviorStructurePred (\_ -> True) (Float DoublePrec) TauMinus "f" [] [] []
        @?=
          Ensures (Implies (IsValid Result)
          (Implies (AExprPred (Value Result))
                   (PredAnd (PredNot $ AExprPred (EFun "f" ResValue Real []))
                            (PredNot $ FAExprPred (FEFun "f_fp" ResValue (Float DoublePrec) [])))))
  , testCase "original no args no conditions no expression list" $
      behaviorStructurePred (\_ -> False) (Float DoublePrec) Original "f" [] [] []
        @?= Ensures (Implies (PredAnd (IsValid Result) (PredBExpr BTrue)) (PredAnd (Implies (AExprPred Result) (PredAnd (AExprPred (EFun "f" ResValue Real [])) (FAExprPred (FEFun "f_fp" ResValue (Float DoublePrec) [])))) (Implies (PredNot (AExprPred Result)) (PredAnd (PredNot (AExprPred (EFun "f" ResValue Real []))) (PredNot (FAExprPred (FEFun "f_fp" ResValue (Float DoublePrec) [])))))))
  , testCase "original no args with conditions no expression list" $
      behaviorStructurePred (\_ -> True) (Float DoublePrec) Original "f" [] [] []
        @?=
          Ensures (Implies (IsValid Result)
          (PredAnd
          (Implies (AExprPred (Value Result))
                   (PredAnd (AExprPred (EFun "f" ResValue Real []))
                            (FAExprPred (FEFun "f_fp" ResValue (Float DoublePrec) []))))
          (Implies (PredNot $ AExprPred (Value Result))
                   (PredAnd (PredNot $ AExprPred (EFun "f" ResValue Real []))
                            (PredNot $ FAExprPred (FEFun "f_fp" ResValue (Float DoublePrec) []))))))
  ]

isFiniteHypothesis__test = testGroup
  "isFiniteHypothesis"
  [ testCase "no conditions and an empty expression list" $
      isFiniteHypothesis [] @?= PredBExpr BTrue,
    testCase "with conditions and an empty expression list" $
      isFiniteHypothesis [] @?= PredBExpr BTrue,
    testCase "no conditions and one expression" $
      isFiniteHypothesis [PVS.FVar PVS.FPDouble "x"]
        @?= IsFiniteFP (FVar (Float DoublePrec) "x"),
    testCase "with conditions and one expression" $
      isFiniteHypothesis [PVS.FVar PVS.FPDouble "x"]
        @?= IsFiniteFP (FVar (Float DoublePrec) "x")
  ]

predPostCond__test = testGroup "predPostCond"
  [ testCase "no conditions, tauplus and an empty expression list " $
      predPostCond (\_ -> False) TauPlus "f" []
        @?= Implies (AExprPred Result)
                    (AExprPred $ EFun "f" ResValue Real [])
  , testCase "no conditions, tauminus and an empty expression list " $
      predPostCond (\_ -> False) TauMinus "f" []
        @?= Implies (AExprPred Result)
                    (PredNot $ AExprPred $ EFun "f" ResValue Real [])
  , testCase "no conditions, original and an empty expression list " $
      predPostCond (\_ -> False) Original "f" []
        @?= Iff (AExprPred Result)
                (AExprPred $ EFun "f" ResValue Real [])
  , testCase "with conditions, tauplus and an empty expression list " $
      predPostCond (\ _ -> True) TauPlus "f" []
        @?= Implies (AExprPred $ Value Result)
                    (AExprPred $ EFun "f" ResValue Real [])
  , testCase "with conditions, tauminus and an empty expression list " $
      predPostCond (\_ -> True) TauMinus "f" []
        @?= Implies (AExprPred $ Value Result)
                    (PredNot $ AExprPred $ EFun "f" ResValue Real [])
  , testCase "with conditions, original and an empty expression list " $
      predPostCond (\_ -> True) Original "f" []
        @?= Iff (AExprPred $ Value Result)
                   (AExprPred $ EFun "f" ResValue Real [])
  ]
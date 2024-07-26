-- Notices:
-- Copyright 2023 United States Government as represented by the Administrator of the National Aeronautics and Space Administration. All Rights Reserved.

-- This software calls the NASA Software named “PRECiSA with Instrumented Code Generation” LAR-19739-1, which is not bundled or redistributed with this software, but users of this software must obtain their own NASA license, which is subject to the terms and conditions of the applicable at the time.

-- Disclaimers
-- No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE. THIS AGREEMENT DOES NOT, IN ANY MANNER, CONSTITUTE AN ENDORSEMENT BY GOVERNMENT AGENCY OR ANY PRIOR RECIPIENT OF ANY RESULTS, RESULTING DESIGNS, HARDWARE, SOFTWARE PRODUCTS OR ANY OTHER APPLICATIONS RESULTING FROM USE OF THE SUBJECT SOFTWARE.  FURTHER, GOVERNMENT AGENCY DISCLAIMS ALL WARRANTIES AND LIABILITIES REGARDING THIRD-PARTY SOFTWARE, IF PRESENT IN THE ORIGINAL SOFTWARE, AND DISTRIBUTES IT "AS IS."

-- Waiver and Indemnity:  RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS AGAINST THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT.  IF RECIPIENT'S USE OF THE SUBJECT SOFTWARE RESULTS IN ANY LIABILITIES, DEMANDS, DAMAGES, EXPENSES OR LOSSES ARISING FROM SUCH USE, INCLUDING ANY DAMAGES FROM PRODUCTS BASED ON, OR RESULTING FROM, RECIPIENT'S USE OF THE SUBJECT SOFTWARE, RECIPIENT SHALL INDEMNIFY AND HOLD HARMLESS THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW.  RECIPIENT'S SOLE REMEDY FOR ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL TERMINATION OF THIS AGREEMENT.


module TransformationUtilsTest where

import Test.Tasty
import Test.Tasty.HUnit
import Transformation
import TransformationUtils
import AbsPVSLang
import AbsSpecLang
import Control.Monad.State
import Operators
import qualified Data.Map as Map

returnsValueEqualTo :: (Eq a, Show a) => IO a -> a -> IO ()
returnsValueEqualTo lhs rhs = lhs >>= (@?= rhs)

returnsValueEqualTo':: State TranStateInterp FAExpr -> FAExpr -> IO ()
returnsValueEqualTo' lhs rhs = return (fst $ runState lhs initState) `returnsValueEqualTo` rhs
  where
    initState = [("f",TransState { freshErrVar = FreshErrVar { env = [], count = 0, localEnv = [] },
                                                     forExprMap = [] })]

checkOutputIs :: (Eq a, Show a) => IO a -> a -> IO ()
checkOutputIs actual expected =
  actual >>=
      \out ->
          (out == expected)
              @? ("Output: " ++ show out ++ " is different than expected: " ++ show expected)

testTransformationUtils = testGroup "TransformationUtils"
  [computeErrorGuards__tests
  ,computeErrorVarValue_tests
  ]

computeErrorGuards__tests = testGroup "computeErrorGuards tests"
  [
  -- TODO: Fix the following tests
  --  computeErrorGuards__test1
  -- ,computeErrorGuards__test2
  ]

computeErrorGuards__test1 =
  testCase "" $
    computeErrorGuards 7 14 spec Map.empty Map.empty (decl, errVarEnv,localEnv',forMap)
    `checkOutputIs`
    (decl
    ,[("E_x"
      ,FVar FPDouble "x"
      ,RealMark "x" ResValue
      ,FBTrue
      ,ErrorMark "y" ResValue FPDouble
      ,4.440892098500626e-16
      ,[FVar FPDouble "x"]
      ,[RealMark "x" ResValue]
      ,[ErrorMark "x" ResValue FPDouble]
      ,[VarBind "y" ResValue FPDouble (LBDouble 2) (UBDouble 5)])])
    where
      decl = Decl False FPDouble "f" [] (FInt 5)
      errVarEnv = [("E_x", FVar FPDouble "x", FBTrue)]
      spec = Spec [SpecBind "f" [VarBind "y" ResValue FPDouble (LBDouble 2) (UBDouble 5)]]
      localEnv' = [("x",FPDouble,FVar FPDouble "y")]
      forMap = []


computeErrorGuards__test2 =
  testCase "" $
    computeErrorGuards 7 14 spec Map.empty Map.empty (decl, errVarEnv,localEnv',forMap)
    `checkOutputIs`
    (decl
    ,[("E_x"
      ,FVar FPDouble "x"
      ,RealMark "x" ResValue
      ,FBTrue
      ,ErrorMark "y" ResValue FPDouble
      ,4.440892098500626e-16
      ,[FVar FPDouble "x"]
      ,[RealMark "x" ResValue]
      ,[ErrorMark "x" ResValue FPDouble]
      ,[VarBind "y" ResValue FPDouble (LBDouble 2) (UBDouble 5)]),
      ("E_y"
      ,BinaryFPOp AddOp FPDouble (FVar FPDouble "x") (FVar FPDouble "y")
      ,BinaryOp AddOp (RealMark "x" ResValue) (RealMark "y" ResValue)
      ,FBTrue
      ,ErrBinOp AddOp FPDouble (RealMark "y" ResValue) (ErrorMark "y" ResValue FPDouble) (RealMark "y" ResValue) (ErrorMark "y" ResValue FPDouble)
      ,1.7763568394002505e-15
      ,[FVar FPDouble "x",FVar FPDouble "y"]
      ,[RealMark "x" ResValue,RealMark "y" ResValue]
      ,[ErrorMark "x" ResValue FPDouble,ErrorMark "y" ResValue FPDouble]
      ,[VarBind "y" ResValue FPDouble (LBDouble 2) (UBDouble 5)])
      ])
 where
      decl = Decl False FPDouble "f" [] (FInt 5)
      errVarEnv = [("E_x", FVar FPDouble "x", FBTrue)
                  ,("E_y", BinaryFPOp AddOp FPDouble (FVar FPDouble "x") (FVar FPDouble "y"), FBTrue)]
      spec = Spec [SpecBind "g" [VarBind "z" ResValue FPDouble (LBDouble 7) (UBDouble 12)],
                   SpecBind "f" [VarBind "y" ResValue FPDouble (LBDouble 2) (UBDouble 5)]]
      localEnv' = [("x",FPDouble,FVar FPDouble "y")]
      forMap = []

computeErrorVarValue_tests = testGroup "computeErrorVarValue tests"
  [computeErrorVarValue__test1
  ,computeErrorVarValue__test2
  ,computeErrorVarValue__test3
  ]
computeErrorVarValue__test1 =
  testCase "test1" $
    computeErrorVarValue 7 14 [VarBind "x" ResValue FPDouble (LBDouble 2) (UBDouble 5)] Map.empty [] Map.empty ("E_x", FVar FPDouble "x", FBTrue)
    `checkOutputIs`
    ("E_x"
    ,FVar FPDouble "x"
    ,Var Real "x"
    ,FBTrue
    ,ErrorMark "x" ResValue FPDouble
    ,4.440892098500626e-16
    ,[FVar FPDouble "x"]
    ,[RealMark "x" ResValue]
    ,[ErrorMark "x" ResValue FPDouble]
    ,[VarBind "x" ResValue FPDouble (LBDouble 2) (UBDouble 5)])

computeErrorVarValue__test2 =
  testCase "test2" $
    computeErrorVarValue 7 14 [VarBind "x" ResValue FPDouble (LBDouble 2) (UBDouble 5), VarBind "y" ResValue FPDouble (LBDouble 2) (UBDouble 5)] Map.empty [] Map.empty ("E_x", FVar FPDouble "x", FBTrue)
    `checkOutputIs`
    ("E_x"
    ,FVar FPDouble "x"
    ,Var Real "x"
    ,FBTrue
    ,ErrorMark "x" ResValue FPDouble
    ,4.440892098500626e-16
    ,[FVar FPDouble "x"]
    ,[RealMark "x" ResValue]
    ,[ErrorMark "x" ResValue FPDouble]
    ,[VarBind "x" ResValue FPDouble (LBDouble 2) (UBDouble 5),VarBind "y" ResValue FPDouble (LBDouble 2) (UBDouble 5)])

computeErrorVarValue__test3 =
  testCase "test3" $
    computeErrorVarValue 7 14 [VarBind "x" ResValue FPDouble (LBDouble 2) (UBDouble 5), VarBind "y" ResValue FPDouble (LBDouble 2) (UBDouble 5)] Map.empty [] Map.empty ("E_x", BinaryFPOp AddOp FPDouble (FVar FPDouble "x") (FVar FPDouble "y"), FBTrue)
    `checkOutputIs`
    ("E_x"
    ,BinaryFPOp AddOp FPDouble (FVar FPDouble "x") (FVar FPDouble "y")
    ,BinaryOp AddOp (Var Real "x") (Var Real "y")
    ,FBTrue
    ,ErrBinOp AddOp FPDouble (RealMark "x" ResValue) (ErrorMark "x" ResValue FPDouble) (RealMark "y" ResValue) (ErrorMark "y" ResValue FPDouble)
    ,1.7763568394002505e-15
    ,[FVar FPDouble "x",FVar FPDouble "y"]
    ,[RealMark "x" ResValue,RealMark "y" ResValue]
    ,[ErrorMark "x" ResValue FPDouble,ErrorMark "y" ResValue FPDouble]
    ,[VarBind "x" ResValue FPDouble (LBDouble 2) (UBDouble 5), VarBind "y" ResValue FPDouble (LBDouble 2) (UBDouble 5)])


-- Notices:
-- Copyright 2023 United States Government as represented by the Administrator of the National Aeronautics and Space Administration. All Rights Reserved.

-- This software calls the NASA Software named “PRECiSA with Instrumented Code Generation” LAR-19739-1, which is not bundled or redistributed with this software, but users of this software must obtain their own NASA license, which is subject to the terms and conditions of the applicable at the time.

-- Disclaimers
-- No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE. THIS AGREEMENT DOES NOT, IN ANY MANNER, CONSTITUTE AN ENDORSEMENT BY GOVERNMENT AGENCY OR ANY PRIOR RECIPIENT OF ANY RESULTS, RESULTING DESIGNS, HARDWARE, SOFTWARE PRODUCTS OR ANY OTHER APPLICATIONS RESULTING FROM USE OF THE SUBJECT SOFTWARE.  FURTHER, GOVERNMENT AGENCY DISCLAIMS ALL WARRANTIES AND LIABILITIES REGARDING THIRD-PARTY SOFTWARE, IF PRESENT IN THE ORIGINAL SOFTWARE, AND DISTRIBUTES IT "AS IS."

-- Waiver and Indemnity:  RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS AGAINST THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT.  IF RECIPIENT'S USE OF THE SUBJECT SOFTWARE RESULTS IN ANY LIABILITIES, DEMANDS, DAMAGES, EXPENSES OR LOSSES ARISING FROM SUCH USE, INCLUDING ANY DAMAGES FROM PRODUCTS BASED ON, OR RESULTING FROM, RECIPIENT'S USE OF THE SUBJECT SOFTWARE, RECIPIENT SHALL INDEMNIFY AND HOLD HARMLESS THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW.  RECIPIENT'S SOLE REMEDY FOR ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL TERMINATION OF THIS AGREEMENT.

module FramaC.PrettyPrint.CLangTest where

import Common.TypesUtils
import FramaC.CLang
import FramaC.Types
import PPExt (prettyDoc, render)
import Test.Tasty
import Test.Tasty.HUnit

test =
  testGroup
    "PrettyPrint of CLang AST"
    [ testGroup "Stm" $
        [ testGroup
            "VarAssign"
            $ let cases =
                    [ ( "single precision integer constant",
                        VarAssign (Float SinglePrec) "res" $ FPCnst SinglePrec 1,
                        "res_single = 1.0;"
                      ),
                      ( "double precision integer constant",
                        VarAssign (Float DoublePrec) "res" $ FPCnst SinglePrec 1,
                        "res_double = 1.0;"
                      ),
                      ( "double precision rational non-fp representable constant",
                        VarAssign (Float DoublePrec) "res" $ FPCnst SinglePrec (0.1 :: Rational),
                        "res_double = 0.1;"
                      ),
                      ( "double precision rational fp representable constant",
                        VarAssign (Float DoublePrec) "res" $ FPCnst SinglePrec (0.5 :: Rational),
                        "res_double = 0.5;"
                      )
                    ]
               in [testCase m (i `isPrettiedAs` o) | (m, i, o) <- cases]
        ],
      testGroup "AExpr" $
        [ testGroup "Var" $
            let cases =
                  [ ("double precision", Var (Float DoublePrec) "x", "x_double"),
                    ("single precision", Var (Float SinglePrec) "x", "x_single"),
                    ("integer", Var Int "y", "y"),
                    ("bool", Var Boolean "z", "z"),
                    ("maybe single", Var (MaybeStruct $ Float SinglePrec) "x", "x_single"),
                    ("maybe double", Var (MaybeStruct $ Float DoublePrec) "x", "x_double"),
                    ("maybe integer", Var (MaybeStruct Int) "x", "x"),
                    ("maybe bool", Var (MaybeStruct Boolean) "b", "b")
                  ]
             in [testCase m (i `isPrettiedAs` o) | (m, i, o) <- cases]
        ]
    ]

class IsPrettiedAs a where
  isPrettiedAs :: a -> String -> Assertion

instance IsPrettiedAs Stm where
  isPrettiedAs stm = flip (assertEqual "") prettyRenderRes
    where
      prettyRenderRes = render $ prettyDoc stm

instance IsPrettiedAs AExpr where
  isPrettiedAs stm = flip (assertEqual "") prettyRenderRes
    where
      prettyRenderRes = render $ prettyDoc stm
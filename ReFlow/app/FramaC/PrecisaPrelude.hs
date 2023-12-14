-- Notices:
-- Copyright 2023 United States Government as represented by the Administrator of the National Aeronautics and Space Administration. All Rights Reserved.

-- This software calls the NASA Software named “PRECiSA with Instrumented Code Generation” LAR-19739-1, which is not bundled or redistributed with this software, but users of this software must obtain their own NASA license, which is subject to the terms and conditions of the applicable at the time.

-- Disclaimers
-- No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE. THIS AGREEMENT DOES NOT, IN ANY MANNER, CONSTITUTE AN ENDORSEMENT BY GOVERNMENT AGENCY OR ANY PRIOR RECIPIENT OF ANY RESULTS, RESULTING DESIGNS, HARDWARE, SOFTWARE PRODUCTS OR ANY OTHER APPLICATIONS RESULTING FROM USE OF THE SUBJECT SOFTWARE.  FURTHER, GOVERNMENT AGENCY DISCLAIMS ALL WARRANTIES AND LIABILITIES REGARDING THIRD-PARTY SOFTWARE, IF PRESENT IN THE ORIGINAL SOFTWARE, AND DISTRIBUTES IT "AS IS."

-- Waiver and Indemnity:  RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS AGAINST THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT.  IF RECIPIENT'S USE OF THE SUBJECT SOFTWARE RESULTS IN ANY LIABILITIES, DEMANDS, DAMAGES, EXPENSES OR LOSSES ARISING FROM SUCH USE, INCLUDING ANY DAMAGES FROM PRODUCTS BASED ON, OR RESULTING FROM, RECIPIENT'S USE OF THE SUBJECT SOFTWARE, RECIPIENT SHALL INDEMNIFY AND HOLD HARMLESS THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW.  RECIPIENT'S SOLE REMEDY FOR ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL TERMINATION OF THIS AGREEMENT.

module FramaC.PrecisaPrelude where

import PPExt

precisaPreludeContent :: Doc
precisaPreludeContent =
  text "#include<stdbool.h>\n"
  $$
  text "#define round(X) (double) (X)\n"
  $$
  text "/*@"
  $$
  -- text"axiomatic fp_funs {"
  -- $$
  text "logic double Dadd(double X, double Y) = round(X+Y);\n"
  $$
  text "logic double Dsub(double X, double Y) = round(X-Y);\n"
  $$
  text "logic double Dmul(double X, double Y) = round(X*Y);\n"
  $$
  text "logic double Dneg(double X) = round(0-X);\n"
  $$
  text "logic double Dabs(double X) = round(X);\n"
  $$
  text "logic double Ddiv(double X, double Y) = (Y != round(0.0) ? round(X/Y) : round(0.0));\n"
  $$
  text "logic double Dsqrt(double X) = sqrt(X);\n"
--   X;
-- //  (Y != 0.0 ? round(X/Y) : 0.0) ;

-- // }

-- // axiomatic int_funs {
  $$
  text "logic integer Iadd(integer X, integer Y) = X+Y;\n"
  $$
  text "logic integer Isub(integer X, integer Y) = X-Y;\n"
  $$
  text "logic integer Imul(integer X, integer Y) = X*Y;\n"
  $$
  text "logic integer Ineg(integer X) = 0-X;\n"
--   // logic integer Idiv(integer X, integer Y) = (Y != 0 ? X/Y : 0) ;
-- // }
-- // axiomatic error_bounds {
  $$
  text "logic real ulp_dp(real X) = \\round_double(\\Up,X)-\\round_double(\\Down,X);\n"
  $$
  text "logic real errAdd_dp(real X, real E_X, real Y, real E_Y)"
  $$
  text "= E_X + E_Y + ulp_dp(\\abs(X + Y) + E_X + E_Y)/2;\n"
  $$
  text "logic real errSub_dp(real X, real E_X, real Y, real E_Y)"
  $$
  text "= E_X + E_Y + ulp_dp(\\abs(X - Y) + E_X + E_Y)/2;\n"
  $$
  text "logic real errMul_dp(real X, real E_X, real Y, real E_Y)"
  $$
  text "= \\abs(X)*E_Y+\\abs(Y)*E_X+E_X*E_Y + ulp_dp(\\abs(X)*\\abs(Y) + \\abs(X)*E_Y + E_X*\\abs(Y) + E_X*E_Y)/2;\n"
  $$
  text "logic real errDiv_dp(real X, real E_X, real Y, real E_Y)"
  $$
  text "= ( ((Y*Y - E_Y*\\abs(Y)) != 0 && (\\abs(Y) - E_Y) !=0)? (\\abs(Y)*E_X + \\abs(X)*E_Y) / (Y*Y - E_Y*\\abs(Y)) + ulp_dp((\\abs(X) + E_X) / (\\abs(Y) - E_Y)) / 2 : 0 );\n"
  $$
  text "logic real errNeg_dp(real X, real E_X) = E_X;\n"
  $$
  text "logic real errAbs_dp(real X, real E_X) = E_X;\n"
  $$
  text "logic real errAdd_i(integer X, real E_X, integer Y, real E_Y) = E_X + E_Y;\n"
  $$
  text "logic real errSub_i(integer X, real E_X, integer Y, real E_Y) = E_X + E_Y;"
  $$
  text "*/\n"
  $$
  text "struct maybeInt {"
  $$
  nest 2 (text "bool isValid;")
  $$
  nest 2 (text "int value;")
  $$
  text "};\n"
  $$
  text "/*@ assigns \\nothing;"
  $$
  text "ensures ! \\result.isValid;"
  $$
  text "*/"
  $$
  text "struct maybeInt none () {"
  $$
  nest 2 (text "struct maybeInt result = { false, 0 };")
  $$
  nest 2 (text "return result;")
  $$
  text "}\n"
  $$
  text "/*@ assigns \\nothing;"
  $$
  text "ensures \\result.isValid;"
  $$
  text "ensures \\result.value == val;"
  $$
  text "*/"
  $$
  text "struct maybeInt some (int val) {"
  $$
  nest 2 (text "struct maybeInt result = { true, val };")
  $$
  nest 2 (text "return result;")
  $$
  text "}\n"
  $$
  text "struct maybeFloat {"
  $$
  nest 2 (text "bool isValid;")
  $$
  nest 2 (text "float value;")
  $$
  text "};\n"
  $$
  text "/*@ assigns \\nothing;"
  $$
  text "ensures ! \\result.isValid;"
  $$
  text "*/"
  $$
  text "struct maybeFloat noneFloat () {"
  $$
  nest 2 (text "struct maybeFloat result = { false, 0 };")
  $$
  nest 2 (text "return result;")
  $$
  text "}\n"
  $$
  text "/*@ assigns \\nothing;"
  $$
  text "ensures \\result.isValid;"
  $$
  text "ensures \\result.value == val;"
  $$
  text "*/"
  $$
  text "struct maybeFloat someFloat (float val) {"
  $$
  nest 2 (text "struct maybeFloat result = { true, val };")
  $$
  nest 2 (text "return result;")
  $$
  text "}\n"
  $$
  text "struct maybeDouble {"
  $$
  nest 2 (text "bool isValid;")
  $$
  nest 2 (text "double value;")
  $$
  text "};\n"
  $$
  text "/*@ assigns \\nothing;"
  $$
  text "ensures ! \\result.isValid;"
  $$
  text "*/"
  $$
  text "struct maybeDouble noneDouble () {"
  $$
  nest 2 (text "struct maybeDouble result = { false, 0 };")
  $$
  nest 2 (text "return result;")
  $$
  text "}\n"
  $$
  text "/*@ assigns \\nothing;"
  $$
  text "ensures \\result.isValid;"
  $$
  text "ensures \\result.value == val;"
  $$
  text "*/"
  $$
  text "struct maybeDouble someDouble (double val) {"
  $$
  nest 2 (text "struct maybeDouble result = { true, val };")
  $$
  nest 2 (text "return result;")
  $$
  text "}\n"
  $$
  text "struct maybeBool {"
  $$
  nest 2 (text "bool isValid;")
  $$
  nest 2 (text "bool value;")
  $$
  text "};\n"
  $$
  text "/*@"
  $$
  text "assigns \\nothing;"
  $$
  text "ensures ! \\result.isValid;"
  $$
  text "*/"
  $$
  text "struct maybeBool noneBool () {"
  $$
  nest 2 (text "struct maybeBool result = { false, false };")
  $$
  nest 2 (text "return result;")
  $$
  text "}\n"
  $$
  text "/*@ assigns \\nothing;"
  $$
  text "ensures \\result.isValid;"
  $$
  text "ensures \\result.value == val;"
  $$
  text "*/"
  $$
  text "struct maybeBool someBool (bool val) {"
  $$
  nest 2 (text "struct maybeBool result = { true, val };")
  $$
  nest 2 (text "return result;")
  $$
  text "}"

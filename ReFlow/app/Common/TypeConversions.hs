-- Notices:
-- Copyright 2023 United States Government as represented by the Administrator of the National Aeronautics and Space Administration. All Rights Reserved.

-- This software calls the NASA Software named “PRECiSA with Instrumented Code Generation” LAR-19739-1, which is not bundled or redistributed with this software, but users of this software must obtain their own NASA license, which is subject to the terms and conditions of the applicable at the time.

-- Disclaimers
-- No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE. THIS AGREEMENT DOES NOT, IN ANY MANNER, CONSTITUTE AN ENDORSEMENT BY GOVERNMENT AGENCY OR ANY PRIOR RECIPIENT OF ANY RESULTS, RESULTING DESIGNS, HARDWARE, SOFTWARE PRODUCTS OR ANY OTHER APPLICATIONS RESULTING FROM USE OF THE SUBJECT SOFTWARE.  FURTHER, GOVERNMENT AGENCY DISCLAIMS ALL WARRANTIES AND LIABILITIES REGARDING THIRD-PARTY SOFTWARE, IF PRESENT IN THE ORIGINAL SOFTWARE, AND DISTRIBUTES IT "AS IS."

-- Waiver and Indemnity:  RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS AGAINST THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT.  IF RECIPIENT'S USE OF THE SUBJECT SOFTWARE RESULTS IN ANY LIABILITIES, DEMANDS, DAMAGES, EXPENSES OR LOSSES ARISING FROM SUCH USE, INCLUDING ANY DAMAGES FROM PRODUCTS BASED ON, OR RESULTING FROM, RECIPIENT'S USE OF THE SUBJECT SOFTWARE, RECIPIENT SHALL INDEMNIFY AND HOLD HARMLESS THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW.  RECIPIENT'S SOLE REMEDY FOR ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL TERMINATION OF THIS AGREEMENT.


module Common.TypeConversions where

import Common.TypesUtils
import qualified FramaC.Types as C
import qualified FramaC.ACSLTypes as ACSL
import AbsPVSLang

type2acsl :: C.Type -> ACSL.Type
type2acsl C.Real = ACSL.Real
type2acsl C.Int  = ACSL.Int
type2acsl C.Boolean  = ACSL.Boolean
type2acsl (C.Float fp)  = ACSL.Float fp
type2acsl (C.Array t i) = ACSL.Array (type2acsl t) i
type2acsl (C.MaybeStruct t) = ACSL.MaybeStruct (type2acsl t)

fprec2MaybeType :: PVSType -> C.Type
fprec2MaybeType t = C.MaybeStruct (fprec2type t)

fprec2type :: PVSType -> C.Type
fprec2type FPSingle = C.Float SinglePrec
fprec2type FPDouble = C.Float DoublePrec
fprec2type TInt = C.Int
fprec2type Real = C.Real
-- fprec2type (Array fp (Just (ArraySizeInt n))) = C.Array (fprec2type fp) (Just $ ArraySizeInt n)
-- fprec2type (Array fp (Just (ArraySizeVar s))) = C.Array (fprec2type fp) (Just $ ArraySizeVar s)
-- fprec2type (Array fp Nothing) = C.Array (fprec2type fp) Nothing
fprec2type Boolean = C.Boolean

fprec2RealType :: PVSType -> ACSL.Type
fprec2RealType TInt = ACSL.Int
fprec2RealType Boolean = ACSL.Boolean
fprec2RealType _    = ACSL.Real

fprec2acsl :: PVSType -> ACSL.Type
fprec2acsl = type2acsl . fprec2type
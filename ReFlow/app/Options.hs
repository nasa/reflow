-- Notices:
-- Copyright 2023 United States Government as represented by the Administrator of the National Aeronautics and Space Administration. All Rights Reserved.

-- This software calls the NASA Software named “PRECiSA with Instrumented Code Generation” LAR-19739-1, which is not bundled or redistributed with this software, but users of this software must obtain their own NASA license, which is subject to the terms and conditions of the applicable at the time.

-- Disclaimers
-- No Warranty: THE SUBJECT SOFTWARE IS PROVIDED "AS IS" WITHOUT ANY WARRANTY OF ANY KIND, EITHER EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL CONFORM TO SPECIFICATIONS, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR FREEDOM FROM INFRINGEMENT, ANY WARRANTY THAT THE SUBJECT SOFTWARE WILL BE ERROR FREE, OR ANY WARRANTY THAT DOCUMENTATION, IF PROVIDED, WILL CONFORM TO THE SUBJECT SOFTWARE. THIS AGREEMENT DOES NOT, IN ANY MANNER, CONSTITUTE AN ENDORSEMENT BY GOVERNMENT AGENCY OR ANY PRIOR RECIPIENT OF ANY RESULTS, RESULTING DESIGNS, HARDWARE, SOFTWARE PRODUCTS OR ANY OTHER APPLICATIONS RESULTING FROM USE OF THE SUBJECT SOFTWARE.  FURTHER, GOVERNMENT AGENCY DISCLAIMS ALL WARRANTIES AND LIABILITIES REGARDING THIRD-PARTY SOFTWARE, IF PRESENT IN THE ORIGINAL SOFTWARE, AND DISTRIBUTES IT "AS IS."

-- Waiver and Indemnity:  RECIPIENT AGREES TO WAIVE ANY AND ALL CLAIMS AGAINST THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT.  IF RECIPIENT'S USE OF THE SUBJECT SOFTWARE RESULTS IN ANY LIABILITIES, DEMANDS, DAMAGES, EXPENSES OR LOSSES ARISING FROM SUCH USE, INCLUDING ANY DAMAGES FROM PRODUCTS BASED ON, OR RESULTING FROM, RECIPIENT'S USE OF THE SUBJECT SOFTWARE, RECIPIENT SHALL INDEMNIFY AND HOLD HARMLESS THE UNITED STATES GOVERNMENT, ITS CONTRACTORS AND SUBCONTRACTORS, AS WELL AS ANY PRIOR RECIPIENT, TO THE EXTENT PERMITTED BY LAW.  RECIPIENT'S SOLE REMEDY FOR ANY SUCH MATTER SHALL BE THE IMMEDIATE, UNILATERAL TERMINATION OF THIS AGREEMENT.

module Options
  ( Options (..),
    parseOptions,
  )
where

import Options.Applicative

data Options = Options
  {  optRealProgramFile    :: FilePath
   , optRealInputRangeFile :: FilePath
   , targetFormat          :: String
   , optMaxDepth           :: Int
   , optMinPrec            :: Int
   , unfoldFunctionCalls   :: Bool
   , noInstrumentation     :: Bool
  }
  deriving (Show)

options :: Parser Options
options =
  Options
    <$> strArgument
      ( metavar "PROGRAM"
          <> help "Program to analyze"
      )
    <*> strArgument
      ( metavar "INPUT"
          <> help "Input ranges for variables"
      )
    <*> strOption
      ( long "format"
          <> short 'f'
          <> showDefault
          <> value "double"
          <> help "Target floating-point format (single or double)"
          <> metavar "PREC"
      )
    <*> option auto
           (  long "max-depth"
           <> short 'd'
           <> showDefault
           <> value 7
           <> help "Maximum depth of branch-and-bound"
           <> metavar "BB_MAX_DEPTH"
           )
    <*> option auto
          (  long "precision"
          <> short 'p'
          <> help "Precision"
          <> showDefault
          <> value 14
          <> metavar "BB_PREC"
          )
    <*> switch
          (  long "unfold-fun-calls"
          <> help "Perform an analysis where the body of each function call is unfolded in the expression and globally optimized. This option may lead to more accurate results."
          )
    <*> switch
          (  long "no-instrumentation"
          <> help "Perform plain C code generation with no contracts and no instrumentation for unstable conditionals."
          )


parseOptions :: IO Options
parseOptions = execParser parserOpts
  where
    parserOpts =
      info
        (options <**> helper)
        ( fullDesc
            <> progDesc "Generate a stable C FP version of a real PVS program or table Floating Point C code generator from PVS Real specifications"
            <> header "ReFlow"
        )
import System.Environment
import System.Exit
import System.IO
import System.Console.GetOpt
import Data.Number.CReal
import Data.Char
import Control.Monad

import Parquail
import TranslateQuail
import Printquail
import Types
import ErrM

data Options = Options
  { optVerbose , optPrecision :: Int
  , optHelp, optVersion :: Bool
  }

defaultOptions :: Options
defaultOptions = Options
  { optVerbose   = 2
  , optPrecision = 10
  , optHelp      = False
  , optVersion   = False
  }

type OptTran = Endo Options

options :: [OptDescr OptTran]
options =
  [ Option ['h'] ["help"] (NoArg help) "Print this help."
  , Option ['v'] ["verbose"] (ReqArg verbose "VALUE") "Verbose mode between 0 (minimum) and 4 (maximum).  Default value if not specified is 2."
  , Option ['p'] ["precision"] (ReqArg precision "VALUE") "Define computation precision as a number of digits. Default value if not specified is 10."
  , Option []  ["version"] (NoArg version) "show version number"
  ]

{-
options :: [OptDescr Flag]
options =
  [ Option ['h'] ["help"] (NoArg Help) "Print this help."
  , Option ['v'] ["verbose"] (ReqArg verbose "VALUE") "Verbose mode between 0 (minimum) and 4 (maximum).  Default value if not specified is 2."
  , Option ['p'] ["precision"] (ReqArg precision "VALUE") "Define computation precision as a number of digits. Default value if not specified is 10."
  , Option []  ["version"] (NoArg Version) "show version number"
  ]
-}

help :: OptTran
help opt = opt { optHelp = True}

version :: OptTran
version opt = opt { optVersion = True}

verbose :: String -> OptTran
verbose s opt | all isDigit s = opt { optVerbose = read s }
              | otherwise     = error $ "unexpected verbose argument: " ++ show s

precision :: String -> OptTran
precision s opt | all isDigit s = opt { optPrecision = read s }
                | otherwise     = error $ "unexpected precision argument: " ++ show s

printVersion :: IO ()
printVersion = putStrLn "hasQuail 2.35"

approxCReal :: Int -> CReal -> CReal
approxCReal pr = read . showCReal pr

-- Here one can statically pick the precision for integers
type IntPrec = Int
-- type IntPrec = Int64
-- type IntPrec = Integer

getOptions :: IO (Options , [String])
getOptions = do
  args <- getArgs
  case getOpt Permute options args of
    (o , fp , []) -> return (foldl (flip id) defaultOptions o , fp)
    (_,_, errs) -> ioError (userError (concat errs ++ usage)) 

usage :: String
usage = usageInfo header options
 where header = "Usage: Run [OPTION...] file..."

main :: IO ()
main = do
  (opt , fps) <- getOptions
  let v  = optVerbose opt
  let pr = optPrecision opt
  case () of
   _ | optHelp    opt -> putStrLn usage
     | optVersion opt -> printVersion
     | [fp] <- fps -> do
       s <- readFile fp
       case pProgr $ myLexer s of
         Bad err -> hPutStrLn stderr err >> exitWith (ExitFailure 1)
         Ok t -> do
           when (v > 0) $ putStrLn $ printTree t
           let st = transProgr $ t
           let (leak , totSecret) = expected st
           let totSec = logBase 2 (fromIntegral (totSecret :: IntPrec))
           let leak' = approxCReal pr leak
           -- putStrLn . showProbTree . runProgram $ st
           -- putStrLn $ "bits leaked: " ++ show (expected st :: Double)
           putStrLn $ "bits leaked: " ++ showCReal pr leak'
           putStrLn $ "total size of secret: " ++ showCReal pr totSec
                                               ++ " ("
                                               ++ showCReal pr (100 * leak' / totSec)
                                              ++ "%)"
     | otherwise -> hPutStrLn stderr ("Can't understand input: " ++ unwords fps) >> exitWith (ExitFailure 1)

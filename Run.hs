import System.Environment
import System.Exit
import System.IO
import System.Console.GetOpt
import Data.Number.CReal

import Control.Monad
import Parquail
import TranslateQuail
import Printquail
import Types
import ErrM

data Flag = Verbose Int | Version | Precision Int | Help
  deriving (Eq)

options :: [OptDescr Flag]
options =
  [ Option ['h'] ["help"] (NoArg Help) "Print this help."
  , Option ['v'] ["verbose"] (ReqArg verbose "VALUE") "Verbose mode between 0 (minimum) and 4 (maximum).  Default value if not specified is 2."
  , Option ['p'] ["precision"] (ReqArg precision "VALUE") "Define computation precision as a number of digits. Default value if not specified is 10."
  , Option []  ["version"] (NoArg Version) "show version number"
  ]

verbose = Verbose . read

precision :: String -> Flag
precision s = Precision (read s)

printVersion :: IO ()
printVersion = putStrLn "hasQuail 2.35"

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (o , [fp] , []) -> do 
      s <- readFile fp
      if Version `elem` o
       then printVersion
       else if Help `elem` o 
        then putStrLn (usageInfo header options)
        else case pProgr $ myLexer s of
          Bad err -> hPutStrLn stderr err >> exitWith (ExitFailure 1)
          Ok t -> do
              let pr = head ([ i | Precision i <- o] ++ [10])
              -- putStrLn $ printTree t
              let st = transProgr $ t
              let (leak , totSecret) = expected st
              let totSec = logBase 2 (fromInteger totSecret) 
              -- putStrLn . showProbTree . runProgram $ st
              -- putStrLn $ "bits leaked: " ++ show (expected st :: Double)
              putStrLn $ "bits leaked: " ++ showCReal pr leak
              putStrLn $ "total size of secret: " ++ showCReal pr totSec
                                                  ++ " ("
                                                  ++ showCReal pr (100 * leak / totSec)
                                                  ++ "%)"
    (_ , _ , errs) ->  ioError (userError (concat errs ++ usageInfo header options))
 where header = "Usage: Run [OPTION...] file..."

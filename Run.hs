import System.Environment
import System.Exit
import System.IO
import Parquail
import TranslateQuail
import Printquail
import Types
import ErrM

main :: IO ()
main = do
  fp:_ <- getArgs
  s <- readFile fp
  case pProgr $ myLexer s of
    Bad err -> hPutStrLn stderr err >> exitWith (ExitFailure 1)
    Ok t -> do
        putStrLn $ printTree t
        putStrLn . showProbTree . runProgram . transProgr $ t

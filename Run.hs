import System.Environment
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
    Bad s -> putStrLn s
    Ok t -> do
        putStrLn $ printTree t
        print . runProgram . transProgr $ t
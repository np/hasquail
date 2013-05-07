{-# LANGUAGE GADTs, KindSignatures, MultiParamTypeClasses, GeneralizedNewtypeDeriving, FlexibleInstances, UndecidableInstances #-}
module Types where

import Prelude hiding (LT, GT, EQ)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Control.Monad.State

type Endo a = a -> a

data Range a = Range { rangeFrom :: a, rangeTo :: a }
  deriving (Show)

-- lengthRange (Range i i) = i - i + 1 = 1
lengthRange :: Range Integer -> Integer
lengthRange (Range i j) = j - i + 1

wellFormedRange :: Ord a => Range a -> Bool
wellFormedRange (Range i j) = i <= j

type Interval a = [Range a]

wellFormedInterval :: Ord a => Interval a -> Bool
wellFormedInterval []  = True
wellFormedInterval [r] = wellFormedRange r
wellFormedInterval (r1@(Range _ j) : r2@(Range k _) : rs)
  = k > j && wellFormedRange r1 && wellFormedInterval (r2 : rs)

lengthInterval :: Interval Integer -> Integer
lengthInterval = sum . map lengthRange

singletonInterval :: a -> Interval a
singletonInterval x = [Range x x]

type Var = String

data Type = TyInt { width :: Int }
          | TyArray { arraySize :: Expr
                    , elemType  :: Type }

data Op = Not | Fac

-- Op2 and Rel2 could be extended
-- * And, Or, Xor could be moved from Op2 to Rel2
-- * Op2 could embed any Rel2 using a boolean as an integer semantics
data Op2 = Add | Sub | Mul | Div | Mod | And | Or | Xor | Rel2 Rel2

data Rel2 = LE | LT | GE | GT | EQ | NE

data Expr = Lit Integer
          | Op2 Op2 Expr Expr
          | Var Var [Expr] -- Var v xs: v is an array, xs are indices
                           -- in particular if xs is null then v is
                           -- just an integer variable.

boolOp :: (Bool -> Bool) -> Integer -> Integer
boolOp op x = if op (x /= 0) then 1 else 0

evalOp :: Op -> Integer -> Integer
evalOp Not = boolOp not
evalOp Fac = \n -> product [1..n]

boolOp2 :: (Bool -> Bool -> Bool) -> Integer -> Integer -> Integer
boolOp2 op2 x y = if op2 (x /= 0) (y /= 0) then 1 else 0

evalOp2 :: Op2 -> Integer -> Integer -> Integer
evalOp2 Add = (+)
evalOp2 Sub = (-)
evalOp2 Mul = (*)
evalOp2 Div = div
evalOp2 Mod = mod
evalOp2 And = boolOp2 (&&)
evalOp2 Or  = boolOp2 (||)
evalOp2 Xor = boolOp2 (/=)
evalOp2 (Rel2 rel2) = \x y -> if evalRel2 rel2 x y then 1 else 0

type EvalEnv = Var -> [Integer] -> Integer
type EvalPrivEnv = Var -> [Integer] -> Interval Integer

evalExpr :: EvalEnv -> Expr -> Integer
evalExpr _   (Lit i)         = i
evalExpr env (Op2 op2 e1 e2) = evalOp2 op2 (evalExpr env e1) (evalExpr env e2)
evalExpr env (Var v es)      = env v (map (evalExpr env) es)

data Cond = CondExpr Expr
          | PrivComp Rel2 (Var, [Expr]) Expr

evalRel2 :: Rel2 -> Integer -> Integer -> Bool
evalRel2 LE = (<=)
evalRel2 LT = (<)
evalRel2 GE = (>=)
evalRel2 GT = (>)
evalRel2 EQ = (==)
evalRel2 NE = (/=)

data CompResult = IntervalComp { trueInterval, falseInterval :: Interval Integer }
                | BoolComp Bool

flipIntervalComp :: CompResult -> CompResult
flipIntervalComp (IntervalComp x y) = IntervalComp y x
flipIntervalComp (BoolComp b)       = BoolComp (not b)

range :: Integer -> Integer -> Interval Integer
range i j | i > j     = []
          | otherwise = [Range i j]

-- botRange [i..j] k = [i..k]
botRange :: Range Integer -> Integer -> Interval Integer
botRange (Range i _j) k = range i k

botInterval :: Interval Integer -> Integer -> Interval Integer
botInterval rs k = [ r' | r <- rs, r' <- botRange r k ]

-- topRange [i..j] k = [k..j]
topRange :: Range Integer -> Integer -> Interval Integer
topRange (Range _i j) k = range k j

topInterval :: Interval Integer -> Integer -> Interval Integer
topInterval rs k = [ r' | r <- rs, r' <- topRange r k ]

splitInterval :: Interval Integer -> Integer -> CompResult
splitInterval rs k = IntervalComp (botInterval rs (k-1)) (topInterval rs k)

removeRange :: Range Integer -> Integer -> Interval Integer
removeRange r@(Range i j) k | not (k `memberRange` r) = [r]
                            | otherwise               = range i (k-1) ++ range (k+1) j

removeInterval :: Interval Integer -> Integer -> Interval Integer
removeInterval rs k = [ r' | r <- rs, r' <- removeRange r k ]

memberRange :: Integer -> Range Integer -> Bool
memberRange k (Range i j) = k >= i && k <= j

memberInterval :: Integer -> Interval Integer -> Bool
k `memberInterval` rs = any (memberRange k) rs

evalPrivRel2 :: Rel2 -> Interval Integer -> Integer -> CompResult
evalPrivRel2 LE rs k = splitInterval rs (k+1)
evalPrivRel2 LT rs k = splitInterval rs k
evalPrivRel2 EQ rs k = IntervalComp i (removeInterval rs k)
                          where i | k `memberInterval` rs = singletonInterval k
                                  | otherwise             = []
evalPrivRel2 GE rs k = flipIntervalComp $ splitInterval rs k
evalPrivRel2 GT rs k = flipIntervalComp $ splitInterval rs (k+1)
evalPrivRel2 NE rs k = flipIntervalComp $ evalPrivRel2 EQ rs k

evalCond :: EvalEnv -> EvalPrivEnv -> Cond -> CompResult
evalCond env _    (CondExpr e) = BoolComp (evalExpr env e /= 0)
evalCond env penv (PrivComp rel2 (v, es) e) =
  evalPrivRel2 rel2 (penv v (map (evalExpr env) es)) (evalExpr env e)

data Stmt = While Expr [Stmt]
          | If Expr [Stmt] [Stmt]
       -- TODO elsif
          | Assign (Var, [Expr]) Expr
          | Return

type Probability = Rational

probIf :: Interval Integer -> Interval Integer -> Probability
probIf rs1 rs2 = fromInteger (lengthInterval rs1) / fromInteger (lengthInterval rs1 + lengthInterval rs2)

class Monad m => MonadProb m where
  withProb :: Probability -> m a -> m a -> m a

class MonadProb m => Exec m where
  getEnv :: m EvalEnv
  getPrivEnv :: m EvalPrivEnv
  addEnv :: (Var, [Integer]) -> Integer -> m ()
  -- askIsPrivate :: m (Var -> Bool)          

data ProbT (m :: * -> *) a where
    WithProb  :: Probability -> ProbT m a -> ProbT m a -> ProbT m a
    Bind      :: m b -> (b -> ProbT m a) -> ProbT m a
    Ret       :: a -> ProbT m a

runProbT :: Monad m => ProbT m a -> m a
runProbT (WithProb _ _ _) = error "runProbT: withprob TODO"
runProbT (Bind m k) = m >>= runProbT . k
runProbT (Ret x) = return x

instance MonadTrans ProbT where
    lift m = Bind m Ret

instance Monad m => Monad (ProbT m) where
  return = lift . return
  WithProb p l r >>= k = WithProb p (l >>= k) (r >>= k)
  Bind m k'      >>= k = Bind m (\x -> k' x >>= k)
  Ret x          >>= k = k x

instance Monad m => MonadProb (ProbT m) where
  withProb p left right = WithProb p left right

instance MonadState s m => MonadState s (ProbT m) where
    get = lift get
    put = lift . put

newtype M a = M { runM :: ProbT (State PrgState) a }
    deriving (Monad, MonadProb, MonadState PrgState)

instance Exec M where
  getEnv = gets (\s v xs -> fromMaybe (error "getEnv") (Map.lookup (v, xs) (publicState s)))
  getPrivEnv = gets (\s v xs -> fromMaybe (error "getPrivEnv") (Map.lookup (v, xs) (privateState s)))
  addEnv vxs i = modify (\s -> s { publicState = Map.insert vxs i (publicState s) })
  -- askIsPrivate = 

type IsPrivate = Var -> Bool

viewCond :: IsPrivate -> Expr -> Cond
viewCond isPrivate (Op2 (Rel2 rel2) (Var v es) e2)
  | isPrivate v =
  PrivComp rel2 (v, es) e2
viewCond _ e = CondExpr e

execStmt :: Exec m => IsPrivate -> Stmt -> m ()
execStmt isPrivate (If condExp ifTrue ifFalse) =
  do env  <- getEnv
     penv <- getPrivEnv
     -- isPrivate <- askIsPrivate
     let cond = viewCond isPrivate condExp
     case evalCond env penv cond of
       BoolComp b -> execStmts isPrivate (if b then ifTrue else ifFalse)
       IntervalComp iTrue iFalse ->
         withProb (probIf iTrue iFalse)
                  (execStmts isPrivate ifTrue)
                  (execStmts isPrivate ifFalse)
execStmt isPrivate (Assign (v, es) e) =
    do env <- getEnv
       addEnv (v,map (evalExpr env) es) (evalExpr env e)
execStmt isPrivate loop@(While cond body) = execStmt isPrivate (If cond (body ++ [loop]) [])
execStmt _ Return = return ()

execStmts :: Exec m => IsPrivate -> [Stmt] -> m ()
execStmts isPrivate = mapM_ (execStmt isPrivate)

data Mode = Const
          | Observable
          | Public
          | Secret
          | Private

isPublic :: Mode -> Bool
isPublic Const = True
isPublic Observable = True
isPublic Public = True
isPublic Secret = False
isPublic Private = False

data Decl = Decl Mode Type Var (Interval Expr) -- e.g. secret x : int(3)
                                               -- const x : int(3) = 2
          | Code Stmt

execDecl :: Exec m => IsPrivate -> Decl -> m ()
execDecl _         (Decl _ _ _v [])   = {-addEnv (v, TODO)-} return ()
execDecl _         (Decl _m _ _v _rs) = error "execDecl TODO"
execDecl isPrivate (Code s)           = execStmt isPrivate s

type Program = [Decl]

execProgram :: Exec m => IsPrivate -> Program -> m ()
execProgram isPrivate = mapM_ (execDecl isPrivate)

runProgram :: Program -> PrgState
runProgram prg = flip execState initialState
               . runProbT
               . runM
               . execProgram isPrivate
               $ prg
  where isPrivate _ = False -- TODO
        initialState = PrgState Map.empty Map.empty

-- Check ranges in declarations
type TypingEnv = Map Var (Mode , Type)

type StateIdent = Integer

-- program counter
                  -- , transitions  :: [Transition]
data PrgState = PrgState { publicState  :: Map (Var,[Integer]) Integer
                         , privateState :: Map (Var,[Integer]) (Interval Integer)
                         }
  deriving (Show)

           {-
data Transition = Transition { probability :: Rational
                             , target      :: StateIdent }

type Chain = Map StateIdent State

translateProgram :: Program -> State
translateProgram = undefined
-}

-- Var

{-
update :: State -> Decl -> State
update s (Decl m ty v interval)
    | isPublic m = s { publicState = Map.insert v ( (publicState s) }
    | otherwise  = ?
update s (Code stm) = ?

trPrg :: TypingEnv -> Chain -> StateIdent -> Program -> State
trPrg env chain ident [] = error "no return" -- Map.lookup chain ident
trPrg env chain ident (Decl mode ty v interval) = 

-- -}
-- -}
-- -}
-- -}
-- -}
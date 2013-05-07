{-# LANGUAGE GADTs, KindSignatures, MultiParamTypeClasses, GeneralizedNewtypeDeriving, FlexibleInstances, UndecidableInstances #-}
module Types where

import Prelude hiding (LT, GT, EQ)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List
import Data.Maybe
import Control.Monad.State
import Numeric
--import Data.Functor.Identity

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
       -- TODO elif: | If [(Expr, [Stmt])] [Stmt]
          | Assign (Var, [Expr]) Expr
       -- | Random (Var, [Expr]) (Interval Expr)
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

data BinTree n a where
  Fork :: n -> BinTree n a -> BinTree n a -> BinTree n a
  Leaf :: a -> BinTree n a
  deriving (Show)

type ProbTree = BinTree Probability

instance Monad (BinTree n) where
  return = Leaf
  Fork p l r >>= k = Fork p (l >>= k) (r >>= k)
  Leaf x     >>= k = k x

mapBinTree :: (n -> n') -> (a -> a') -> BinTree n a -> BinTree n' a'
mapBinTree f g (Fork x l r) = Fork (f x) (mapBinTree f g l) (mapBinTree f g r)
mapBinTree _ g (Leaf x) = Leaf (g x)

instance Functor (BinTree n) where
  fmap = liftM

{-
instance Applicative (BinTree n) where
  pure = return
  (<*>) = ap
-}

instance n ~ Probability => MonadProb (BinTree n) where
  withProb = Fork

data ProbT (m :: * -> *) a where
    WithProb  :: Probability -> ProbT m a -> ProbT m a -> ProbT m a
    Bind      :: m b -> (b -> ProbT m a) -> ProbT m a
    Ret       :: a -> ProbT m a

runProbT :: (MonadState s m, MonadProb n) => (s -> a -> b) -> ProbT m a -> m (n b)
runProbT f (WithProb p ifTrue ifFalse) =
  do s <- get
     ifTrue' <- runProbT f ifTrue
     put s
     ifFalse' <- runProbT f ifFalse
     put s
     return (withProb p ifTrue' ifFalse')
runProbT f (Bind m k) = m >>= runProbT f . k
runProbT f (Ret x) = do s <- get
                        return (return (f s x))

instance MonadTrans ProbT where
    lift m = Bind m Ret

instance Monad m => Monad (ProbT m) where
  return = lift . return
  WithProb p l r >>= k = WithProb p (l >>= k) (r >>= k)
  Bind m k'      >>= k = Bind m (\x -> k' x >>= k)
  Ret x          >>= k = k x

instance Monad m => Functor (ProbT m) where
  fmap = liftM

instance Monad m => MonadProb (ProbT m) where
  withProb p left right = WithProb p left right

instance MonadState s m => MonadState s (ProbT m) where
    get = lift get
    put = lift . put

newtype M a = M { runM :: ProbT (State PrgState) a }
    deriving (Monad, MonadProb, MonadState PrgState)

instance Exec M where
  getEnv = gets (\s v xs -> fromMaybe (error ("getEnv: " ++ show (v,xs))) (Map.lookup (v, xs) (publicState s)))
  getPrivEnv = gets (\s v _UNUSED_xs -> fromMaybe (error "getPrivEnv") (Map.lookup v (privateState s)))
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
execStmt _ (Assign (v, es) e) =
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

isPublicMode, isPrivateMode :: Mode -> Bool
isPublicMode Const = True
isPublicMode Observable = True
isPublicMode Public = True
isPublicMode Secret = False
isPublicMode Private = False
isPrivateMode = not . isPublicMode

data Initializer =
   NoInit
 | ExpInit Expr
 | IntervalInit [Range Expr]

data Decl = Decl Mode Type Var Initializer -- e.g. secret x : int(3)
                                           -- const x : int(3) = 2
          | Code Stmt

execDecl :: Exec m => IsPrivate -> Decl -> m ()
execDecl _         (Decl _ _ _ NoInit)      = return ()
execDecl isPrivate (Decl _ _ v (ExpInit e)) = execStmt isPrivate (Assign (v,[]) e)
execDecl _isPrivate (Decl _m _ _v _rs)       = error "execDecl TODO"
execDecl isPrivate (Code s)                 = execStmt isPrivate s

type Program = [Decl]

execProgram :: Exec m => IsPrivate -> Program -> m ()
execProgram isPrivate = mapM_ (execDecl isPrivate)

privVars :: Program -> Set Var
privVars ds = Set.fromList [v | Decl m _ v NoInit <- ds, isPrivateMode m]

intervalOfType :: Type -> Interval Integer
intervalOfType (TyInt bits) = [Range 0 (2^bits-1)]
intervalOfType TyArray{} = error "intervalOfType: Array"

initPrivEnv :: Program -> Map Var (Interval Integer)
initPrivEnv ds = Map.fromList [(v,intervalOfType ty) | Decl m ty v NoInit <- ds, isPrivateMode m]

showProbTree :: ProbTree PrgState -> String
showProbTree = show . mapBinTree (($"") . showDouble . fromRational) showPrgState
  where showDouble :: Double -> ShowS
        showDouble = showFFloat Nothing

showPrgState :: PrgState -> String
showPrgState (PrgState pub priv) =
   "Pub:"  ++ intercalate "," (map showPub $ Map.toList pub) ++
  ",Priv:" ++ intercalate "," (map showPriv $ Map.toList priv)

showPub :: ((Var,[Integer]),Integer) -> String
showPub ((v,[]),i) = v ++ "=" ++ show i
showPub ((v,xs),i) = v ++ show xs ++ "=" ++ show i

showPriv :: (Var,Interval Integer) -> String
showPriv (v,i) = v ++ "=" ++ showInterval i

showInterval :: Interval Integer -> String
showInterval = concatMap showRange

showRange :: Range Integer -> String
showRange (Range i j) = "[" ++ show i ++ ".." ++ show j ++ "]"

runProgram :: Program -> ProbTree PrgState
runProgram prg = flip evalState initialState
               . runProbT const
               . runM
               . execProgram isPrivate
               $ prg
  where isPrivate = (`Set.member` privVars prg)
        privEnv = initPrivEnv prg
        initialState = PrgState Map.empty privEnv

-- Check ranges in declarations
type TypingEnv = Map Var (Mode , Type)

type StateIdent = Integer

-- program counter
                  -- , transitions  :: [Transition]
data PrgState = PrgState { publicState  :: Map (Var,[Integer]) Integer
                         , privateState :: Map Var (Interval Integer)
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
    | isPublicMode m = s { publicState = Map.insert v ( (publicState s) }
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

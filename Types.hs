{-# LANGUAGE GADTs, KindSignatures, MultiParamTypeClasses, GeneralizedNewtypeDeriving, FlexibleInstances, UndecidableInstances, FlexibleContexts #-}
module Types where

import Prelude hiding (LT, GT, EQ)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List
import Data.Maybe
import Control.Monad.Reader
import Control.Monad.State
import Numeric
import Debug.Trace
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

validate :: String -> (a -> Bool) -> a -> a
validate msg pred x | pred x = x
                    | otherwise = error $ "validate: " ++ msg

validateInterval :: Interval Integer -> Interval Integer
validateInterval = validate "wellFormedInterval" wellFormedInterval

lengthInterval :: Interval Integer -> Integer
lengthInterval = sum . map lengthRange

singletonInterval :: a -> Interval a
singletonInterval x = [Range x x]

type Var = String

data Type a = TyInt { width :: Int }
            | TyArray { arraySize :: a
                      , elemType  :: Type a }
  deriving (Show)

data Op = Not | Fac
  deriving (Show)

-- Op2 and Rel2 could be extended
-- * And, Or, Xor could be moved from Op2 to Rel2
-- * Op2 could embed any Rel2 using a boolean as an integer semantics
data Op2 = Add | Sub | Mul | Div | Mod | And | Or | Xor | Rel2 Rel2
  deriving (Show)

data Rel2 = LE | LT | GE | GT | EQ | NE
  deriving (Show)

data Expr = Lit Integer
          | Op Op Expr
          | Op2 Op2 Expr Expr
          | Var Var [Expr] -- Var v xs: v is an array, xs are indices
                           -- in particular if xs is null then v is
                           -- just an integer variable.
  deriving (Show)

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
evalExpr env (Op op e)       = evalOp op (evalExpr env e)
evalExpr env (Op2 op2 e1 e2) = evalOp2 op2 (evalExpr env e1) (evalExpr env e2)
evalExpr env (Var v es)      = env v (map (evalExpr env) es)

evalRangeExpr :: EvalEnv -> Range Expr -> Interval Integer
evalRangeExpr env (Range e1 e2) = range (evalExpr env e1) (evalExpr env e2)

evalIntervalExpr :: EvalEnv -> Interval Expr -> Interval Integer
evalIntervalExpr env = validateInterval . concatMap (evalRangeExpr env)

data Cond = CondExpr Expr
          | PrivCond Rel2 (Var, [Expr]) Expr
  deriving (Show)

evalRel2 :: Rel2 -> Integer -> Integer -> Bool
evalRel2 LE = (<=)
evalRel2 LT = (<)
evalRel2 GE = (>=)
evalRel2 GT = (>)
evalRel2 EQ = (==)
evalRel2 NE = (/=)

data IntervalComp = IntervalComp { trueInterval, falseInterval :: Interval Integer }
  deriving (Show)

data CompResult = PrivComp (Var,[Integer]) IntervalComp
                | BoolComp Bool
  deriving (Show)

flipIntervalComp :: IntervalComp -> IntervalComp
flipIntervalComp (IntervalComp x y) = IntervalComp y x

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

splitInterval :: Interval Integer -> Integer -> IntervalComp
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

evalPrivRel2 :: Rel2 -> Interval Integer -> Integer -> IntervalComp
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
evalCond env penv (PrivCond rel2 (v, es) e) =
  let es' = map (evalExpr env) es in
  PrivComp (v, es') $
    evalPrivRel2 rel2 (penv v es') (evalExpr env e)

evalInitializer :: EvalEnv -> Initializer Expr -> Initializer Integer
evalInitializer env NoInit           = NoInit
evalInitializer env (Init e)         = Init (evalExpr env e)
evalInitializer env (IntervalInit i) = IntervalInit (evalIntervalExpr env i)

data Stmt = While Expr [Stmt]
          | For Var Var [Stmt]
          | If Expr [Stmt] [Stmt]
          | Assign (Var, [Expr]) Expr
          | Random (Var, [Expr]) RandExp
          | Return
  deriving (Show)

data RandExp = RandomBit Double
             | RandomInt (Range Expr)
  deriving (Show)

type Probability = Rational

probIf :: Interval Integer -> Interval Integer -> Probability
probIf rs1 rs2 = fromInteger (lengthInterval rs1) / fromInteger (lengthInterval rs1 + lengthInterval rs2)

class Monad m => MonadProb m where
  withProb :: Probability -> m a -> m a -> m a

class (MonadProb m, MonadReader PrgEnv m, MonadState PrgState m) => Exec m where

getEnv :: Exec m => m EvalEnv
getEnv = gets (\s v xs -> fromMaybe (error ("no such public variable: " ++ show (v,xs))) (Map.lookup (v, xs) (publicState s)))

getPrivEnv :: Exec m => m EvalPrivEnv
getPrivEnv = gets (\s v xs -> fromMaybe (error ("no such private variable: " ++ show (v,xs))) (Map.lookup (v, xs) (privateState s)))

addEnv :: Exec m => (Var, [Integer]) -> Integer -> m ()
addEnv vxs i = modify (\s -> s { publicState = Map.insert vxs i (publicState s) })

addPrivEnv :: Exec m => (Var, [Integer]) -> Interval Integer -> m ()
addPrivEnv vxs i = modify (\s -> s { privateState = Map.insert vxs i (privateState s) })

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
     put $ error "should not happen"
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

instance MonadProb m => MonadProb (ReaderT e m) where
  -- withProb p l r = ReaderT (\e -> withProb p (runReaderT l e) (runReaderT r e))
  withProb p l r = do e <- ask
                      lift (withProb p (runReaderT l e) (runReaderT r e))
  -- withProb p l r = lift (withProb p) `ap` l `ap` r -- ReaderT (\e -> withProb p (runReaderT l e) (runReaderT r e))

data PrgEnv = PrgEnv { isPrivate    :: Var -> Bool
                     , varDimension :: Var -> [Integer]
                  -- , prgConstants :: Var -> Maybe Integer
                     }

-- program counter
                  -- , transitions  :: [Transition]
data PrgState = PrgState { publicState  :: Map (Var,[Integer]) Integer
                         , privateState :: Map (Var,[Integer]) (Interval Integer)
                         }
  deriving (Show)

newtype M a = M { runM :: ReaderT PrgEnv (ProbT (State PrgState)) a }
    deriving (Monad, MonadProb, MonadState PrgState, MonadReader PrgEnv)

instance Exec M where

viewCond :: (Var -> Bool) -> Expr -> Cond
viewCond isPriv (Op2 (Rel2 rel2) (Var v es) e2)
  | isPriv v = PrivCond rel2 (v, es) e2
viewCond _ e = CondExpr e

withProbIf :: MonadProb m => Interval Integer -> Interval Integer -> m a -> m a -> m a
withProbIf []    []     _      _       = error "impossible IntervalComp [] []"
withProbIf []    iFalse _      ifFalse = ifFalse
withProbIf iTrue []     ifTrue _       = ifTrue
withProbIf iTrue iFalse ifTrue ifFalse = withProb (probIf iTrue iFalse) ifTrue ifFalse

withProbs :: MonadProb m => Range Integer -> (Integer -> m a) -> m a
withProbs r@(Range i j) f
    | i == j    = f i
    | otherwise = withProb (1 / fromInteger (lengthRange r))
                           (f i)
                           (withProbs (Range (i+1) j) f)

execStmt :: Exec m => Stmt -> m ()
execStmt e = execStmt' e {-do s <- get
                trace ("execStmt=" ++ show e ++ " mem=" ++ showPrgState s) (execStmt' e)-}
execStmt' :: Exec m => Stmt -> m ()
execStmt' (If condExp ifTrue ifFalse) =
  do env  <- getEnv
     penv <- getPrivEnv
     isPriv <- asks isPrivate
     let cond = viewCond isPriv condExp
     case evalCond env penv cond of
       BoolComp b -> execStmts (if b then ifTrue else ifFalse)
       PrivComp (v,es) (IntervalComp iTrue iFalse) ->
         withProbIf iTrue iFalse
                    (addPrivEnv (v,es) iTrue  >> execStmts ifTrue)
                    (addPrivEnv (v,es) iFalse >> execStmts ifFalse)
execStmt' (Assign (v, es) e) =
    do env <- getEnv
       addEnv (v,map (evalExpr env) es) (evalExpr env e)
execStmt' (Random (v, es) (RandomBit d)) =
    withProb (toRational d)
             (execStmt (Assign (v, es) (Lit 1)))
             (execStmt (Assign (v, es) (Lit 0)))
execStmt' (Random (v, es) (RandomInt r)) =
    do env <- getEnv
       let i   = evalRangeExpr env r
           es' = map (evalExpr env) es
       case i of
         []   -> error $ "invalid random range: " ++ show r
         [r'] -> withProbs r' $ execStmt . Assign (v, map Lit es') . Lit
         _    -> error "execStmt: RandomInt: impossible"
execStmt' loop@(While cond body) = execStmt (If cond (body ++ [loop]) [])
execStmt' (For v arr body) =
    do varDim <- asks varDimension
       let len:_ = varDim arr
           stms = [stm | i <- [0..len-1]
                      , stm <- (Assign (v,[]) (Var arr [Lit i]) :
                                body ++
                                [Assign (arr,[Lit i]) (Var v [])]) ]
       execStmts stms

execStmt' Return = return ()

execStmts :: Exec m => [Stmt] -> m ()
execStmts = mapM_ execStmt

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

data Initializer a =
   NoInit
 | Init a
 | IntervalInit (Interval a)

data Decl = Decl Mode (Type Expr) Var (Initializer Expr) -- e.g. secret x : int 3;
          | Cnst Var Integer                             -- const x := 2;
          | Code Stmt

execInit :: Exec m => Var -> Initializer Expr -> m ()
execInit _ NoInit            = return ()
execInit v (Init e)          = do arrDim <- asks varDimension
                                  execStmts [ Assign (v,map Lit ixs) e | ixs <- enumIxs (arrDim v) ]
execInit v (IntervalInit rs) = do env <- getEnv
                                  addPrivEnv (v,[]) (evalIntervalExpr env rs)

execDecl :: Exec m => Decl -> m ()
execDecl (Decl _ _ v init) = execInit v init
execDecl (Cnst v n)        = execStmt (Assign (v,[]) (Lit n))
execDecl (Code s)          = execStmt s

type Program = [Decl]

execProgram :: Exec m => Program -> m ()
execProgram = mapM_ execDecl

privVars :: Program -> Set Var
privVars ds = Set.fromList [v | Decl m _ v _ <- ds, isPrivateMode m]

intervalOfType :: Type a -> Interval Integer
intervalOfType (TyInt bits)   = range 0 (2^bits-1)
intervalOfType (TyArray _ ty) = intervalOfType ty

dimensionOfType :: Type a -> [a]
dimensionOfType (TyArray sz ty) = sz : dimensionOfType ty
dimensionOfType TyInt{}         = []

enumIxs :: [Integer] -> [[Integer]]
enumIxs (sz : szs) = [ (i:ixs) | ixs <- enumIxs szs, i <- [0..sz-1] ]
enumIxs []         = [[]]

instance Functor Type where
  fmap _ (TyInt i)       = TyInt i
  fmap f (TyArray sz ty) = TyArray (f sz) (fmap f ty)

initVarDim :: EvalEnv -> Program -> Map Var [Integer]
initVarDim env ds = Map.fromList
                   [ (v,dimensionOfType ty')
                   | Decl m ty v _ <- ds
                   , let ty' = fmap (evalExpr env) ty
                   ]

initPrivInterval :: EvalEnv -> Type Integer -> Initializer Integer -> Interval Integer
initPrivInterval env ty NoInit           = intervalOfType ty
initPrivInterval env _  (Init _)         = error "initPrivInterval"
initPrivInterval env _  (IntervalInit i) = i

initPrivEnv :: EvalEnv -> Program -> Map (Var,[Integer]) (Interval Integer)
initPrivEnv env ds = Map.fromList $
                   [ ((v,xs),initPrivInterval env ty' init')
                   | Decl m ty v init <- ds
                   , isPrivateMode m
                   , let ty'   = fmap (evalExpr env) ty
                         init' = evalInitializer env init
                   , xs <- enumIxs . dimensionOfType $ ty'
                   ]

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

showPriv :: ((Var,[Integer]),Interval Integer) -> String
showPriv ((v,[]),i) = v ++ "=" ++ showInterval i
showPriv ((v,xs),i) = v ++ show xs ++ "=" ++ showInterval i

showInterval :: Interval Integer -> String
showInterval = concatMap showRange

showRange :: Range Integer -> String
showRange (Range i j) = "[" ++ show i ++ ".." ++ show j ++ "]"

programConstants :: Program -> Map Var Integer
programConstants ds = Map.fromList [ (v,n) | Cnst v n <- ds ]

runProgram :: Program -> ProbTree PrgState
runProgram prg = flip evalState initialState
               . runProbT const
               . flip runReaderT initialEnv
               . runM
               . execProgram
               $ prg
  where isPriv = (`Set.member` privVars prg)
        cstEnv v [] = fromMaybe (error "not a constant") (Map.lookup v (programConstants prg))
        cstEnv v _  = error "unexpected constant array"
        initialEnv = PrgEnv isPriv
                            (fromMaybe (error "not an array") . flip Map.lookup (initVarDim cstEnv prg))
        initialState = PrgState Map.empty (initPrivEnv cstEnv prg)

-- Check ranges in declarations
--type TypingEnv = Map Var (Mode , Type)

--type StateIdent = Integer

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

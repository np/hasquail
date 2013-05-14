{-# LANGUAGE GADTs, KindSignatures, MultiParamTypeClasses, GeneralizedNewtypeDeriving, FlexibleInstances, UndecidableInstances, FlexibleContexts, ScopedTypeVariables #-}
module Types where


import Prelude hiding (LT, GT, EQ, sum, product, concatMap, mapM_, any)
import qualified Prelude as P
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Function (on)
import Data.Set (Set)
import Data.List (intercalate, groupBy, sortBy) -- hiding (sum, product, concatMap, mapM_)
import Data.Maybe
import Data.Foldable
import Data.Traversable
-- import Data.Ratio ((%))
import Control.Arrow ((&&&))
import Control.Applicative
import Control.Monad.Reader hiding (mapM_)
import Control.Monad.State hiding (mapM_)
import Numeric
import Debug.Trace
--import Data.Functor.Identity

import Interval

type Endo a = a -> a

--type Val = String

data Type a = TyInt { width :: Int }
            | TyArray { arraySize :: a
                      , elemType  :: Type a }
  deriving (Show)

instance Traversable Type where
  traverse _ (TyInt i)       = pure (TyInt i)
  traverse f (TyArray sz ty) = TyArray <$> f sz <*> traverse f ty

instance Functor  Type where fmap = fmapDefault
instance Foldable Type where foldMap = foldMapDefault

data Op = Not | Fac
  deriving (Show)

-- Op2 and Rel2 could be extended
-- * And, Or, Xor could be moved from Op2 to Rel2
-- * Op2 could embed any Rel2 using a boolean as an integer semantics
data Op2 = Add | Sub | Mul | Div | Mod | And | Or | Xor | Rel2 Rel2
  deriving (Show)

data Rel2 = LE | LT | GE | GT | EQ | NE
  deriving (Show)

-- 'var' is the type of variables
data Exp var
  = Lit Integer
  | Op Op (Exp var)
  | Op2 Op2 (Exp var) (Exp var)
  | Var var [Exp var] -- Var v xs: v is an array, xs are indices
                       -- in particular if xs is null then v is
                       -- just an integer variable.
  deriving (Show)

instance Traversable Exp where
  traverse _ (Lit i) = pure (Lit i)
  traverse f (Op op e) = Op op <$> traverse f e
  traverse f (Op2 op2 e1 e2) = Op2 op2 <$> traverse f e1 <*> traverse f e2
  traverse f (Var x es) = Var <$> f x <*> traverse (traverse f) es

instance Functor  Exp where fmap = fmapDefault
instance Foldable Exp where foldMap = foldMapDefault

{-# INLINE lit #-}
lit :: Integral n => n -> Exp var
lit = Lit . toInteger

{-# INLINE boolOp #-}
boolOp :: (Eq n, Num n) => (Bool -> Bool) -> n -> n
boolOp op x = if op (x /= 0) then 1 else 0

evalOp :: (Enum n, Eq n, Num n) => Op -> n -> n
evalOp Not = boolOp not
evalOp Fac = \n -> product [1..n]

{-# INLINE boolOp2 #-}
boolOp2 :: (Eq n, Num n) => (Bool -> Bool -> Bool) -> n -> n -> n
boolOp2 op2 x y = if op2 (x /= 0) (y /= 0) then 1 else 0

evalOp2 :: Integral n => Op2 -> n -> n -> n
evalOp2 Add = (+)
evalOp2 Sub = (-)
evalOp2 Mul = (*)
evalOp2 Div = div
evalOp2 Mod = mod
evalOp2 And = boolOp2 (&&)
evalOp2 Or  = boolOp2 (||)
evalOp2 Xor = boolOp2 (/=)
evalOp2 (Rel2 rel2) = \x y -> if evalRel2 rel2 x y then 1 else 0

type EvalEnv n var = var -> [n] -> n
type EvalPrivEnv n var = var -> [n] -> Interval n

evalExp :: Integral n => EvalEnv n var -> Exp var -> n
evalExp _   (Lit i)         = fromInteger i
evalExp env (Op op e)       = evalOp op (evalExp env e)
evalExp env (Op2 op2 e1 e2) = evalOp2 op2 (evalExp env e1) (evalExp env e2)
evalExp env (Var v es)      = env v (map (evalExp env) es)

evalRangeExp :: Integral n => EvalEnv n var -> Range (Exp var) -> Interval n
evalRangeExp env (Range e1 e2) = range (evalExp env e1) (evalExp env e2)

evalIntervalExp :: Integral n => EvalEnv n var -> Interval (Exp var) -> Interval n
evalIntervalExp env = validateInterval . concatMap (evalRangeExp env)

data Cond var
   = CondExp (Exp var)
   | PrivCond Rel2 (var, [Exp var]) (Exp var)
  deriving (Show)

instance Traversable Cond where
  traverse f (CondExp e) = CondExp <$> traverse f e
  traverse f (PrivCond rel2 (v,es) e)
    = PrivCond rel2 <$> ((,) <$> f v <*> traverse (traverse f) es)
                    <*> traverse f e

instance Functor  Cond where fmap = fmapDefault
instance Foldable Cond where foldMap = foldMapDefault

evalRel2 :: Ord a => Rel2 -> a -> a -> Bool
evalRel2 LE = (<=)
evalRel2 LT = (<)
evalRel2 GE = (>=)
evalRel2 GT = (>)
evalRel2 EQ = (==)
evalRel2 NE = (/=)


data CompResult n var
  = PrivComp (var,[n]) (IntervalComp n)
  | BoolComp Bool
  deriving (Show)


evalPrivRel2 :: (Ord a, Num a) => Rel2 -> Interval a -> a -> IntervalComp a
evalPrivRel2 LE rs k = splitInterval rs (k+1)
evalPrivRel2 LT rs k = splitInterval rs k
evalPrivRel2 EQ rs k = IntervalComp i (removeInterval rs k)
                          where i | k `memberInterval` rs = singletonInterval k
                                  | otherwise             = []
evalPrivRel2 GE rs k = flipIntervalComp $ splitInterval rs k
evalPrivRel2 GT rs k = flipIntervalComp $ splitInterval rs (k+1)
evalPrivRel2 NE rs k = flipIntervalComp $ evalPrivRel2 EQ rs k

evalCond :: Integral n => EvalEnv n var -> EvalPrivEnv n var -> Cond var -> CompResult n var
evalCond env _    (CondExp e) = BoolComp (evalExp env e /= 0)
evalCond env penv (PrivCond rel2 (v, es) e) =
  let es' = map (evalExp env) es in
  PrivComp (v, es') $
    evalPrivRel2 rel2 (penv v es') (evalExp env e)

evalInitializer :: Integral n => EvalEnv n var -> Initializer (Exp var) -> Initializer n
evalInitializer   _ NoInit           = NoInit
evalInitializer env (Init e)         = Init (evalExp env e)
evalInitializer env (IntervalInit i) = IntervalInit (evalIntervalExp env i)

data Stm var = While (Exp var) [Stm var]
             | For var var [Stm var]
             | If (Exp var) [Stm var] [Stm var]
             | Assign (var, [Exp var]) (Exp var)
             | Random (var, [Exp var]) (RandExp var)
             | Return
  deriving (Show)

instance Traversable Stm where
  traverse f (While e s) = While <$> traverse f e
                                 <*> traverse (traverse f) s
  traverse f (For v1 v2 s) = For <$> f v1
                                 <*> f v2
                                 <*> traverse (traverse f) s
  traverse f (If e s1 s2) = If <$> traverse f e
                               <*> traverse (traverse f) s1
                               <*> traverse (traverse f) s2
  traverse f (Assign (v, es) e)
    = Assign <$> ((,) <$> f v <*> traverse (traverse f) es)
             <*> traverse f e
  traverse f (Random (v, es) e)
    = Random <$> ((,) <$> f v <*> traverse (traverse f) es)
             <*> traverse f e
  traverse _ Return = pure Return

instance Functor  Stm where fmap = fmapDefault
instance Foldable Stm where foldMap = foldMapDefault

data RandExp var
  = RandomBit Double
  | RandomInt (Range (Exp var))
  deriving (Show)

instance Traversable RandExp where
  traverse _ (RandomBit d) = pure (RandomBit d)
  traverse f (RandomInt r) = RandomInt <$> traverse (traverse f) r

instance Functor  RandExp where fmap = fmapDefault
instance Foldable RandExp where foldMap = foldMapDefault

type Probability = Rational

{-# INLINE probIf #-}
probIf :: Integral n => Interval n -> Interval n -> Probability
probIf rs1 rs2 = fromIntegral (lengthInterval rs1) / fromIntegral (lengthInterval rs1 + lengthInterval rs2)

class Monad m => MonadProb m where
  withProb :: Probability -> m a -> m a -> m a

class (MonadProb m,
       MonadReader (PrgEnv n var) m,
       MonadState (PrgState n var) m,
       Show n,
       Integral n,
       Show var,
       Ord var)
      => Exec n var m where

{-# INLINE getEnv #-}
getEnv :: Exec n var m => m (EvalEnv n var)
getEnv = gets (\s v xs -> fromMaybe (error ("no such public variable: " ++ show (v,xs))) (Map.lookup (v, xs) (publicState s)))

{-# INLINE getPrivEnv #-}
getPrivEnv :: Exec n var m => m (EvalPrivEnv n var)
getPrivEnv = gets (\s v xs -> fromMaybe (error ("no such private variable: " ++ show (v,xs))) (Map.lookup (v, xs) (privateState s)))

{-# INLINE addEnv #-}
addEnv :: Exec n var m => (var, [n]) -> n -> m ()
addEnv vxs i = modify (\s -> s { publicState = Map.insert vxs i (publicState s) })

{-# INLINE addPrivEnv #-}
addPrivEnv :: Exec n var m => (var, [n]) -> Interval n -> m ()
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

instance Functor (BinTree n) where fmap = liftM

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

runProbT :: (MonadState s m, MonadProb n) => ProbT m a -> m (n a)
runProbT (WithProb p ifTrue ifFalse) =
  do s <- get
     ifTrue' <- runProbT ifTrue
     put s
     ifFalse' <- runProbT ifFalse
     put $ error "should not happen, if it does you're doing it wrong..."
     return (withProb p ifTrue' ifFalse')
runProbT (Bind m k) = m >>= runProbT . k
runProbT (Ret x) = return (return x)

instance MonadTrans ProbT where
    lift m = Bind m Ret

instance Monad m => Monad (ProbT m) where
  return = lift . return
  WithProb p l r >>= k = WithProb p (l >>= k) (r >>= k)
  Bind m k'      >>= k = Bind m (\x -> k' x >>= k)
  Ret x          >>= k = k x

instance Monad m => Functor (ProbT m) where fmap = liftM

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

data PrgEnv n var
  = PrgEnv { isPrivate    :: var -> Bool
           , varDimension :: var -> [n]
        -- , prgConstants :: var -> Maybe Integer
           }

-- program counter
                  -- , transitions  :: [Transition]
data PrgState n var
  = PrgState { publicState  :: Map (var,[n]) n
             , privateState :: Map (var,[n]) (Interval n)
             }
  deriving (Eq,Ord,Show)

newtype M n var a = M { runM :: ReaderT (PrgEnv n var)
                                  (ProbT
                                     (State (PrgState n var))) a }
    deriving (Monad, MonadProb,
              MonadState (PrgState n var),
              MonadReader (PrgEnv n var))

instance (Ord var, Show var, Show n, Integral n) => Exec n var (M n var) where

{-# INLINE viewCond #-}
viewCond :: (var -> Bool) -> Exp var -> Cond var
viewCond isPriv (Op2 (Rel2 rel2) (Var v es) e2)
  | isPriv v = PrivCond rel2 (v, es) e2
viewCond _ e = CondExp e

{-# INLINE withProbIf #-}
withProbIf :: (Integral n, MonadProb m) => Interval n -> Interval n -> m a -> m a -> m a
withProbIf []    []     _      _       = error "impossible IntervalComp [] []"
withProbIf []    _      _      ifFalse = ifFalse
withProbIf _     []     ifTrue _       = ifTrue
withProbIf iTrue iFalse ifTrue ifFalse = withProb (probIf iTrue iFalse) ifTrue ifFalse

withProbs :: (Integral n, MonadProb m) => Range n -> (n -> m a) -> m a
withProbs r@(Range i j) f
    | i == j    = f i
{-
-- this seeems to be slower actually
    | i + 1 == j = withProb (1 % 2) (f i) (f j)
    | otherwise = withProb ((m - i) % lengthRange r)
                    (withProbs (Range i m) f)
                    (withProbs (Range (m+1) j) f)
       where
         m = (i + j) `div` 2
-}
    | otherwise = withProb (1 / fromIntegral (lengthRange r))
                           (f i)
                           (withProbs (Range (i+1) j) f)

execStm :: Exec n var m => Stm var -> m ()
execStm e = execStm' e {-do s <- get
                trace ("execStm=" ++ show e ++ " mem=" ++ showPrgState s) (execStm' e)-}
execStm' :: Exec n var m => Stm var -> m ()
execStm' (If condExp ifTrue ifFalse) =
  do env  <- getEnv
     penv <- getPrivEnv
     isPriv <- asks isPrivate
     let cond = viewCond isPriv condExp
     case evalCond env penv cond of
       BoolComp b -> execStms (if b then ifTrue else ifFalse)
       PrivComp (v,es) (IntervalComp iTrue iFalse) ->
         withProbIf iTrue iFalse
                    (addPrivEnv (v,es) iTrue  >> execStms ifTrue)
                    (addPrivEnv (v,es) iFalse >> execStms ifFalse)
execStm' (Assign (v, es) e) =
    do env <- getEnv
       addEnv (v,map (evalExp env) es) (evalExp env e)
execStm' (Random (v, es) (RandomBit d)) =
    withProb (toRational d)
             (execStm (Assign (v, es) (Lit 1)))
             (execStm (Assign (v, es) (Lit 0)))
execStm' (Random (v, es) (RandomInt r)) =
    do env <- getEnv
       let i   = evalRangeExp env r
           es' = map (evalExp env) es
       case i of
         []   -> error $ "invalid random range: " ++ show r
         [r'] -> withProbs r' $ execStm . Assign (v, map lit es') . lit
         _    -> error "execStm: RandomInt: impossible"
execStm' loop@(While cond body) = execStm (If cond (body ++ [loop]) [])
execStm' (For v arr body) =
    do varDim <- asks varDimension
       let len:_ = varDim arr
           stms = [stm | i <- [0..len-1]
                      , stm <- (Assign (v,[]) (Var arr [lit i]) :
                                body ++
                                [Assign (arr,[lit i]) (Var v [])]) ]
       execStms stms

execStm' Return = return ()

{-# INLINE execStms #-}
execStms :: Exec n var m => [Stm var] -> m ()
execStms = mapM_ execStm

data Mode = Constant
          | Observable
          | Public
          | Secret
          | Private
  deriving (Eq)

{-# INLINE isPublicMode #-}
{-# INLINE isPrivateMode #-}
isPublicMode, isPrivateMode :: Mode -> Bool
isPublicMode Constant = True
isPublicMode Observable = True
isPublicMode Public = True
isPublicMode Secret = False
isPublicMode Private = False
isPrivateMode = not . isPublicMode

data Initializer a =
   NoInit
 | Init a
 | IntervalInit (Interval a)

instance Traversable Initializer where
  traverse _ NoInit = pure NoInit
  traverse f (Init x) = Init <$> f x
  traverse f (IntervalInit i) = IntervalInit <$> traverse (traverse f) i

instance Functor  Initializer where fmap = fmapDefault
instance Foldable Initializer where foldMap = foldMapDefault

data Decl var
  = Decl Mode (Type (Exp var)) var (Initializer (Exp var)) -- e.g. secret x : int 3;
  | Cnst var Integer                                       -- const x := 2;
  | Code (Stm var)

instance Traversable Decl where
  traverse f (Decl m ty v ini) = Decl m <$> traverse (traverse f) ty <*> f v <*> traverse (traverse f) ini
  traverse f (Cnst v i) = Cnst <$> f v <*> pure i
  traverse f (Code s) = Code <$> traverse f s

instance Functor  Decl where fmap = fmapDefault
instance Foldable Decl where foldMap = foldMapDefault

execInit :: Exec n var m => var -> Initializer (Exp var) -> m ()
execInit _ NoInit            = return ()
execInit v (Init e)          = do arrDim <- asks varDimension
                                  execStms [ Assign (v,map lit ixs) e | ixs <- enumIxs (arrDim v) ]
execInit v (IntervalInit rs) = do env <- getEnv
                                  addPrivEnv (v,[]) (evalIntervalExp env rs)

execDecl :: Exec n var m => Decl var -> m ()
execDecl (Decl _ _ v ini) = execInit v ini
execDecl (Cnst v n)       = execStm (Assign (v,[]) (lit n))
execDecl (Code s)         = execStm s

type Program var = [Decl var]

{-# INLINE execProgram #-}
execProgram :: Exec n var m => Program var -> m ()
execProgram = mapM_ execDecl

{-# INLINE vars #-}
vars :: Ord var => (Mode -> Bool) -> Program var -> Set var
vars p ds = Set.fromList [v | Decl m _ v _ <- ds, p m]

intervalOfType :: (Ord n, Num n) => Type a -> Interval n
intervalOfType (TyInt bits)   = range 0 (2^bits-1)
intervalOfType (TyArray _ ty) = intervalOfType ty

dimensionOfType :: Type a -> [a]
dimensionOfType (TyArray sz ty) = sz : dimensionOfType ty
dimensionOfType TyInt{}         = []

enumIxs :: (Num n, Enum n) => [n] -> [[n]]
enumIxs (sz : szs) = [ (i:ixs) | ixs <- enumIxs szs, i <- [0..sz-1] ]
enumIxs []         = [[]]

initVarDim :: (Integral n, Ord var) => EvalEnv n var -> Program var -> Map var [n]
initVarDim env ds = Map.fromList
                   [ (v,dimensionOfType ty')
                   | Decl _ ty v _ <- ds
                   , let ty' = fmap (evalExp env) ty
                   ]

-- EvalEnv is not yet used
{-# INLINE initPrivInterval #-}
initPrivInterval :: (Ord n, Num n) => EvalEnv ix var -> Type n -> Initializer n -> Interval n
initPrivInterval   _ ty NoInit           = intervalOfType ty
initPrivInterval   _ _  (Init _)         = error "initPrivInterval"
initPrivInterval   _ _  (IntervalInit i) = i

{-# INLINE initPrivEnv #-}
initPrivEnv :: (Integral n, Ord var) => EvalEnv n var -> Program var -> Map (var,[n]) (Interval n)
initPrivEnv env ds = Map.fromList $
                   [ ((v,xs),initPrivInterval env ty' ini')
                   | Decl m ty v ini <- ds
                   , isPrivateMode m
                   , let ty'  = fmap (evalExp env) ty
                         ini' = evalInitializer env ini
                   , xs <- enumIxs . dimensionOfType $ ty'
                   ]

secretOfType :: Integral n => Type n -> n
secretOfType (TyInt bits)   = 2^bits
secretOfType (TyArray s ty) = secretOfType ty ^ s

-- EvalEnv is not yet used
{-# INLINE secretPrivInterval #-}
secretPrivInterval :: Integral n => EvalEnv ix var -> Type n -> Initializer n -> n
secretPrivInterval _ ty NoInit           = secretOfType ty
secretPrivInterval _ _  (Init _)         = error "initPrivInterval"
secretPrivInterval _ ty  (IntervalInit i) = lengthInterval i ^ product (dimensionOfType ty)

{-# INLINE secretBits #-}
secretBits :: (Show n, Integral n, Show var, Ord var) => EvalEnv n var -> Program var -> n
secretBits cstEnv ds
  = sum [ secretPrivInterval cstEnv ty i
  | Decl Secret ty' _ i' <- ds
  , let i = evalInitializer cstEnv i'
  , let ty = fmap (evalExp cstEnv) ty'
  ]

showProbTree :: (Show n, Show var) => ProbTree (PrgState n var) -> String
showProbTree = show . mapBinTree (($"") . showDouble . fromRational) showPrgState
  where showDouble :: Double -> ShowS
        showDouble = showFFloat Nothing

showPrgState :: (Show n, Show var) => PrgState n var -> String
showPrgState (PrgState pub priv) =
   "Pub:"  ++ intercalate "," (map showPub $ Map.toList pub) ++
  ",Priv:" ++ intercalate "," (map showPriv $ Map.toList priv)

showPub :: (Show var, Show ix, Show a) => ((var,[ix]),a) -> String
showPub ((v,[]),i) = show v ++ "=" ++ show i
showPub ((v,xs),i) = show v ++ show xs ++ "=" ++ show i

showPriv :: (Show ix, Show var, Show a) => ((var,[ix]),Interval a) -> String
showPriv ((v,[]),i) = show v ++ "=" ++ showInterval i
showPriv ((v,xs),i) = show v ++ show xs ++ "=" ++ showInterval i

showInterval :: Show a => Interval a -> String
showInterval = concatMap showRange

showRange :: Show a => Range a -> String
showRange (Range i j) = "[" ++ show i ++ ".." ++ show j ++ "]"

{-# INLINE programConstants #-}
programConstants :: (Num n, Ord var) => Program var -> Map var n
programConstants ds = Map.fromList [ (v,fromInteger n) | Cnst v n <- ds ]

{-# INLINE initialEnv #-}
initialEnv :: (Integral n, Ord var) => EvalEnv n var -> Program var -> PrgEnv n var
initialEnv cstEnv prg = PrgEnv isPriv varDim
  where
    privVars = vars isPrivateMode prg
    isPriv = (`Set.member` privVars)
    varDim = fromMaybe (error "not an array") . flip Map.lookup (initVarDim cstEnv prg)

{-# INLINE runProgram #-}
runProgram :: (Show n, Integral n, Show var, Ord var) => EvalEnv n var -> Program var -> ProbTree (PrgState n var)
runProgram cstEnv prg
               = flip evalState initialState
               . runProbT
               . flip runReaderT (initialEnv cstEnv prg)
               . runM
               . (>> get)
               . execProgram
               $ prg
  where initialState = PrgState Map.empty (initPrivEnv cstEnv prg)

-- Assumption, input lists are strictly increasing
-- therefore output will also be
-- The idea for doing this is that some states might be the same
-- and we would therefore merge them before doing the three different
-- entropies (since all three would merge them)

-- I haven't found any case where this have actually improved
-- the run so it is probably faster if (<++>) = (++)
(<++>) :: (Num n, Ord a) => [(n , a)] -> [(n , a)] -> [(n , a)]
[] <++> ys = ys
xs <++> [] = xs
xs@((px , x) : xs') <++> ys@((py, y) : ys') = case compare x y of
  P.LT -> (px , x) : xs' <++> ys
  P.EQ -> trace "equated" $ (px + py , x) : xs' <++> ys'
  P.GT -> (py , y) : xs <++> ys'

collect :: (Ord a) => ProbTree a -> [(Rational , a)]
collect (Leaf x) = [(1 , x)]
collect (Fork p ls rs) = [ (p  * i , a) | (i , a) <- collect ls]
                    <++> [ (p' * i , a) | (i , a) <- collect rs]
  where
    p' = 1 - p

{-# INLINE entropy #-}
entropy :: Floating c => [Rational] -> c
entropy xs
  -- = - logBase 2 (product [p ** p | (p' , _) <- xs, let p = fromRational p'])
  = - sum [ p * logBase 2 p | p' <- xs , let p = fromRational p']

{-# INLINE mergeBy #-}
mergeBy :: Num n => (a -> a -> Ordering) -> [(n , a)] -> [n]
mergeBy cmp = map (sum . map fst)
            . groupBy (((P.EQ ==) .) . cmp `on` snd)
            . sortBy (cmp `on` snd)

{-
matchVar :: PrgState -> PrgState -> PrgState
matchVar pa pb = PrgState
  { publicState  = Map.unionWithKey const (publicState pa) (Map.mapWithKey (\ _ _ -> 0) (publicState  pb))
  , privateState = Map.unionWithKey const (publicState pa) (Map.mapWithKey (\ _ _ -> 0) (privateState pb))
  }
-}

{-# INLINE expected #-}
expected :: forall n var c. (Show n, Integral n, Show var, Ord var, Num c, Show c , Floating c) => Program var -> (c , n)
expected prg = (t "o" o + t "s" s - t "os" os , secretBits cstEnv prg)
  where
    t :: forall b. Ord b => String -> (PrgState n var -> b) -> c
    t _nm f = let x = entropy (mergeBy (compare `on` f) st)
               in trace ("entropy of " ++ _nm ++ " is " ++ show x) x
    cstEnv v [] = fromMaybe (error "not a constant") (Map.lookup v (programConstants prg))
    cstEnv _ _  = error "unexpected constant array"
    st = trace "running" $ collect $ runProgram cstEnv prg
    o  = filterState Observable . publicState
    s  = filterState Secret     . privateState
    os = o &&& s
    filterState :: Mode -> Map (var,ix) o -> [((var,ix),o)]
    filterState m = filter (\((k,_),_) -> k `Set.member` v) . Map.toList
       where v = vars (== m) prg

-- -}
-- -}
-- -}
-- -}
-- -}

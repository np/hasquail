module Interval where

import Prelude hiding (LT, GT, EQ, sum, product, concatMap, mapM_, any)

import Control.Applicative
import Control.Arrow ((&&&))
import Data.Function (on)
import Data.Foldable
import Data.Traversable

data Range a = Range { rangeFrom :: a, rangeTo :: a }
  deriving (Show)

instance Eq a => Eq (Range a) where
  (==) = (==) `on` (rangeFrom &&& rangeTo)

instance Ord a => Ord (Range a) where
  compare = compare `on` (rangeFrom &&& rangeTo)

instance Traversable Range where
  traverse f (Range x y) = Range <$> f x <*> f y

instance Functor  Range where fmap = fmapDefault
instance Foldable Range where foldMap = foldMapDefault

-- lengthRange (Range i i) = i - i + 1 = 1
{-# INLINE lengthRange #-}
lengthRange :: Num a => Range a -> a
lengthRange (Range i j) = j - i + 1

{-# INLINE wellFormedRange #-}
wellFormedRange :: Ord a => Range a -> Bool
wellFormedRange (Range i j) = i <= j

type Interval a = [Range a]

wellFormedInterval :: Ord a => Interval a -> Bool
wellFormedInterval []  = True
wellFormedInterval [r] = wellFormedRange r
wellFormedInterval (r1@(Range _ j) : r2@(Range k _) : rs)
  = k > j && wellFormedRange r1 && wellFormedInterval (r2 : rs)


{-# INLINE validate #-}
validate :: String -> (a -> Bool) -> a -> a
validate msg p x | p x       = x
                 | otherwise = error $ "validate: " ++ msg
{-# INLINE validateInterval #-}
validateInterval :: Ord a => Interval a -> Interval a
validateInterval = validate "wellFormedInterval" wellFormedInterval

{-# INLINE lengthInterval #-}
lengthInterval :: Num a => Interval a -> a
lengthInterval = sum . map lengthRange

{-# INLINE singletonInterval #-}
singletonInterval :: a -> Interval a
singletonInterval x = [Range x x]

data IntervalComp a
  = IntervalComp { trueInterval, falseInterval :: Interval a }
  deriving (Show)

{-# INLINE flipIntervalComp #-}
flipIntervalComp :: IntervalComp a -> IntervalComp a
flipIntervalComp (IntervalComp x y) = IntervalComp y x

{-# INLINE range #-}
range :: Ord a => a -> a -> Interval a
range i j | i > j     = []
          | otherwise = [Range i j]

{-# INLINE splitInterval #-}
splitInterval :: (Ord a, Num a) => Interval a -> a -> IntervalComp a
splitInterval rs k = IntervalComp [ r' | Range i _j <- rs, r' <- range i (k-1) ]
                                  [ r' | Range _i j <- rs, r' <- range k j     ]

{-# INLINE removeRange #-}
removeRange :: (Ord a, Num a) => Range a -> a -> Interval a
removeRange r@(Range i j) k | not (k `memberRange` r) = [r]
                            | otherwise               = range i (k-1) ++ range (k+1) j

{-# INLINE removeInterval #-}
removeInterval :: (Ord a, Num a) => Interval a -> a -> Interval a
removeInterval rs k = [ r' | r <- rs, r' <- removeRange r k ]

{-# INLINE memberRange #-}
memberRange :: Ord a => a -> Range a -> Bool
memberRange k (Range i j) = k >= i && k <= j

{-# INLINE memberInterval #-}
memberInterval :: Ord a => a -> Interval a -> Bool
k `memberInterval` rs = any (memberRange k) rs

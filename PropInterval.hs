module PropInterval where

import Test.QuickCheck
import Interval

import Data.List

instance (Num a , Arbitrary a) => Arbitrary (Range a) where
  arbitrary = do
   x <- arbitrary
   y <- arbitrary
   return (Range x (x + y))

newtype WF = WF {wf :: Interval Integer} deriving Show

instance Arbitrary WF where
  arbitrary = do
   xs <- fmap (nub . sort) arbitrary
   let toI []       = []
       toI (_ : []) = []
       toI (x : y : xs) = Range x y : toI xs
   return (WF (toI xs))
prop_WF i = wellFormedInterval (wf i)

prop_singleton x = wellFormedInterval (singletonInterval x)
prop_singletonLength x = lengthInterval (singletonInterval x) == 1

prop_range i j = wellFormedInterval (range i j)

prop_removeInterval x i = not (x `memberInterval` removeInterval i x)

prop_removeIntervalWell i x = wellFormedInterval (removeInterval (wf i) x)

main = do
    putStrLn "running prop_WF" 
    qc (prop_WF :: WF -> Bool)
    putStrLn "running prop_singleton" 
    qc (prop_singleton :: Integer -> Bool)
    putStrLn "running prop_singletonLength" 
    qc (prop_singletonLength :: Integer -> Bool)
    putStrLn "running prop_range"
    qc (prop_range :: Integer -> Integer -> Bool)
    putStrLn "running prop_removeInterval"
    qc (prop_removeInterval :: Integer -> Interval Integer -> Bool)
    putStrLn "running prop_removeIntervalWell"
    qc (prop_removeIntervalWell :: WF -> Integer -> Bool)
  where 
    qc p = flip quickCheckWith p stdArgs { maxSuccess = 1000 }

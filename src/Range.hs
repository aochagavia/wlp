module Range where

import qualified Data.Set as Set

data Range = RangeInt IntRange
           | RangeBool BoolRange
    deriving (Show)

data MyInt = Bounded Int
           | MinInfinite
           | MaxInfinite
    deriving (Eq, Show)

type BoolRange = Set.Set Bool
type IntRange = [Interval]
type Interval = (MyInt, MyInt)

instance Ord MyInt where
    compare MinInfinite MinInfinite = EQ
    compare MinInfinite _ = LT
    compare _ MinInfinite = GT
    compare MaxInfinite MaxInfinite = EQ
    compare MaxInfinite _ = GT
    compare _ MaxInfinite = LT
    compare (Bounded x) (Bounded y) = compare x y

rFalse, rTrue :: Range
rFalse = RangeBool $ Set.singleton False
rTrue = RangeBool $ Set.singleton True

leftInfinite, rightInfinite :: Int -> Range
leftInfinite n = RangeInt $ [(MinInfinite, Bounded n)]
rightInfinite n = RangeInt $ [(Bounded n, MaxInfinite)]

bounded :: Int -> Int -> Range
bounded low up = RangeInt $ [(Bounded low, Bounded up)]

unionRange :: Range -> Range -> Range
unionRange (RangeBool b1) (RangeBool b2) = RangeBool $ Set.union b1 b2
unionRange (RangeInt r1) (RangeInt r2) = RangeInt $ undefined

unionRange _ _ = error "Called unionRange with incompatible ranges"

intersectRange :: Range -> Range -> Range
intersectRange (RangeBool b1) (RangeBool b2) = RangeBool $ Set.intersection b1 b2
intersectRange (RangeInt r1) (RangeInt r2) = undefined
intersectRange _ _ = error "Called intersectRange with incompatible ranges"

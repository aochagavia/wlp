module Range where

import qualified Data.Set as Set

data Range = RangeInt IntRange
           | RangeBool BoolRange
    deriving (Show)

data IntRange = InclusiveInclusive MyInt MyInt
              | Disjoint IntRange IntRange
    deriving (Show)

data MyInt = Bounded Int
           | MinInfinite
           | MaxInfinite
    deriving (Eq, Show)

type BoolRange = Set.Set Bool

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
leftInfinite n = RangeInt $ InclusiveInclusive MinInfinite $ Bounded n
rightInfinite n = RangeInt $ InclusiveInclusive (Bounded n) MaxInfinite

bounded :: Int -> Int -> Range
bounded low up = RangeInt $ InclusiveInclusive (Bounded low) (Bounded up)

unionRange :: Range -> Range -> Range
unionRange (RangeBool b1) (RangeBool b2) = RangeBool $ Set.union b1 b2
unionRange (RangeInt r1) (RangeInt r2) = RangeInt $ unionRangeInt r1 r2
    where unionRangeInt :: IntRange -> IntRange -> IntRange
          unionRangeInt (InclusiveInclusive begin1 end1) (InclusiveInclusive begin2 end2) = undefined

unionRange _ _ = error "Called unionRange with incompatible ranges"

intersectRange :: Range -> Range -> Range
intersectRange (RangeBool b1) (RangeBool b2) = RangeBool $ Set.intersection b1 b2
intersectRange (RangeInt r1) (RangeInt r2) = undefined
intersectRange _ _ = error "Called intersectRange with incompatible ranges"

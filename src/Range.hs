module Range where

import qualified Data.Map as Map
import qualified Data.Set as Set

data Range = RangeInt IntRange
           | RangeBool BoolRange
           | RangeArray Range
    deriving (Show)

data MyInt = Bounded Int
           | MinInfinite
           | MaxInfinite
    deriving (Eq, Show)

type BoolRange = Set.Set Bool
-- |A union of integer intervals.
-- The intervals are non-overlapping and increasing, which means:
-- As an invariant, we require that 1 + the upper bound of the n'th element
-- is strictly less than the lower bound of the n+1'th element
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

increment :: MyInt -> MyInt
increment (Bounded i) = Bounded $ i+1
increment MaxInfinite = MaxInfinite
increment MinInfinite = error "Minus infinity has no successor"

-- |Add an interval to the range, respecting the invariants.
addToIntRange :: Interval -> IntRange -> IntRange
addToIntRange (l1, u1) [] = [(l1, u1)]
addToIntRange (l1, u1) ((l2, u2):r2)
    | increment u1 < l2 = (l1, u1) : (l2, u2) : r2
    | increment u2 < l1 = (l2, u2) : addToIntRange (l1, u1) r2
    -- the overlap may cover every interval, so we have to recurse over the range
    | otherwise = addToIntRange (min l1 l2, max u1 u2) r2

rFalse, rTrue :: Range
rFalse = RangeBool $ Set.singleton False
rTrue = RangeBool $ Set.singleton True

leftInfinite, rightInfinite :: Int -> Range
leftInfinite n = RangeInt [(MinInfinite, Bounded n)]
rightInfinite n = RangeInt [(Bounded n, MaxInfinite)]

bounded :: Int -> Int -> Range
bounded low up = RangeInt [(Bounded low, Bounded up)]

unionRange :: Range -> Range -> Range
unionRange (RangeBool b1) (RangeBool b2) = RangeBool $ Set.union b1 b2
unionRange (RangeInt r1) (RangeInt r2) = RangeInt $ unionIntRange r1 r2
    where
    unionIntRange [] r2 = r2
    unionIntRange r1 [] = r1
    unionIntRange ((l1, u1):r1) ((l2, u2):r2)
        | increment u1 < l2 = (l1, u1) : unionIntRange r1 ((l2, u2):r2)
        | increment u2 < l1 = (l2, u2) : unionIntRange ((l1, u1):r1) r2
        -- the intervals overlap, so their union is a bigger interval
        | otherwise = unionIntRange (addToIntRange (min l1 l2, max u1 u2) r1) r2

unionRange _ _ = error "Called unionRange with incompatible ranges"

intersectRange :: Range -> Range -> Range
intersectRange (RangeBool b1) (RangeBool b2) = RangeBool $ Set.intersection b1 b2
intersectRange (RangeInt r1) (RangeInt r2) = RangeInt $ intersectIntRange r1 r2
    where
    intersectIntRange [] _ = []
    intersectIntRange _ [] = []
    intersectIntRange ((l1, u1):r1) ((l2, u2):r2)
        | u1 < l2 = intersectIntRange r1 ((l2, u2):r2)
        | u2 < l1 = intersectIntRange ((l1, u1):r1) r2
        | u1 <= u2 = (max l1 l2, min u1 u2) : intersectIntRange r1 ((l2, u2):r2)
        | u2 <= u1 = (max l1 l2, min u1 u2) : intersectIntRange ((l1, u1):r1) r2
intersectRange _ _ = error "Called intersectRange with incompatible ranges"

-- |Take the pointwise union or intersection of maps to ranges.
-- If a key is in both maps, we take union or intersection,
-- otherwise we use the full range as default.
unionRanges, intersectRanges :: Ord k => Map.Map k Range -> Map.Map k Range -> Map.Map k Range
unionRanges = Map.intersectionWith unionRange
intersectRanges = Map.unionWith intersectRange

module Range where

import qualified Data.Map as Map
import qualified Data.Set as Set

-- ^Define ranges for our literal types and operations on these ranges.

-- |Represents the range of the given literal type.
-- We use a sum type since expressions are represented untyped.
data Range = RangeInt IntRange
           | RangeBool BoolRange
           | RangeArray Range
    deriving (Eq, Ord, Show)

-- |Represents the endpoint of intervals of integers.
data InfiniteInt = MinInfinite
           | Bounded Int
           | MaxInfinite
    deriving (Eq, Show)

instance Ord InfiniteInt where
    compare MinInfinite MinInfinite = EQ
    compare MinInfinite _ = LT
    compare _ MinInfinite = GT
    compare MaxInfinite MaxInfinite = EQ
    compare MaxInfinite _ = GT
    compare _ MaxInfinite = LT
    compare (Bounded x) (Bounded y) = compare x y

-- |While perhaps not the most efficient representation,
-- treating ranges as sets makes most operations easy to define.
type BoolRange = Set.Set Bool
-- |A union of integer intervals.
-- The intervals are non-overlapping and increasing, which means:
-- As an invariant, we require that 1 + the upper bound of the n'th element
-- is strictly less than the lower bound of the n+1'th element
type IntRange = [Interval]
-- |Represents the closed interval with respective lower and upper bound.
type Interval = (InfiniteInt, InfiniteInt)

-- |Move the boundary of an interval up by one integer.
-- Note that this resuls in an error when the boundary is 'MinInfinite'.
increment :: InfiniteInt -> InfiniteInt
increment (Bounded i) = Bounded $ i+1
increment MaxInfinite = MaxInfinite
increment MinInfinite = error "Minus infinity has no successor"

-- |Is there no value in this range?
isEmpty :: Range -> Bool
isEmpty (RangeArray r) = isEmpty r
isEmpty (RangeBool optionSet) = Set.null optionSet
isEmpty (RangeInt intervals) = all intervalEmpty intervals
    where
    intervalEmpty (lower, upper) = lower > upper

-- |Add an interval to the range, respecting the invariants.
addToIntRange :: Interval -> IntRange -> IntRange
addToIntRange (l1, u1) [] = [(l1, u1)]
addToIntRange (l1, u1) ((l2, u2):r2)
    | increment u1 < l2 = (l1, u1) : (l2, u2) : r2
    | increment u2 < l1 = (l2, u2) : addToIntRange (l1, u1) r2
    -- the overlap may cover every interval, so we have to recurse over the range
    | otherwise = addToIntRange (min l1 l2, max u1 u2) r2

-- |A range consisting of only one boolean value.
rFalse, rTrue :: Range
rFalse = RangeBool $ Set.singleton False
rTrue = RangeBool $ Set.singleton True

-- |A range that contains the bound and everything smaller or greater.
leftInfinite, rightInfinite :: Int -> Range
leftInfinite n = RangeInt [(MinInfinite, Bounded n)]
rightInfinite n = RangeInt [(Bounded n, MaxInfinite)]

-- |The range that consists exactly of the given interval.
-- For a range that contains only 'n', use 'bounded n n'.
bounded :: Int -> Int -> Range
bounded low up = RangeInt [(Bounded low, Bounded up)]

-- |The range that contains every integer except the given one.
exclude :: Int -> Range
exclude i = RangeInt [(MinInfinite, Bounded (i-1)), (Bounded (i+1), MaxInfinite)]

-- |Take the union of two ranges, consisting of all values that are in either.
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

-- |Take the intersection of two ranges, consisting of all values that are in both.
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

-- |Represents an abstract map of ranges, refined by 'Predicate.RangeMap'.
type RangeMap' k = Map.Map k Range
-- |Represents an abstract map of aliases, refined by 'Predicate.AliasMap'.
type AliasMap' k = Map.Map k (Set.Set k)

-- |Alias the first key to the second key and the other way around.
symmetrical :: Ord k => k -> k -> AliasMap' k
symmetrical k1 k2 = Map.fromList [(k1, Set.singleton k2), (k2, Set.singleton k1)]

-- |Takes two AliasMaps that are symmetrical and transitive, and makes a
-- symmetrical and transitive intersection/union.
intersectAliases, unionAliases :: Ord k => AliasMap' k -> AliasMap' k -> AliasMap' k
intersectAliases = Map.intersectionWith Set.intersection
-- Note that this case is a lot trickier to make the intersection very simple.
unionAliases = Map.foldlWithKey insertAliases
    where
    -- Insert a new or existing key in the map.
    -- If the key is already in the map, takes the union.
    -- Does not ensure the map is symmetrical or transitive!
    insertKey :: Ord k => k -> Set.Set k -> AliasMap' k -> AliasMap' k
    insertKey key new map = case Map.lookup key map of
        Nothing -> Map.insert key new map
        Just existing -> Map.insert key (Set.union new existing) map
    -- Perform insertKey (Set.singleton k) for all x in the set.
    insertAll :: Ord k => Set.Set k -> k -> AliasMap' k -> AliasMap' k
    insertAll set k map = Set.fold (\x -> insertKey x (Set.singleton k)) map set
    -- Insert a new alias in the map.
    -- The map will remain symmetrical and transitive.
    insertAlias :: Ord k => AliasMap' k -> k -> k -> AliasMap' k
    insertAlias map k1 k2 = insertKey k1 (Set.singleton k2) $
        insertKey k2 (Set.singleton k2) $
        (case Map.lookup k1 map of
            -- which also implies that no x has x R k1
            Nothing -> id
            -- (x R k1) <-> (k1 R x), so we also want k2 R x and x R k2
            Just related1 -> insertKey k2 related1 . insertAll related1 k2
        ) $
        (case Map.lookup k2 map of
            -- which also implies that no x has x R k2
            Nothing -> id
            -- (x R k2) <-> (k2 R x), so we also want k1 R x and x R k1
            Just related2 -> insertKey k1 related2 . insertAll related2 k1
        )
        map
    insertAliases :: Ord k => AliasMap' k -> k -> Set.Set k -> AliasMap' k
    insertAliases map k1 = Set.fold (\k2 map -> insertAlias map k1 k2) map

-- |Given a map of keys to ranges, and a map of keys that alias other keys,
-- determine the full amount of aliases and ranges.
-- Ranges should contain all the keys of aliases.
-- Will alias each value to the maximum of all its aliases.
-- If there is no alias greater than itself, will use the range for that value.
unionAliasRange :: Ord k => RangeMap' k -> AliasMap' k -> Map.Map k (Either Range k)
unionAliasRange ranges aliases = Map.foldlWithKey tryAlias Map.empty ranges
    where
    intersectLeftRange (Left r1) (Left r2) = Left $ intersectRange r1 r2
    insertRange k v = Map.insertWith intersectLeftRange k (Left v)
    tryAlias map key range = case Map.lookup key aliases >>= Set.lookupMax of
        Nothing -> insertRange key range map -- not an alias, so continue
        Just maximum -> if key < maximum -- so we don't get cycles of aliases
            then Map.insert key (Right maximum) $ -- also intersect the range
                insertRange maximum range map
            else insertRange key range map

-- |Copy the values to each alias.
-- The original of each alias should be an element of the map.
copyAliases :: Ord k => Map.Map k k -> Map.Map k v -> Map.Map k v
copyAliases aliases values = Map.foldlWithKey copyAlias values aliases
    where
    copyAlias :: Ord k => Map.Map k v -> k -> k -> Map.Map k v
    copyAlias values' alias original = Map.insert alias (values' Map.! original) values'

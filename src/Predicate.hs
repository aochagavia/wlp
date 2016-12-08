module Predicate where

import Rewriting
import Syntax

import qualified Data.Map as Map
import qualified Data.Set as Set

data Range = RangeInt IntRange
           | RangeBool BoolRange
    deriving (Show)

data MyInt = Bounded Int
           | Infinite
    deriving (Show)

data IntRange = InclusiveInclusive MyInt MyInt
              | Disjoint IntRange IntRange
    deriving (Show)

data BoolRange = RTrue
               | RFalse
               | TrueOrFalse
    deriving (Show)

leftInfinite, rightInfinite :: Int -> Range
leftInfinite n = RangeInt $ InclusiveInclusive Infinite $ Bounded n
rightInfinite n = RangeInt $ InclusiveInclusive (Bounded n) Infinite
bounded :: Int -> Int -> Range
bounded low up = RangeInt $ InclusiveInclusive (Bounded low) (Bounded up)

-- |Take the pointwise union or intersection of maps to ranges.
-- If a key is in both maps, we take union or intersection,
-- otherwise we use the full range as default.
unionRange, intersectRange :: Map.Map k Range -> Map.Map k Range -> Map.Map k Range
unionRange = undefined
intersectRange = undefined

-- |Of course, there are expressions that aren't predicates but we're all very smart people so that won't happen.
type Predicate = Expression

-- |We want to exclude trivially true predicates when we want to check them.
-- However, this is not as easy as it sounds: when we're testing an implication,
-- we want the hypothesis to not be trivially *false*. Therefore, we make two
-- functions to calculate a range for each free variable in which this is the case.
-- Of course, this is basically SAT, so we will allow certain trivial cases when
-- the expression gets too complicated to easily reduce.
nonTrivTrue :: Predicate -> Map.Map Name Range
nonTrivTrue (NameExpr name) = Map.singleton name (RangeBool RFalse) -- We got here through boolean operators, so it must be a boolean
nonTrivTrue (Negation p) = nonTrivFalse p
nonTrivTrue (Operated Implies p q) = nonTrivFalse p `intersectRange` nonTrivTrue q
nonTrivTrue (Operated Wedge p q) = nonTrivTrue p `unionRange` nonTrivTrue q
nonTrivTrue (Operated Vee p q) = nonTrivTrue p `intersectRange` nonTrivTrue q
nonTrivTrue (Operated LessThan p q) = fullRangeI p `unionRange` fullRangeI q
nonTrivTrue (Operated LessEqual p q) = fullRangeI p `unionRange` fullRangeI q
nonTrivTrue (Operated Equal p q) = fullRangeI p `unionRange` fullRangeI q

-- |Find a range for the variables that excludes assignments that make it trivially false.
-- See 'nonTrivTrue' for the reasoning.
nonTrivFalse :: Predicate -> Map.Map Name Range
nonTrivFalse (NameExpr name) = Map.singleton name (RangeBool RTrue) -- We got here through boolean operators, so it must be a boolean
nonTrivFalse (Negation p) = nonTrivTrue p
nonTrivFalse (Operated Implies p q) = nonTrivTrue p `unionRange` nonTrivFalse q
nonTrivFalse (Operated Wedge p q) = nonTrivFalse p `intersectRange` nonTrivFalse q
nonTrivFalse (Operated Vee p q) = nonTrivFalse p `unionRange` nonTrivFalse q
nonTrivFalse (Operated LessThan (NameExpr n) (LiteralExpr (LiteralInt i)))
    = Map.singleton n $ leftInfinite $ i-1
nonTrivFalse (Operated LessThan (LiteralExpr (LiteralInt i)) (NameExpr n))
    = Map.singleton n $ rightInfinite $ i+1
nonTrivFalse (Operated LessEqual (NameExpr n) (LiteralExpr (LiteralInt i)))
    = Map.singleton n $ leftInfinite i
nonTrivFalse (Operated LessEqual (LiteralExpr (LiteralInt i)) (NameExpr n))
    = Map.singleton n $ rightInfinite i
nonTrivFalse (Operated Equal (LiteralExpr (LiteralInt i)) (NameExpr n))
    = Map.singleton n $ bounded i i
nonTrivFalse (Operated Equal (NameExpr n) (LiteralExpr (LiteralInt i)))
    = Map.singleton n $ bounded i i

-- |Give every free variable in the predicate the full range of integers.
fullRangeI :: Predicate -> Map.Map Name Range
fullRangeI pred = Map.fromList [(var, fullRange) | var <- free]
    where
    free = Set.toList $ freeVarsExpr pred
    fullRange = RangeInt $ InclusiveInclusive Infinite Infinite

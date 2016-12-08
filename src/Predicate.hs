module Predicate where

import Range
import Rewriting
import Syntax

import qualified Data.Map as Map
import qualified Data.Set as Set

-- |Take the pointwise union or intersection of maps to ranges.
-- If a key is in both maps, we take union or intersection,
-- otherwise we use the full range as default.
unionRanges, intersectRanges :: Ord k => Map.Map k Range -> Map.Map k Range -> Map.Map k Range
unionRanges = Map.intersectionWith unionRange
intersectRanges = Map.unionWith intersectRange
-- |Of course, there are expressions that aren't predicates but we're all very smart people so that won't happen.
type Predicate = Expression

-- |We want to exclude trivially true predicates when we want to check them.
-- However, this is not as easy as it sounds: when we're testing an implication,
-- we want the hypothesis to not be trivially *false*. Therefore, we make two
-- functions to calculate a range for each free variable in which this is the case.
-- Of course, this is basically SAT, so we will allow certain trivial cases when
-- the expression gets too complicated to easily reduce.
nonTrivTrue :: Predicate -> Map.Map Name Range
nonTrivTrue (NameExpr name) = Map.singleton name rFalse -- We got here through boolean operators, so it must be a boolean
nonTrivTrue (Negation p) = nonTrivFalse p
nonTrivTrue (Operated Implies p q) = nonTrivFalse p `intersectRanges` nonTrivTrue q
nonTrivTrue (Operated Wedge p q) = nonTrivTrue p `unionRanges` nonTrivTrue q
nonTrivTrue (Operated Vee p q) = nonTrivTrue p `intersectRanges` nonTrivTrue q
nonTrivTrue (Operated _ _ _) = Map.empty -- We could go deeper but let's use the default.

-- |Find a range for the variables that excludes assignments that make it trivially false.
-- See 'nonTrivTrue' for the reasoning.
nonTrivFalse :: Predicate -> Map.Map Name Range
nonTrivFalse (NameExpr name) = Map.singleton name rTrue -- We got here through boolean operators, so it must be a boolean
nonTrivFalse (Negation p) = nonTrivTrue p
nonTrivFalse (Operated Implies p q) = nonTrivTrue p `unionRanges` nonTrivFalse q
nonTrivFalse (Operated Wedge p q) = nonTrivFalse p `intersectRanges` nonTrivFalse q
nonTrivFalse (Operated Vee p q) = nonTrivFalse p `unionRanges` nonTrivFalse q
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

-- |Give infinite range to free variables without a range
-- We need a type to handle the case where the expression is a single name
defaultInfinite :: Type -> Expression -> Map.Map Name Range -> Map.Map Name Range
defaultInfinite ty expr rangeHavers = rangeHavers `Map.union` fullRange ty expr

-- |Give all free variables an infinite range, using the type of the expression
fullRange :: Type -> Expression -> Map.Map Name Range
fullRange ty expr = fullRangeFor <$> typeInferExpr ty expr
    where
    fullRangeFor :: Type -> Range
    fullRangeFor (Primitive BoolType) = RangeBool $ Set.fromList [True, False]
    fullRangeFor (Primitive IntType) = RangeInt $ [(MinInfinite, MaxInfinite)]

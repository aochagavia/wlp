module Predicate where

import Range
import Rewriting
import Syntax

import qualified Data.Map as Map
import qualified Data.Set as Set

-- |Of course, there are expressions that aren't predicates but we're all very smart people so that won't happen.
type Predicate = Expression

-- |Map variables and array indices to the range of values they can take.
type AssignMap = Map.Map AsgTarget Range

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
nonTrivTrue _ = Map.empty -- TODO: find some other cases to cover

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
nonTrivFalse (Operated _ _ _) = Map.empty -- We could go deeper but let's use the default.
nonTrivFalse _ = Map.empty -- TODO: find some other cases to cover

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
    fullRangeFor (Primitive IntType) = RangeInt [(MinInfinite, MaxInfinite)]
    fullRangeFor (Array prim) = RangeArray $ fullRangeFor (Primitive prim)

-- |Normalize a predicate to eliminate various implications and trivial truths.
-- This isn't a full reduction but should get us far enough to generate test cases.
normalize :: Predicate -> Predicate
-- | ~ ~ a === a
normalize (Negation (Negation exp)) = exp -- Which is not true in constructive logic!
normalize (Negation exp) = Negation $ normalize exp
-- | e1 => (e2 => e3) === (e1 /\ e2) => e3
normalize (Operated Implies e1 (Operated Implies e2 e3)) = normalize $ (e1' /\. e2') =>. e3'
    where
    e1' = normalize e1
    e2' = normalize e2
    e3' = normalize e3
-- | (True /\ e1) = e1 and (False /\ e1) = False (and symmetrically)
normalize (Operated Wedge e1 (LiteralExpr (LiteralBool True))) = normalize e1
normalize (Operated Wedge e1 (LiteralExpr (LiteralBool False))) = b False
normalize (Operated Wedge (LiteralExpr (LiteralBool True)) e1) = normalize e1
normalize (Operated Wedge (LiteralExpr (LiteralBool False)) e1) = b False
-- | (True \/ e1) = True and (False \/ e1) = e1 (and symmetrically)
normalize (Operated Vee e1 (LiteralExpr (LiteralBool True))) = b True
normalize (Operated Vee e1 (LiteralExpr (LiteralBool False))) = normalize e1
normalize (Operated Vee (LiteralExpr (LiteralBool True)) e1) = b True
normalize (Operated Vee (LiteralExpr (LiteralBool False)) e1) = normalize e1
-- | True -> e1 === e1 and False -> e1 === True
normalize (Operated Implies (LiteralExpr (LiteralBool True)) e1) = normalize e1
normalize (Operated Implies (LiteralExpr (LiteralBool False)) e1) = b True
normalize (Operated op e1 e2) = Operated op (normalize e1) (normalize e2)
normalize (Forall var exp) = Forall var (normalize exp)
normalize e = e


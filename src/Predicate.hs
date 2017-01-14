module Predicate where

import Eval
import Range
import Rewriting
import Syntax

import qualified Data.Map as Map
import qualified Data.Set as Set

-- |Of course, there are expressions that aren't predicates but we're all very smart people so that won't happen.
type Predicate = Expression

-- |Map variables and array indices to the range of values they can take.
type RangeMap = Map.Map AsgTarget Range
-- |Map variables and array indices to the others they are equal to.
type AliasMap = Map.Map AsgTarget (Set.Set AsgTarget)
-- |Map variables and array indices to their aliases or a range.
type RangeAliasMap = Map.Map AsgTarget (Either Range AsgTarget)

-- |We want to exclude trivially true predicates when we want to check them.
-- However, this is not as easy as it sounds: when we're testing an implication,
-- we want the hypothesis to not be trivially *false*. Therefore, we make two
-- functions to calculate a range for each free variable in which this is the case.
-- Of course, this is basically SAT, so we will allow certain trivial cases when
-- the expression gets too complicated to easily reduce.
nonTrivRange :: Bool -> Predicate -> RangeMap
nonTrivRange bool (NameExpr name)
    = Map.singleton (NameTarget name) $ RangeBool $ Set.singleton bool
        -- We got here through boolean operators, so it must be a boolean
nonTrivRange bool (Index (NameExpr array) i)
    = Map.singleton (ArrTarget array i) $ RangeBool $ Set.singleton bool

nonTrivRange bool (Negation p) = nonTrivRange (not bool) p

nonTrivRange True (Operated Implies p q)
    = nonTrivRange False p `intersectRanges` nonTrivRange True q
nonTrivRange False (Operated Implies p q)
    = nonTrivRange True p `unionRanges` nonTrivRange False q
nonTrivRange True (Operated Wedge p q)
    = nonTrivRange True p `unionRanges` nonTrivRange True q
nonTrivRange True (Operated Vee p q)
    = nonTrivRange True p `intersectRanges` nonTrivRange True q
nonTrivRange False (Operated Wedge p q)
    = nonTrivRange False p `intersectRanges` nonTrivRange False q
nonTrivRange False (Operated Vee p q)
    = nonTrivRange False p `unionRanges` nonTrivRange False q

nonTrivRange True (Operated LessThan (NameExpr n) (LiteralExpr (LiteralInt i)))
    = Map.singleton (NameTarget n) $ rightInfinite i
nonTrivRange True (Operated LessThan (LiteralExpr (LiteralInt i)) (NameExpr n))
    = Map.singleton (NameTarget n) $ leftInfinite i
nonTrivRange True (Operated LessEqual (NameExpr n) (LiteralExpr (LiteralInt i)))
    = Map.singleton (NameTarget n) $ rightInfinite $ i + 1
nonTrivRange True (Operated LessEqual (LiteralExpr (LiteralInt i)) (NameExpr n))
    = Map.singleton (NameTarget n) $ leftInfinite $ i - 1
-- The same as above but for indexing
nonTrivRange True (Operated LessThan (Index (NameExpr n) e) (LiteralExpr (LiteralInt i)))
    = Map.singleton (ArrTarget n e) $ rightInfinite i
nonTrivRange True (Operated LessThan (LiteralExpr (LiteralInt i)) (Index (NameExpr n) e))
    = Map.singleton (ArrTarget n e) $ leftInfinite i
nonTrivRange True (Operated LessEqual (Index (NameExpr n) e) (LiteralExpr (LiteralInt i)))
    = Map.singleton (ArrTarget n e) $ rightInfinite $ i + 1
nonTrivRange True (Operated LessEqual (LiteralExpr (LiteralInt i)) (Index (NameExpr n) e))
    = Map.singleton (ArrTarget n e) $ leftInfinite $ i - 1
nonTrivRange True (Operated Equal (LiteralExpr (LiteralInt i)) (Index (NameExpr n) e))
    = Map.singleton (ArrTarget n e) $ bounded i i
nonTrivRange True (Operated Equal (Index (NameExpr n) e) (LiteralExpr (LiteralInt i)))
    = Map.singleton (ArrTarget n e) $ bounded i i

nonTrivRange False (Operated LessThan (NameExpr n) (LiteralExpr (LiteralInt i)))
    = Map.singleton (NameTarget n) $ leftInfinite $ i-1
nonTrivRange False (Operated LessThan (LiteralExpr (LiteralInt i)) (NameExpr n))
    = Map.singleton (NameTarget n) $ rightInfinite $ i+1
nonTrivRange False (Operated LessEqual (NameExpr n) (LiteralExpr (LiteralInt i)))
    = Map.singleton (NameTarget n) $ leftInfinite i
nonTrivRange False (Operated LessEqual (LiteralExpr (LiteralInt i)) (NameExpr n))
    = Map.singleton (NameTarget n) $ rightInfinite i
nonTrivRange False (Operated Equal (LiteralExpr (LiteralInt i)) (NameExpr n))
    = Map.singleton (NameTarget n) $ bounded i i
nonTrivRange False (Operated Equal (NameExpr n) (LiteralExpr (LiteralInt i)))
    = Map.singleton (NameTarget n) $ bounded i i
-- The same as above but for indexing
nonTrivRange False (Operated LessThan (Index (NameExpr n) e) (LiteralExpr (LiteralInt i)))
    = Map.singleton (ArrTarget n e) $ leftInfinite $ i-1
nonTrivRange False (Operated LessThan (LiteralExpr (LiteralInt i)) (Index (NameExpr n) e))
    = Map.singleton (ArrTarget n e) $ rightInfinite $ i+1
nonTrivRange False (Operated LessEqual (Index (NameExpr n) e) (LiteralExpr (LiteralInt i)))
    = Map.singleton (ArrTarget n e) $ leftInfinite i
nonTrivRange False (Operated LessEqual (LiteralExpr (LiteralInt i)) (Index (NameExpr n) e))
    = Map.singleton (ArrTarget n e) $ rightInfinite i
nonTrivRange False (Operated Equal (LiteralExpr (LiteralInt i)) (Index (NameExpr n) e))
    = Map.singleton (ArrTarget n e) $ bounded i i
nonTrivRange False (Operated Equal (Index (NameExpr n) e) (LiteralExpr (LiteralInt i)))
    = Map.singleton (ArrTarget n e) $ bounded i i

nonTrivRange _ _ = Map.empty -- TODO: find some other cases to cover

-- |Determine which variables have to have identical values when we want to
-- avoid trivially true (or false) instantiations.
nonTrivAlias :: Bool -> Predicate -> AliasMap
nonTrivAlias bool (Negation p)
    = nonTrivAlias (not bool) p
nonTrivAlias True (Operated Implies p q)
    = nonTrivAlias False p `unionAliases` nonTrivAlias True q
nonTrivAlias False (Operated Implies p q)
    = nonTrivAlias True p `intersectAliases` nonTrivAlias False q
nonTrivAlias True (Operated Vee p q)
    = nonTrivAlias True p `unionAliases` nonTrivAlias True q
nonTrivAlias False (Operated Vee p q)
    = nonTrivAlias False p `intersectAliases` nonTrivAlias False q
nonTrivAlias True (Operated Wedge p q)
    = nonTrivAlias True p `intersectAliases` nonTrivAlias True q
nonTrivAlias False (Operated Wedge p q)
    = nonTrivAlias False p `unionAliases` nonTrivAlias False q
nonTrivAlias False (Operated Equal (NameExpr n1) (NameExpr n2))
    -- avoid duplicate entries
    | n1 /= n2 = symmetrical (NameTarget n1) (NameTarget n2)
nonTrivAlias False (Operated Equal (NameExpr n1) (Index (NameExpr n2) e))
    | n1 /= n2 = symmetrical (NameTarget n1) (ArrTarget n2 e)
nonTrivAlias False (Operated Equal (Index (NameExpr n1) e) (NameExpr n2))
    | n1 /= n2 = symmetrical (ArrTarget n1 e) (NameTarget n2)
nonTrivAlias False (Operated Equal (Index (NameExpr n1) e1) (Index (NameExpr n2) e2))
    | (n1, e1) /= (n2, e2) = symmetrical (ArrTarget n1 e1) (ArrTarget n2 e2)
nonTrivAlias _ _ = Map.empty -- TODO: find some other cases to cover

-- |Give infinite range to free variables without a range
-- We need a type to handle the case where the expression is a single name
defaultInfinite :: Type -> Expression -> RangeMap -> RangeMap
defaultInfinite ty expr rangeHavers = rangeHavers `Map.union` fullRange ty expr

-- |Give all free variables an infinite range, using the type of the expression
fullRange :: Type -> Expression -> RangeMap
fullRange ty expr = fullRangeFor <$> typeInferExpr ty expr

fullRangeFor :: Type -> Range
fullRangeFor (Primitive BoolType) = RangeBool $ Set.fromList [True, False]
fullRangeFor (Primitive IntType) = RangeInt [(MinInfinite, MaxInfinite)]
fullRangeFor (Array prim) = RangeArray $ fullRangeFor (Primitive prim)

-- |Write the predicate in prenex' normal form
-- In PNF, all quantifiers are moved to the front of the predicate
-- (which makes finding counterexamples a lot easier)
-- In P'NF, we only have Forall, so we also allow (a single) Negation in between Forall
prenex' :: Predicate -> Predicate
prenex' = foldExpression (LiteralExpr, NameExpr, op, neg, Index, Repby, Forall)
    where
    -- Refresh (only) the given variable
    refresh' :: (FreeVars syntax, Bindable var) => var -> syntax -> syntax
    refresh' var expr = refresh (Set.singleton $ toName var) expr
    -- Replaces any free instances of the given variable
    -- Since we get a lot of double negations, eliminate them
    neg (Negation p) = p
    neg p = Negation p
    -- Pull quantifiers outside of operators
    -- (∀p) /\ q === ∀(p /\ q) and symmetrically, and dually
    op Wedge (Forall var p) q = Forall var $ op Wedge p $ refresh' var q
    op Wedge q (Forall var p) = Forall var $ op Wedge p $ refresh' var q
    op Vee (Forall var p) q = Forall var $ op Vee p $ refresh' var q
    op Vee q (Forall var p) = Forall var $ op Vee p $ refresh' var q
    -- (¬∀p) /\ q === ¬∀(p\/¬q) and symmetrically, and dually
    op Wedge (Negation (Forall var p)) q
        = Negation $ Forall var $ op Vee p $ neg $ refresh' var q
    op Wedge q (Negation (Forall var p))
        = Negation $ Forall var $ op Vee p $ neg $ refresh' var q
    op Vee (Negation (Forall var p)) q
        = Negation $ Forall var $ op Wedge p $ neg $ refresh' var q
    op Vee q (Negation (Forall var p))
        = Negation $ Forall var $ op Wedge p $ neg $ refresh' var q
    -- (p => q) === (~p \/ q), combined with the rules above
    op Implies (Forall var p) q = Negation $ Forall var $ neg $ op Implies p (refresh' var q)
    op Implies q (Forall var p) = Forall var $ op Implies (refresh' var q) p
    op Implies (Negation (Forall var p)) q
        = Negation $ Forall var $ neg $ op Implies p $ refresh' var q
    op Implies q (Negation (Forall var p))
        = Negation $ Forall var $ neg $ op Implies (refresh' var q) (neg p)
    op o p q = Operated o p q

-- |Normalize a predicate to eliminate various implications and trivial truths.
-- This isn't a full reduction but should get us far enough to generate test cases.
normalize :: Predicate -> Predicate
normalize = stripForall . prenex' . normalize'
    where
    -- | ~ ~ a === a
    normalize' (Negation (Negation exp)) = exp -- Which is not true in constructive logic!
    normalize' (Negation exp) = Negation $ normalize' exp
    -- | e1 => (e2 => e3) === (e1 /\ e2) => e3
    normalize' (Operated Implies e1 (Operated Implies e2 e3)) = normalize' $ (e1' /\. e2') =>. e3'
        where
        e1' = normalize' e1
        e2' = normalize' e2
        e3' = normalize' e3
    -- | (True /\ e1) = e1 and (False /\ e1) = False (and symmetrically)
    normalize' (Operated Wedge e1 (LiteralExpr (LiteralBool True))) = normalize' e1
    normalize' (Operated Wedge e1 (LiteralExpr (LiteralBool False))) = b False
    normalize' (Operated Wedge (LiteralExpr (LiteralBool True)) e1) = normalize' e1
    normalize' (Operated Wedge (LiteralExpr (LiteralBool False)) e1) = b False
    -- | (True \/ e1) = True and (False \/ e1) = e1 (and symmetrically)
    normalize' (Operated Vee e1 (LiteralExpr (LiteralBool True))) = b True
    normalize' (Operated Vee e1 (LiteralExpr (LiteralBool False))) = normalize' e1
    normalize' (Operated Vee (LiteralExpr (LiteralBool True)) e1) = b True
    normalize' (Operated Vee (LiteralExpr (LiteralBool False)) e1) = normalize' e1
    -- | True -> e1 === e1 and False -> e1 === True
    normalize' (Operated Implies (LiteralExpr (LiteralBool True)) e1) = normalize' e1
    normalize' (Operated Implies (LiteralExpr (LiteralBool False)) e1) = b True
    normalize' (Operated op e1 e2) = Operated op (normalize' e1) (normalize' e2)
    normalize' (Forall var exp) = Forall var (normalize' exp)
    normalize' e = e

    -- Get rid of all forall quantifiers in the front of the expression
    stripForall :: Predicate -> Predicate
    stripForall (Forall var exp) = stripForall exp
    stripForall exp = exp

-- |Is there no quantifier whatsoever in this formula?
-- Predicates with quantifiers are hard to test, so we reject quantifierful ones
isQuantifierFree :: Predicate -> Bool
isQuantifierFree = foldExpression
    ( const True -- LiteralExpr
    , const True -- NameExpr
    , const (&&) -- Operated
    , id -- Negation
    , const $ const True -- Index
    , const $ const -- Repby
    , const $ const False -- Forall
    )

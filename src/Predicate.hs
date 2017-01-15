module Predicate where

import Eval
import Range
import Rewriting
import Syntax

import qualified Data.Map as Map
import qualified Data.Set as Set

import Debug.Trace

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
nonTrivRange True (Operated Equal (LiteralExpr (LiteralInt i)) (NameExpr n))
    = Map.singleton (NameTarget n) $ exclude i
nonTrivRange True (Operated Equal (NameExpr n) (LiteralExpr (LiteralInt i)))
    = Map.singleton (NameTarget n) $ exclude i
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
    = Map.singleton (ArrTarget n e) $ exclude i
nonTrivRange True (Operated Equal (Index (NameExpr n) e) (LiteralExpr (LiteralInt i)))
    = Map.singleton (ArrTarget n e) $ exclude i

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

-- If all y in Y have P(y), then ∀x∈X P(x) is equivalent to ∀x∈(X \ Y) P(x)
-- (and ~∀x∈X P(x) is equivalent to ~∀x∈(X \ Y) P(x))
nonTrivRange _ (Quantify ForAll var expr) = nonTrivRange True expr
-- If all y in Y have ~P(y), then ∃x∈X P(x) is equivalent to ∃x∈(X \ Y) P(x)
-- (and ~∃x∈X P(x) is equivalent to ~∃x∈(X \ Y) P(x))
nonTrivRange _ (Quantify Exists var expr) = nonTrivRange False expr

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

-- |Write the predicate in prenex normal form
-- In PNF, all quantifiers are moved to the front of the predicate
-- (which makes finding counterexamples a lot easier)
prenex :: Predicate -> Predicate
prenex = foldExpression (LiteralExpr, NameExpr, op, neg, Index, Repby, Quantify)
    where
    -- Refresh (only) the given variable
    refresh' :: (FreeVars syntax, Bindable var) => var -> syntax -> syntax
    refresh' var expr = refresh (Set.singleton $ toName var) expr
    -- Replaces any free instances of the given variable
    -- Since we get a lot of double negations, eliminate them
    neg (Negation p) = p
    neg (Quantify ForAll v p) = Quantify Exists v $ neg p
    neg (Quantify Exists v p) = Quantify ForAll v $ neg p
    neg p = Negation p
    -- Pull quantifiers outside of operators
    -- (∀p) /\ q === ∀(p /\ q) and symmetrically, and dually
    op Wedge (Quantify qu var p) q
        = Quantify qu var $ op Wedge p $ refresh' var q
    op Wedge q (Quantify qu var p)
        = Quantify qu var $ op Wedge p $ refresh' var q
    op Vee (Quantify qu var p) q
        = Quantify qu var $ op Vee p $ refresh' var q
    op Vee q (Quantify qu var p)
        = Quantify qu var $ op Vee p $ refresh' var q
    -- (p => q) === (~p \/ q), combined with the rules above
    op Implies (Quantify ForAll var p) q
        = Quantify Exists var $ op Implies (refresh' var p) q
    op Implies (Quantify Exists var p) q
        = Quantify ForAll var $ op Implies (refresh' var p) q
    op Implies p (Quantify qu var q)
        = Quantify qu var $ op Implies (refresh' var p) q
    op o p q = Operated o p q

-- |Normalize a predicate to eliminate various implications and trivial truths.
-- This isn't a full reduction but should get us far enough to generate test cases.
normalize :: Predicate -> Predicate
normalize = stripForall . prenex . normalize'
    where
    normalize' = foldExpression (LiteralExpr, NameExpr, operated, negation, index, repby, Quantify)
    -- | ~ ~ a === a
    negation (Negation exp) = exp
    -- ~(x < y) = x >= y
    negation (Operated LessThan e1 e2) = operated LessEqual e2 e1
    negation (Operated LessEqual e1 e2) = operated LessThan e2 e1
    negation (LiteralExpr (LiteralBool bool)) = b $ not bool
    negation exp = Negation exp
    -- Evaluate as much as possible.
    operated op (LiteralExpr l1) (LiteralExpr l2) = LiteralExpr $ operate op l1 l2
    -- | e1 => (e2 => e3) === (e1 /\ e2) => e3
    operated Implies e1 (Operated Implies e2 e3) = normalize' $ (e1 /\. e2) =>. e3
    -- | (True /\ e1) = e1 and (False /\ e1) = False (and symmetrically)
    operated Wedge e1 (LiteralExpr (LiteralBool True)) = e1
    operated Wedge e1 (LiteralExpr (LiteralBool False)) = b False
    operated Wedge (LiteralExpr (LiteralBool True)) e1 = e1
    operated Wedge (LiteralExpr (LiteralBool False)) e1 = b False
    -- | (True \/ e1) = True and (False \/ e1) = e1 (and symmetrically)
    operated Vee e1 (LiteralExpr (LiteralBool True)) = b True
    operated Vee e1 (LiteralExpr (LiteralBool False)) = e1
    operated Vee (LiteralExpr (LiteralBool True)) e1 = b True
    operated Vee (LiteralExpr (LiteralBool False)) e1 = e1
    -- | deMorgan's laws: (~p /\ ~q) === ~(p \/ q) and dually
    operated Vee (Negation e1) (Negation e2) = neg $ operated Wedge e1 e2
    operated Wedge (Negation e1) (Negation e2) = neg $ operated Vee e1 e2
    -- | True -> e1 === e1 and False -> e1 === True
    operated Implies (LiteralExpr (LiteralBool True)) e1 = e1
    operated Implies (LiteralExpr (LiteralBool False)) e1 = b True
    -- | e1 -> True === True and e1 -> False === Negation e1
    operated Implies e1 (LiteralExpr (LiteralBool True)) = b True
    operated Implies e1 (LiteralExpr (LiteralBool False)) = negation e1
    -- Handle some cases with identical values on both sides of the operators
    operated Vee e1 e2 | e1 == e2 = e1
    operated Wedge e1 e2 | e1 == e2 = e1
    operated Implies e1 e2 | e1 == e2 = b True
    operated LessThan e1 e2 | e1 == e2 = b False
    operated LessEqual e1 e2 | e1 == e2 = b True
    operated Equal e1 e2 | e1 == e2 = b True
    -- Try to evaluate more of the expression
    operated LessThan e1 e2 = moveLiterals LessThan e1 e2
    operated LessEqual e1 e2 = moveLiterals LessEqual e1 e2
    operated Equal e1 e2 = moveLiterals Equal e1 e2
    operated op e1 e2 = Operated op e1 e2

    -- Also simplify unnecessary indexing
    index (Repby arr index ex) index' | index == index' = ex
    index arr index = Index arr index
    repby arr index (Index arr' index') | arr == arr' && index == index' = arr
    repby arr index expr = Repby arr index expr

    -- Group the literals on the same side of an (in)equality operator
    -- we assume that there aren't any sides that aren't evaluated already.
    moveLiterals :: BinaryOp -> Expression -> Expression -> Expression
    -- e1 - e2 >=< e3 === e1 >=< e3 + e2 === e1 - e3 >=< e2
    moveLiterals op (Operated Minus e1 e2@LiteralExpr{}) e3@LiteralExpr{}
        = operated op e1 $ operated Plus e3 e2
    moveLiterals op (Operated Minus e1@LiteralExpr{} e2) e3@LiteralExpr{}
        = operated op (operated Minus e1 e3) e2
    -- e1 + e2 >=< e3 === e1 >=< e3 - e2 === e2 >=< e3 - e1
    moveLiterals op (Operated Plus e1 e2@LiteralExpr{}) e3@LiteralExpr{}
        = operated op e1 $ operated Minus e3 e2
    moveLiterals op (Operated Plus e1@LiteralExpr{} e2) e3@LiteralExpr{}
        = operated op e2 $ operated Minus e1 e1
    -- e1 >=< e2 - e3 === e1 + e3 >=< e2 === e3 >=< e2 - e1
    moveLiterals op e1@LiteralExpr{} (Operated Minus e2 e3@LiteralExpr{})
        = operated op (operated Plus e1 e3) e2
    moveLiterals op e1@LiteralExpr{} (Operated Minus e2@LiteralExpr{} e3)
        = operated op e3 (operated Minus e2 e1)
    -- e1 >=< e2 + e3 === e1 - e3 >=< e2 === e1 - e2 >=< e3
    moveLiterals op e1@LiteralExpr{} (Operated Plus e2 e3@LiteralExpr{})
        = operated op (operated Minus e1 e3) e2
    moveLiterals op e1@LiteralExpr{} (Operated Plus e2@LiteralExpr{} e3)
        = operated op (operated Minus e1 e2) e3
    moveLiterals op e1 e2 = Operated op e1 e2

    -- Get rid of all forall quantifiers in the front of the expression
    stripForall :: Predicate -> Predicate
    stripForall (Quantify ForAll var exp) = stripForall exp
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
    , const $ const $ const False -- Quantify
    )

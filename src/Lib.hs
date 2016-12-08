module Lib where

import Predicate
import Range
import Rewriting
import Syntax
import Util

import qualified Data.Map as Map
import qualified Data.Set as Set
import Test.QuickCheck

-- |Calculate the wlp of a program based on the given postcondition
wlp :: Program -> Expression -> Expression
wlp (Program _ _ s) q = wlp' s q -- TODO: recursion requires that we store this value somewhere

-- | Calculate the wlp of a statement based on the given postcondition
wlp' :: Statement -> Expression -> Expression
wlp' Skip q = q
-- Assignment requires simultaneously replacing all free variables in the postcondition
wlp' (Assign targets exprs) q = replaceVars q $ Map.fromList $ zip targets exprs
wlp' (Sequence stmt1 stmt2) q = wlp' stmt1 $ wlp' stmt2 q
wlp' (Assert condition) q = condition /\. q
wlp' (Assume condition) q = condition =>. q
-- Local variables get renamed so they don't clash with those in the condition
wlp' (Var vars stmt) q = wlp' (refresh names currentFree stmt) q
    where
    currentFree :: Set.Set Name
    currentFree = freeVarsStmt stmt `Set.union` freeVarsExpr q
    names :: [Name]
    names = map toName vars
wlp' stmt q = error $ "Statement " ++ show stmt ++ " has no wlp defined!"

-- |Given a path consisting of elementary statements, compute the wlp of True.
-- We don't handle pre- and postconditions explicitly, but include them in the path.
-- If the wlp is a tautology, the path is correct.
wlpPath :: Statement -> Expression
wlpPath stmt = wlp' stmt $ b True

-- |Find all paths through the program up to the given length.
-- Note that by length we apparently mean the number of 'Sequence's in the statement.
paths :: Int -> Program -> [Statement]
paths n (Program _ _ s) = map fst $ paths' n s
    where
    -- Enumerate all paths through a compound statement, returning the path and length.
    paths' :: Int -> Statement -> [(Statement, Int)]
    paths' n s | n < 0 = []
    paths' n s@Skip = [(s, 0)]
    paths' n s@(Assert _) = [(s, 0)]
    paths' n s@(Assume _) = [(s, 0)]
    paths' n s@(Assign _ _) = [(s, 0)]
    paths' n (Sequence s1 s2) = do
        (path1, length1) <- paths' (n - 1) s1
        (path2, length2) <- paths' (n - 1 - length1) s2
        return (Sequence path1 path2, length1 + length2 + 1)
    paths' n s@(If cond then_ else_) = thenPaths ++ elsePaths
        where
        makeThenPath (path, length) = (assume cond `Sequence` path, length + 1)
        makeElsePath (path, length) = (assume (neg cond) `Sequence` path, length + 1)
        thenPaths = makeThenPath <$> paths' (n-1) then_
        elsePaths = makeElsePath <$> paths' (n-1) else_
    paths' n s@(While cond body) = breakPath : continuePaths
        where
        breakPath = (assume $ neg cond, 0)
        makeContinuePath (path, length) = (assume cond `Sequence` path, length + 1)
        continuePaths = makeContinuePath <$> paths' (n-1) (body `Sequence` s)
    paths' n s@(Var vars stmt) = do
        (path, length) <- paths' n stmt
        return (Var vars path, length)

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

-- | Instantiate the free variables of a predicate and check that it holds.
-- Uses 'Gen' to convert ranges of acceptable values to a single value.
testPredicate :: Predicate -> Property
testPredicate pred = forAll instantiations checkCase -- TODO: if instantiations contains an empty range, pass immediately
    where
    checkCase :: Map.Map Name Literal -> Bool
    checkCase = literalToBool . evaluateClosed pred

    literalToBool :: Literal -> Bool
    literalToBool lit = case lit of
        LiteralBool b -> b
        LiteralInt i -> error "TypeError: cannot cast int to bool"
    evaluateClosed :: Expression -> Map.Map Name Literal -> Literal
    evaluateClosed (LiteralExpr l) env = l
    evaluateClosed (NameExpr name) env = env Map.! name
    evaluateClosed (Operated op e1 e2) env = evalOp op e1' e2'
        where
        e1' = evaluateClosed e1 env
        e2' = evaluateClosed e2 env
    evaluateClosed (Negation e1) env = evalNeg e1'
        where
        e1' = evaluateClosed e1 env
    evaluateClosed (Forall var expr) env = error "forall is undecidable!"

    -- Evaluate expressions of literals.
    -- When types are incorrect, this gives an error.
    evalNeg :: Literal -> Literal
    evalNeg (LiteralBool b1) = LiteralBool $ not b1
    evalOp :: BinaryOp -> Literal -> Literal -> Literal
    evalOp Plus (LiteralInt n1) (LiteralInt n2) = LiteralInt $ n1 + n2
    evalOp Minus (LiteralInt n1) (LiteralInt n2) = LiteralInt $ n1 - n2
    evalOp Wedge (LiteralBool b1) (LiteralBool b2) = LiteralBool $ b1 && b2
    evalOp Vee (LiteralBool b1) (LiteralBool b2) = LiteralBool $ b1 || b2
    evalOp Implies (LiteralBool b1) (LiteralBool b2) = LiteralBool $ (not b1) || b2
    evalOp LessThan (LiteralInt n1) (LiteralInt n2) = LiteralBool $ n1 < n2
    evalOp LessEqual (LiteralInt n1) (LiteralInt n2) = LiteralBool $ n1 <= n2
    evalOp Equal (LiteralInt n1) (LiteralInt n2) = LiteralBool $ n1 == n2

    instantiations :: Gen (Map.Map Name Literal)
    instantiations = mapM rangeToGen $ defaultInfinite bool pred $ nonTrivTrue pred

    rangeToGen :: Range -> Gen Literal
    rangeToGen (RangeInt r) = LiteralInt <$> rangeToGenI r
    rangeToGen (RangeBool r) = LiteralBool <$> rangeToGenB r

    rangeToGenI :: IntRange -> Gen Int
    rangeToGenI (InclusiveInclusive MinInfinite MaxInfinite) = arbitrary :: Gen Int
    rangeToGenI (InclusiveInclusive MinInfinite (Bounded upper)) = sized (\size ->
        choose (upper - size, upper))
    rangeToGenI (InclusiveInclusive (Bounded lower) MaxInfinite) = sized (\size ->
        choose (lower, lower + size))
    rangeToGenI (InclusiveInclusive (Bounded lower) (Bounded upper)) = elements [lower .. upper]
    rangeToGenI (Disjoint r1 r2) = oneof [rangeToGenI r1, rangeToGenI r2]
    rangeToGenB :: BoolRange -> Gen Bool
    rangeToGenB = elements . Set.toList

someFunc :: IO ()
someFunc = putStrLn "someFunc"

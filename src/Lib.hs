module Lib where

import Eval
import Predicate
import Range
import Rewriting
import Syntax
import Util

import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Test.QuickCheck

-- |Calculate the wlp of a program based on the given postcondition
wlp :: Program -> Expression -> Expression
wlp (Program _ _ s) = wlp' s -- TODO: recursion requires that we store this value somewhere

-- | Calculate the wlp of a statement based on the given postcondition
wlp' :: Statement -> Expression -> Expression
wlp' Skip q = q
-- Assignment requires simultaneously replacing all free variables in the postcondition
-- However, handling assignment to arrays is a bit more complicated:
-- translating `a[i]=x` to `a = repby(a,i,e)` means we also have to make sure
-- the assignments to a now occur sequentially, not simultaneously!
-- (Which also means we can't just translate before calculating wlp)
wlp' (Assign targets exprs) q = replace q $ replacements $ zip targets exprs
    where
    -- Recursively build the replacements so we can handle sequentiality.
    -- TODO: use some higher order functions to make it a bit more readable.
    replacements :: [(AsgTarget, Expression)] -> Map.Map Name Expression
    replacements [] = Map.empty
    replacements ((NameTarget name, val) : targets)
        = Map.insert name val $ replacements targets
    replacements ((ArrTarget name index, val) : targets)
        = let result = replacements targets in case Map.lookup name result of
            -- The array isn't initialized
            Nothing -> Map.insert name (Repby (ref name) index val) result
            -- The array is initialized
            Just arr -> Map.insert name (Repby arr index val) result
wlp' (Sequence stmt1 stmt2) q = wlp' stmt1 $ wlp' stmt2 q
wlp' (Assert condition) q = condition /\. q
wlp' (Assume condition) q = condition =>. q
-- Local variables get renamed so they don't clash with those in the condition
wlp' (Var vars stmt) q = wlp' (refresh currentFree stmt) q
    where
    currentFree :: Set.Set Name
    currentFree = Set.fromList $ map toName vars
-- Note that we don't expect while or if statements to be present in the path,
-- since they have just been desugared
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
    paths' n (Var vars stmt) = do
        (path, length) <- paths' n stmt
        return (Var vars path, length)

-- |Instantiate the free variables of a predicate and check that it holds.
-- Uses 'Gen' to convert ranges of acceptable values to a single value.
testPredicate :: Predicate -> Property
testPredicate pred' = checkCase
    where
    -- Normalize the predicate so we don't test too complicated things
    pred :: Predicate
    pred = normalize pred'

    checkCase :: Property
    checkCase =
        if any isEmpty ranges
        then property True -- If the conditions aren't met, we always succeed
        else counterexample (show pred') $ forAll instantiations runCase

    runCase :: Map.Map AsgTarget Literal -> Bool
    runCase = literalToBool . fromRight . evaluateClosed pred . literalize

    -- Make sure any expressions in the AsgTarget get evaluated
    literalize :: Map.Map AsgTarget Literal -> Map.Map AsgTarget Literal
    literalize env = Map.mapKeys (evaluateAsg env) env
    evaluateAsg :: Map.Map AsgTarget Literal -> AsgTarget -> AsgTarget
    evaluateAsg env (NameTarget n) = NameTarget n
    evaluateAsg env (ArrTarget arr index)
        = ArrTarget arr $ LiteralExpr $ fromRight $ evaluateClosed index env

    instantiations :: Gen (Map.Map AsgTarget Literal)
    instantiations = mapM rangeToGen ranges
    ranges :: Map.Map AsgTarget Range
    ranges = defaultInfinite bool pred $ nonTrivTrue pred

    rangeToGen :: Range -> Gen Literal
    rangeToGen (RangeInt r) = LiteralInt <$> rangeToGenI r
    rangeToGen (RangeBool r) = LiteralBool <$> rangeToGenB r
    rangeToGen (RangeArray r) = pure $ LiteralArray r

    rangeToGenI :: IntRange -> Gen Int
    rangeToGenI range = oneof $ map intervalToGenI range

    intervalToGenI :: Interval -> Gen Int
    intervalToGenI (MinInfinite, MaxInfinite) = arbitrary :: Gen Int
    intervalToGenI (MinInfinite, Bounded upper) = sized (\size ->
        choose (upper - size, upper))
    intervalToGenI (Bounded lower, MaxInfinite) = sized (\size ->
        choose (lower, lower + size))
    intervalToGenI (Bounded lower, Bounded upper) = elements [lower .. upper]
    rangeToGenB :: BoolRange -> Gen Bool
    rangeToGenB = elements . Set.toList

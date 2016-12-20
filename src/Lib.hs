module Lib where

import Eval
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
wlp (Program _ _ s) = wlp' s -- TODO: recursion requires that we store this value somewhere

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

-- | Instantiate the free variables of a predicate and check that it holds.
-- Uses 'Gen' to convert ranges of acceptable values to a single value.
testPredicate :: Predicate -> Property
testPredicate pred = forAll instantiations checkCase -- TODO: if instantiations contains an empty range, pass immediately
    where
    checkCase :: Map.Map Name Literal -> Bool
    checkCase = literalToBool . evaluateClosed pred

    instantiations :: Gen (Map.Map Name Literal)
    instantiations = mapM rangeToGen $ defaultInfinite bool pred $ nonTrivTrue pred

    rangeToGen :: Range -> Gen Literal
    rangeToGen (RangeInt r) = LiteralInt <$> rangeToGenI r
    rangeToGen (RangeBool r) = LiteralBool <$> rangeToGenB r

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

someFunc :: IO ()
someFunc = putStrLn "someFunc"

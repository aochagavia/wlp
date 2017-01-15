{-# LANGUAGE NamedFieldPuns #-}
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
wlp' (Var vars stmt) q = wlp' stmt q
    where
    currentFree :: Set.Set Name
    currentFree = Set.map toName $ freeVars q
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
    -- Interpret a program call via inlining.
    -- This should also handle recursive calls since Haskell is lazy.
    paths' n (ProgramCall (Program params returns code) resultAsgs args)
        = paths' n $ Var locals inlined
        where
        assumeToAssert = foldStatement (Skip, Assume, Assert, Assign, Sequence,
            If, While, Var, ProgramCall)
        locals = map (flip Variable int . toName) $ Set.toList $ freeVars inlined
        inlined =
            Assign (map (NameTarget . toName) params) args `Sequence`
            -- We also need to check that our call meets the preconditions
            -- and that the postcondition has already been checked.
            assumeToAssert code `Sequence`
            Assign resultAsgs (map (ref . toName) returns)

-- |Convert a range of values to a QuickCheck generator.
rangeToGen :: Range -> Gen Literal
rangeToGen (RangeInt r) = LiteralInt <$> rangeToGenI r
    where
    rangeToGenI :: IntRange -> Gen Int
    rangeToGenI range = oneof $ map intervalToGenI range
    intervalToGenI :: Interval -> Gen Int
    intervalToGenI (MinInfinite, MaxInfinite) = arbitrary :: Gen Int
    intervalToGenI (MinInfinite, Bounded upper) = sized (\size ->
        choose (upper - size, upper))
    intervalToGenI (Bounded lower, MaxInfinite) = sized (\size ->
        choose (lower, lower + size))
    intervalToGenI (Bounded lower, Bounded upper) = elements [lower .. upper]
rangeToGen (RangeBool r) = LiteralBool <$> rangeToGenB r
    where
    rangeToGenB :: BoolRange -> Gen Bool
    rangeToGenB = elements . Set.toList
rangeToGen (RangeArray r) = pure $ LiteralArray r

-- |Represents the values we chose for variables.
type Instantiations = Map.Map AsgTarget Literal

-- |Represents the outcome of checking a predicate.
data CheckResult
    = NoCases
        -- ^There were no test cases to consider.
        -- This indicates the predicate is surely correct.
    | SuccessForall Predicate
        -- ^Each instantiation of Forall succeeded.
        -- This indicates the predicate is likely correct.
    | SuccessExists Predicate Instantiations
        -- ^There was a successful instantiation of Exists.
        -- This indicates the predicate is surely correct.
    | Counterexample Predicate Instantiations
        -- ^There is a failing instantiation of Forall.
        -- This indicates the predicate is surely incorrect.
    | NoExample Predicate
        -- ^Could not find a case where Exists holds.
        -- This indicates the predicate is likely incorrect.
    deriving (Show)

-- |Do we consider these cases a success?
isSuccess :: CheckResult -> Bool
isSuccess NoCases{} = True
isSuccess SuccessForall{} = True
isSuccess SuccessExists{} = True
isSuccess Counterexample{} = False
isSuccess NoExample{} = False
-- |Is the outcome of these cases sure?
isSure :: CheckResult -> Bool
isSure NoCases{} = True
isSure SuccessForall{} = False
isSure SuccessExists{} = True
isSure Counterexample{} = True
isSure NoExample{} = False

-- |Convert CheckResult to QuickCheck results.
instance Testable CheckResult where
    property = property . isSuccess

-- |Take the surest failure of all the results.
conjunction :: [CheckResult] -> CheckResult
conjunction = foldr findSureFailure NoCases
    where
    findSureFailure r1 r2 = case (isSuccess r1, isSuccess r2) of
        (True, True) -> findSure r1 r2
        (False, True) -> r1
        (True, False) -> r2
        (False, False) -> findSure r1 r2
    findSure r1 r2 = case (isSure r1, isSure r2) of
        (True, True) -> r1
        (False, True) -> r1
        (True, False) -> r2
        (False, False) -> r1

-- | The type of functions that check properties of the instantiations.
type Checker = Gen Instantiations -> Gen CheckResult

-- |Instantiate the free variables of a predicate and check that it holds.
-- Uses 'Gen' to convert ranges of acceptable values to a single value.
testPredicate :: Predicate -> Gen CheckResult
testPredicate basePredicate
    | any isEmpty ranges = pure NoCases
    | otherwise = quantifiedCases True normalizedPredicate instantiations
    where
    normalizedPredicate :: Predicate
    normalizedPredicate = normalize basePredicate

    -- |Evaluate a quantifier-free predicate and conclude based on the quantifier.
    conclude :: Bool -> Predicate -> Checker
    conclude isForall pred instantiationGen = do
        instantiation <- instantiationGen
        let outcome = runCase pred instantiation
        if isForall
        then if outcome
            then return $ SuccessForall pred
            else return $ Counterexample pred instantiation
        else if outcome
            then return $ SuccessExists pred instantiation
            else return $ NoExample pred

    -- |Add a new quantifier to the test.
    quantify :: Bool -> BoundVariable -> Predicate -> Checker -> Checker
    quantify isForall (Variable name ty) pred checkPredicate instantiation = do
        -- TODO: infer ranges
        value <- rangeToGen $ fullRangeFor ty
        let makeInstantiation = Map.insert (NameTarget name) value
        let instantiation' = makeInstantiation <$> instantiation
        result <- checkPredicate instantiation'
        return $ if isForall
        then case result of
            res@NoCases{} -> SuccessForall pred
            res@SuccessForall{} -> SuccessForall pred
            res@SuccessExists{} -> SuccessForall pred
            res@(Counterexample _ inst') -> Counterexample pred inst'
            res@NoExample{} -> NoExample pred
        else case result of
            res@NoCases{} -> SuccessExists pred $ makeInstantiation Map.empty
            res@SuccessForall{} -> SuccessForall pred
            res@(SuccessExists _ inst') -> SuccessExists pred $ makeInstantiation inst'
            res@(Counterexample _ inst') -> NoExample pred
            res@NoExample{} -> NoExample pred

    -- |Take the negation of a test.
    negate :: Predicate -> Checker -> Checker
    negate pred checkPredicate instantiation = do
        result <- checkPredicate instantiation
        return $ case result of
            res@NoCases{} -> NoCases
            res@SuccessForall{} -> NoExample pred
            res@(SuccessExists _ inst') -> Counterexample pred inst'
            res@(Counterexample _ inst') -> SuccessExists pred inst'
            res@NoExample{} -> SuccessForall pred

    -- Check a predicate with quantifiers, where the next quantifier should
    -- be interpreted as ∀ when isForall and ∃ when not.
    quantifiedCases :: Bool -> Predicate -> Checker
    quantifiedCases isForall originalPred@(Negation pred)
        = negate originalPred $ quantifiedCases (not isForall) pred
    quantifiedCases isForall originalPred@(Forall var pred)
        = quantify isForall var originalPred $ quantifiedCases isForall pred
    quantifiedCases isForall pred
        = conclude isForall pred

    -- Evaluate a predicate without quantifiers.
    runCase :: Predicate -> Instantiations -> Bool
    runCase predicate = literalToBool . fromRight . evaluateClosed predicate . literalize

    -- Make sure any expressions in the AsgTarget get evaluated
    literalize :: Map.Map AsgTarget Literal -> Map.Map AsgTarget Literal
    literalize env = if env' == env then env else literalize env'
        where env' = Map.mapKeys (evaluateAsg env) env
    evaluateAsg :: Map.Map AsgTarget Literal -> AsgTarget -> AsgTarget
    evaluateAsg env (NameTarget n) = NameTarget n
    evaluateAsg env target@(ArrTarget arr index)
        = case evaluateClosed index env of
            Left missing -> target
            Right result -> ArrTarget arr $ LiteralExpr $ result

    instantiations :: Gen (Map.Map AsgTarget Literal)
    instantiations = copyAliases aliases <$> rangeInstantiations
    rangeInstantiations :: Gen (Map.Map AsgTarget Literal)
    rangeInstantiations = mapM rangeToGen ranges
    (ranges, aliases) = Map.mapEither id $ allRanges `unionAliasRange` knownAliases
    knownAliases :: AliasMap
    knownAliases = nonTrivAlias True normalizedPredicate
    allRanges :: RangeMap
    allRanges = defaultInfinite bool normalizedPredicate $ nonTrivRange True normalizedPredicate

-- |Use QuickCheck to test each path through the program up to a given length.
wlpCheck :: String -> Program -> Int -> IO CheckResult
wlpCheck testName prog len = do
    putStrLn $ "Testing " ++ testName
    finalResult <- runTests
    if isSuccess finalResult
    then putStrLn $ "Success!"
    else putStrLn $ "Failed: " ++ show finalResult
    return finalResult
    where
    properties :: [Gen CheckResult]
    properties = map (testPredicate . wlpPath) $ paths len prog
    testsToRun :: [IO CheckResult]
    testsToRun = map generate $ concat $ replicateM 10 properties
    runTests :: IO CheckResult
    runTests = conjunction <$> sequence testsToRun

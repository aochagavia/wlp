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
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Test.QuickCheck

-- |Calculate the wlp of a program based on the given postcondition.
-- Usually, you would want to use wlpCheck since it can verify the wlp holds.
wlp :: Program -> Expression -> Expression
wlp (Program _ _ _ s) = wlp' s

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
-- Local variables get put in Forall so they don't clash with those in the condition
wlp' (Var vars stmt) q = addForalls $ wlp' (refresh currentFree qFree stmt) q
    where
    addForalls :: Predicate -> Predicate
    addForalls q = Set.foldr addForall q $ stmtFree `Set.difference` qFree
    addForall :: Name -> Predicate -> Predicate
    addForall var q = forall var int q
    currentFree, qFree, stmtFree :: Set.Set Name
    currentFree = qFree `Set.intersection` stmtFree
    qFree = Set.map toName (freeVars q)
    stmtFree = Set.map toName (Set.fromList vars)
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
paths n (Program _ _ _ s) = map fst $ paths' n s
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
    paths' n (ProgramCall prog resultAsgs args)
        = paths' n $ Var locals inlined
        where
        dropConditions = foldStatement (Skip, const Skip, const Skip, Assign,
            Sequence, If, While, Var, ProgramCall)
        locals = map (flip Variable int . toName) $ Set.toList $ freeVars code'
        -- Make sure we don't accidentally rescope any of our expressions.
        movedToScope = Set.map toName $ allFreeVars args `Set.union` Set.fromList resultAsgs `Set.union` freeVars prog
        (Program _ params' returns' code') = refresh movedToScope Set.empty prog
        inlined =
            Assign (map (NameTarget . toName) params') args `Sequence`
            -- Note that we can't use the pre-/postconditions since we need to
            -- satisfy them, not use them! (Also, they might contain free
            -- variables that we don't want to get bound.)
            dropConditions code' `Sequence`
            Assign resultAsgs (map (ref . toName) returns')

-- |Convert a range of values to a QuickCheck generator.
rangeToGen :: Range -> Maybe (Gen Literal)
rangeToGen r
    | isEmpty r = Nothing
    | otherwise = Just $ rangeToGen' r
    where
    rangeToGen' (RangeInt r) = LiteralInt <$> rangeToGenI r
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
    rangeToGen' (RangeBool r) = LiteralBool <$> rangeToGenB r
        where
        rangeToGenB :: BoolRange -> Gen Bool
        rangeToGenB = elements . Set.toList
    rangeToGen' (RangeArray r) = pure $ LiteralArray r

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

-- | The type of functions that check properties of the instantiations.
type Checker = Gen Instantiations -> Gen CheckResult

-- |Instantiate the free variables of a predicate and check that it holds.
-- Uses 'Gen' to convert ranges of acceptable values to a single value.
testPredicate :: Predicate -> Gen CheckResult
testPredicate basePredicate = case instantiations of
                                Nothing -> pure NoCases
                                Just i  -> quantifiedCases normalizedPredicate i
    where
    normalizedPredicate :: Predicate
    normalizedPredicate = normalize basePredicate

    -- |Evaluate a quantifier-free predicate with free variables
    -- (therefore, it should act as a Forall.)
    conclude :: Predicate -> Checker
    conclude pred instantiationGen = do
        instantiation <- instantiationGen
        let outcome = runCase pred instantiation
        return $ if outcome
            then SuccessForall pred
            else Counterexample pred instantiation

    -- |Add a new quantifier to the test.
    quantify :: Quantifier -> BoundVariable -> Predicate -> Checker -> Checker
    quantify q (Variable name ty) pred checkPredicate instantiation = do
        -- TODO: infer ranges
        -- we can use fromJust here because we are using full ranges
        value <- fromJust $ rangeToGen $ fullRangeFor ty
        let makeInstantiation = Map.insert (NameTarget name) value
        let instantiation' = makeInstantiation <$> instantiation
        results <- replicateM 100 $ checkPredicate instantiation'
        return $ quantifyResults q pred makeInstantiation results

    -- |Collect the results for a single quantifier.
    quantifyResults ForAll pred makeInst = foldr conjoin $ SuccessForall pred
        where
        conjoin res@NoCases{} newRes = newRes
        conjoin res@SuccessForall{} newRes = if isSure newRes && isSuccess newRes
            then res
            else newRes
        conjoin res@SuccessExists{} newRes = newRes
        conjoin res@(Counterexample _ inst') newRes = Counterexample pred $ makeInst inst'
        conjoin res@NoExample{} newRes = if isSuccess newRes
            then NoExample pred
            else newRes
    quantifyResults Exists pred makeInst = foldr disjoin $ NoExample pred
        where
        disjoin res@NoCases{} newRes = if isSuccess newRes
            then newRes
            else NoExample pred
        disjoin res@SuccessForall{} newRes = if isSuccess newRes && isSure newRes
             then newRes
             else res
        disjoin res@(SuccessExists _ inst') newRes = res
        disjoin res@(Counterexample _ inst') newRes = if isSuccess newRes
            then newRes
            else NoExample pred
        disjoin res@NoExample{} newRes = if isSuccess newRes || isSure newRes
            then newRes
            else res

    -- Test a case with quantifiers, when it is in prenex normal form.
    -- Repeatedly strips the quantifier and makes a new test with it.
    quantifiedCases :: Predicate -> Checker
    quantifiedCases originalPred@(Quantify q var pred)
        = quantify q var originalPred $ quantifiedCases pred
    quantifiedCases pred = conclude pred

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

    instantiations :: Maybe (Gen (Map.Map AsgTarget Literal))
    instantiations = (fmap (copyAliases aliases)) <$> rangeInstantiations
    rangeInstantiations :: Maybe (Gen (Map.Map AsgTarget Literal))
    rangeInstantiations = sequence <$> mapM rangeToGen ranges
    (ranges, aliases) = Map.mapEither id $ allRanges `unionAliasRange` knownAliases
    knownAliases :: AliasMap
    knownAliases = nonTrivAlias True normalizedPredicate
    allRanges :: RangeMap
    allRanges = defaultInfinite bool normalizedPredicate $ nonTrivRange True normalizedPredicate

-- |Use QuickCheck to test each path through the program up to a given length.
wlpCheck :: Program -> Int -> IO CheckResult
wlpCheck prog len = do
    putStrLn $ "Testing " ++ name prog
    finalResult <- runTests
    if isSuccess finalResult
    then putStrLn $ "Success! Performed " ++ show maxTests ++ " tests on " ++ show (length allPaths) ++ " paths."
    else putStrLn $ "Failed: " ++ show finalResult
    return finalResult
    where
    maxTests :: Int
    maxTests = 1000 * len
    -- All the paths that can be tested.
    allPaths :: [Statement]
    allPaths = paths len prog
    -- A list of potential test cases.
    properties :: [Gen CheckResult]
    properties = map (testPredicate . wlpPath) allPaths
    -- An infinite list of test cases to run.
    -- Use runTests to run a finite amount of them.
    testsToRun :: [IO CheckResult]
    testsToRun = map generate $ concat $ repeat properties
    runTests :: IO CheckResult
    runTests = runTests' maxTests True True NoCases testsToRun
    -- Run part of a list of test cases, exiting when we're sure of failure
    -- or when we've covered enough cases.
    -- This should short-circuit the cases to avoid infinite loops.
    runTests' :: Int -> Bool -> Bool -> CheckResult -> [IO CheckResult] -> IO CheckResult
    runTests' 0 _ _ res _ = pure res
    runTests' _ _ _ res [] = pure res
    runTests' _ False False res _ = pure res
    runTests' n True True res (t:ts) = do
        newRes <- t
        runTests' (n-1) (isSure newRes) (isSuccess newRes) newRes ts
    runTests' n False True res (t:ts) = do
        newRes <- t
        if isSuccess newRes
        then runTests' (n-1) False True res ts
        else runTests' (n-1) (isSure newRes) False newRes ts
    runTests' n True False res (t:ts) = do
        newRes <- t
        if isSuccess newRes
        then runTests' (n-1) True False res ts
        else runTests' (n-1) (isSure newRes) False newRes ts

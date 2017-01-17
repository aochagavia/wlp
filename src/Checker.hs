module Checker where

import Control.Monad
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Test.QuickCheck

import Eval
import Predicate
import Range
import Syntax
import Util

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
type Checker = Maybe (Gen Instantiations) -> Gen CheckResult

-- Evaluate a predicate without quantifiers.
runCase :: Predicate -> Instantiations -> Bool
runCase predicate = literalToBool . fromRight . evaluateClosed predicate . literalize
    where
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


-- |Evaluate a quantifier-free predicate with no free variables.
-- It should be sure of its result.
conclude :: Predicate -> Checker
conclude pred Nothing = pure $ NoCases -- Can't instantiate, so don't check.
conclude pred (Just instantiationGen) = do
    instantiation <- instantiationGen
    let outcome = runCase pred instantiation
    return $ if outcome
        then SuccessExists pred instantiation
        else Counterexample pred instantiation

-- |Add a new quantifier to the test.
quantify :: Quantifier -> BoundVariable -> Predicate -> Checker -> Checker
quantify q (Variable name ty) pred checkPredicate instantiation = do
    -- we can use fromJust here because we are using full ranges
    value <- fromJust $ rangeToGen $ fullRangeFor ty
    let makeInstantiation = Map.insert (NameTarget name) value
    let instantiation' = fmap makeInstantiation <$> instantiation
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

-- |Convert a range of values to a QuickCheck generator.
-- Used to convert a Map AsgTarget to Gen Instantiations
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

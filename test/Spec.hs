{-# LANGUAGE TemplateHaskell #-}

import Control.Applicative
import qualified Data.Set as Set

import Lib
import Predicate
import Rewriting
import Syntax

import Test.QuickCheck

-- |A program that does absolutely nothing
void :: Program
void = program [] [] []

prop_void :: Property
prop_void = once $ p === q
    where
    q = ref "x" =>. ref "y"
    p = wlp void q

-- |A program that always returns the given Int
intConst :: Int -> Program
intConst n = program [] [("r", int)] [
               assignN ["r"] [i n]
           ]

prop_intCont :: Int -> Property
prop_intCont n = p === expectedP
    where
    q = (ref "r") ==. (i n)
    expectedP = (i n) ==. (i n)
    p = wlp (intConst n) q

-- |An identity program for integers
intId :: Program
intId = program [("x", int)] [("r", int)] [
            assignN ["r"] [ref "x"]
        ]

prop_intId :: Property
prop_intId = once $ p === expectedP
    where
    q = (ref "r") ==. (ref "x")
    expectedP = (ref "x") ==. (ref "x")
    p = wlp intId q

-- |A special test for bound variables
prop_intIdBound :: Property
prop_intIdBound = once $ p === q
    where
    q = forall "r" int (ref "r" >. i 100)
    p = wlp intId q

-- |A program that swaps two variables
-- Uses simultaneous assignment, so might break assignment semantics sometimes.
swapSimultaneous :: Program
swapSimultaneous = program [("x", int), ("y", int)] [("x", int), ("y", int)] [
        assignN ["x", "y"] [ref "y", ref "x"]
    ]

-- |If the substitution goes wrong, we get either x == x or y == y
prop_SwapSimultaneous :: Property
prop_SwapSimultaneous = once $ p === expectedP
    where
    q = ref "x" !=. ref "y"
    p = wlp swapSimultaneous q
    expectedP = ref "y" !=. ref "x"

-- |A program that includes pre- and postconditions.
negateNumber :: Program
negateNumber = program [("x", int)] [("y", int)] [
        assume $ i (-1) <=. ref "x",
        assignN ["y"] [i 0 -. ref "x"],
        assert $ i 1 >=. ref "y"
    ]

-- |Check the specification is preserved by wlp
prop_negateNumber :: Property
prop_negateNumber = once $ p === expectedP
    where
    q = b True
    p = wlp negateNumber q
    expectedP = (i (-1) <=. ref "x") =>. ((i 1 >=. (i 0 -. ref "x")) /\. q)

-- |Overwrites a local variable but doesn't modify anything else.
overwriteLocalVar :: Program
overwriteLocalVar = program [("x", int)] [("y", int)] [
        var [("x", int)] [
            assignN ["x"] [i 37]
        ],
        assignN ["y"] [ref "x"]
    ]

-- |Overwriting a local variable shouldn't overwrite the other variable.
prop_localVarsWork :: Property
prop_localVarsWork = once $ p === expectedP
    where
    q = ref "y" <. i 0
    p = wlp overwriteLocalVar q
    expectedP = ref "x" <. i 0

-- |The example program E from the assignment
exampleProgram :: Program
exampleProgram = program [("x", int)] [("y", int)] [
        assume $ i (-1) <=. ref "x",
        while (i 0 <. ref "x") [ assignN ["x"] [ref "x" -. i 1]],
        assignN ["y"] [ref "x"],
        assert $ ref "y" ==. i 0
    ]

prop_exampleProgramPaths :: Property
prop_exampleProgramPaths = once $ foundPaths === expectedPaths
    where
    foundPaths :: [[Statement]]
    foundPaths = map unSequence $ paths 7 exampleProgram
    expectedPaths :: [[Statement]]
    expectedPaths = [
            [assume $ i (-1) <=. ref "x", assume $ neg $ i 0 <. ref "x", assignN ["y"] [ref "x"], assert $ ref "y" ==. i 0],
            [assume $ i (-1) <=. ref "x", assume $ i 0 <. ref "x", assignN ["x"] [ref "x" -. i 1], assume $ neg $ i 0 <. ref "x", assignN ["y"] [ref "x"], assert $ ref "y" ==. i 0],
            [assume $ i (-1) <=. ref "x", assume $ i 0 <. ref "x", assignN ["x"] [ref "x" -. i 1], assume $ i 0 <. ref "x", assignN ["x"] [ref "x" -. i 1], assume $ neg $ i 0 <. ref "x", assignN ["y"] [ref "x"], assert $ ref "y" ==. i 0]
        ]

prop_exampleProgramIsWrong :: Property
prop_exampleProgramIsWrong = expectFailure $ conjoin $ map (testPredicate . wlpPath) $ paths 7 exampleProgram

-- |The example program E from the assignment, but now it works
exampleProgramFixed :: Program
exampleProgramFixed = program [("x", int)] [("y", int)] [
        assume $ i 0 <=. ref "x",
        while (i 0 <. ref "x") [ assignN ["x"] [ref "x" -. i 1]],
        assignN ["y"] [ref "x"],
        assert $ ref "y" ==. i 0
    ]

prop_exampleProgramIsFixed :: Property
prop_exampleProgramIsFixed = conjoin $ map (testPredicate . wlpPath) $ paths 7 exampleProgramFixed

-- |The minind program from assignment 1
minind :: Program
minind = program [("a", Array IntType), ("i", int), ("N", int)] [("r", int)] [
        assume $ ref "N" >. ref "i",
        var [("min", int)] [
            assignN ["min", "r"] ["a" !!. ref "i", ref "i"],
            while (ref "i" <. ref "N") [
                if_ (("a" !!. ref "i") <. ref "min") [
                    assignN ["min", "r"] ["a" !!. ref "i", ref "i"]
                ] [],
                assignN ["i"] [ref "i" +. i 1]
            ]
        ],
        assert $ forall "j" int (((ref "j" >=. ref "i") /\. (ref "r" <. ref "N")) =>.
            (("a" !!. ref "j") <=. ("a" !!. ref "r")))
    ]

prop_minindWorks :: Property
prop_minindWorks = conjoin $ map (testPredicate . wlpPath) $ paths 10 minind

-- |The minind program from assignment 1 with a broken postcondition
minindWrong :: Program
minindWrong = program [("a", Array IntType), ("i", int), ("N", int)] [("r", int)] [
        assume $ ref "N" >. ref "i",
        var [("min", int)] [
            assignN ["min", "r"] ["a" !!. ref "i", ref "i"],
            while (ref "i" <. ref "N") [
                if_ (("a" !!. ref "i") <. ref "min") [
                    assignN ["min", "r"] ["a" !!. ref "i", ref "i"]
                ] [],
                assignN ["i"] [ref "i" +. i 1]
            ]
        ],
        assert $ forall "j" int (("a" !!. ref "j") <=. ("a" !!. ref "r"))
    ]

prop_minindIsWrong :: Property
prop_minindIsWrong = expectFailure $ conjoin $ map (testPredicate . wlpPath) $ paths 10 minindWrong

-- |Represents parts of expressions that have an explicit type.
class ArbitraryTyped a where
    arbitraryTyped :: Type -> Gen a
instance Arbitrary Type where
    arbitrary = oneof
        [ Primitive <$> arbitraryBoundedEnum
        , Array <$> arbitraryBoundedEnum
        ]
-- Variables are not ArbitraryTyped since we can't use them in an expression.
instance Arbitrary Variable where
    arbitrary = Variable <$> arbitrary <*> arbitrary

instance ArbitraryTyped Literal where
    arbitraryTyped (Primitive IntType) = LiteralInt <$> arbitrary
    arbitraryTyped (Primitive BoolType) = LiteralBool <$> arbitrary
    arbitraryTyped (Array t) = pure $ LiteralArray $ fullRangeFor $ Primitive t
instance ArbitraryTyped BinaryOp where
    arbitraryTyped (Primitive IntType) = elements [Plus, Minus]
    arbitraryTyped (Primitive BoolType) = elements [Wedge, Vee, Implies, LessThan, LessEqual, Equal]

instance ArbitraryTyped Expression where
    arbitraryTyped t@(Primitive IntType) = sized $ \size -> if size <= 0
        then LiteralExpr <$> arbitraryTyped t
        else oneof
            [ LiteralExpr <$> arbitraryTyped t
            , NameExpr <$> arbitrary
            , do
                operator <- arbitraryTyped t
                let (_, leftType, rightType) = operatorType operator
                firstHalf <- choose (0, size)
                Operated
                    <$> pure operator
                    <*> resize firstHalf (arbitraryTyped leftType)
                    <*> resize (size - firstHalf) (arbitraryTyped rightType)
            ]
    -- TODO: merge this with the above somehow?
    arbitraryTyped t@(Primitive BoolType) = sized $ \size -> if size <= 0
        then LiteralExpr <$> arbitraryTyped t
        else oneof
            [ LiteralExpr <$> arbitraryTyped t
            , NameExpr <$> arbitrary
            , do
                operator <- arbitraryTyped t
                let (_, leftType, rightType) = operatorType operator
                firstHalf <- choose (0, size)
                Operated
                    <$> pure operator
                    <*> resize firstHalf (arbitraryTyped leftType)
                    <*> resize (size - firstHalf) (arbitraryTyped rightType)
            , Negation <$> resize (size-1) (arbitraryTyped bool)
            , Forall <$> arbitrary <*> resize (size-1) (arbitraryTyped bool)
            ]

-- |Check that prenex normalization gives predicates in prenex form
prop_prenexGivesPrenex :: Property
prop_prenexGivesPrenex = forAll (arbitraryTyped bool) $
        isPrenex' . prenex'
    where
    isPrenex' :: Predicate -> Bool
    isPrenex' (LiteralExpr _) = True
    isPrenex' (NameExpr _) = True
    isPrenex' (Operated _ p q) = isQuantifierFree p && isQuantifierFree q
    isPrenex' (Negation p) = isPrenex' p
    isPrenex' (Forall _ p) = isPrenex' p

-- |Check that normalization doesn't break predicates
prop_normalizeIsEquivalent :: Property
prop_normalizeIsEquivalent = forAll (arbitraryTyped bool) doCheck
    where
    doCheck pred = isQuantifierFree pred ==> isEquivalent pred (normalize pred)
    isEquivalent p1 p2 = testPredicate ((p1 =>. p2) /\. (p2 =>. p1))

-- |Refreshing should only refresh the given free variables
prop_refreshKeepsVars :: Property
prop_refreshKeepsVars = forAll (arbitraryTyped bool :: Gen Expression) $ (\expr ->
        freeVars expr == freeVars (refresh Set.empty expr))

-- Evil QuickCheck TemplateHaskell hackery
return []
main = $quickCheckAll

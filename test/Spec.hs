{-# LANGUAGE TemplateHaskell #-}

import Control.Applicative
import qualified Data.Map as Map
import qualified Data.Set as Set

import Checker
import Lib
import Predicate
import Range
import Rewriting
import Syntax

import Test.QuickCheck

-- |A program that does absolutely nothing
void :: Program
void = program "void" [] [] []

prop_void :: Property
prop_void = once $ p === q
    where
    q = ref "x" =>. ref "y"
    p = wlp void q

-- |A program that always returns the given Int
intConst :: Int -> Program
intConst n = program "intConst" [] [("r", int)] [
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
intId = program "intId" [("x", int)] [("r", int)] [
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
swapSimultaneous = program "swapSimultaneous" [("x", int), ("y", int)] [("x", int), ("y", int)] [
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
negateNumber = program "negateNumber" [("x", int)] [("y", int)] [
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
overwriteLocalVar = program "overwriteLocalVar" [("x", int)] [("y", int)] [
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
exampleProgram = program "exampleProgram" [("x", int)] [("y", int)] [
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

-- |Don't bind variables that will enter into the WLP
varTest = program "varTest" [] [] [
        assume $ ref "b",
        var [("b", int)] [
            assert $ ref "b"
        ]
    ]

prop_varTestWLP :: Property
prop_varTestWLP = once $ foundWLP === expectedWLP
    where
    foundWLP = wlpPath $ head $ paths 2 varTest
    expectedWLP = ref "b" =>. forall "b" int (ref "b" /\. b True)

-- |Program calls have some interesting edge cases with bound vs. non-bound variables.
asgTest = program "asgTest" [("i", int)] [("j", int)] [
        assume $ ref "i" ==. i 0,
        if_ (ref "b") [
            call ["j"] asgTest [ref "i"]
        ] [
            assignN ["j"] [ref "i"]
        ],
        assert $ ref "j" ==. i 0
    ]

prop_asgTestPaths :: Property
prop_asgTestPaths = once $ foundPaths === expectedPaths
    where
    foundPaths, expectedPaths :: [[Statement]]
    foundPaths = map unSequence $ paths 10 asgTest
    expectedPaths = [
            [
                assume $ ref "i" ==. i 0,
                assume $ ref "b",
                -- this is the interesting part: the local variables get a new name
                var [("x1", int), ("x2", int), ("x3", int)] [
                    -- We have to do some ugly work since `Sequence` is not
                    -- the right associativity.
                    assignN ["x2"] [ref "i"] `Sequence`
                    (skip `Sequence` (
                    (assume $ neg $ ref "x1") `Sequence`
                    assignN ["x3"] [ref "x2"] `Sequence`
                    skip)) `Sequence`
                    assignN ["j"] [ref "x3"]
                ],
                assert $ ref "j" ==. i 0
            ], [
                assume $ ref "i" ==. i 0,
                assume $ neg $ ref "b",
                assignN ["j"] [ref "i"],
                assert $ ref "j" ==. i 0
            ]
        ]

-- |Substituting within a quantifier shouldn't bind variables.
prop_substituteBound :: Property
prop_substituteBound = once $ expectedWLP === foundWLP
    where
    expectedWLP = forall "x1" int $ ref "x" ==. ref "x1"
    foundWLP = wlp' (assignN ["y"] [ref "x"]) $ forall "x" int $ ref "y" ==. ref "x"

exampleProgramIsWrong :: IO CheckResult
exampleProgramIsWrong = wlpCheck exampleProgram 7

-- |The example program E from the assignment, but now it works
exampleProgramFixed :: Program
exampleProgramFixed = program "exampleProgram" [("x", int)] [("y", int)] [
        assume $ i 0 <=. ref "x",
        while (i 0 <. ref "x") [ assignN ["x"] [ref "x" -. i 1]],
        assignN ["y"] [ref "x"],
        assert $ ref "y" ==. i 0
    ]

exampleProgramIsFixed :: IO CheckResult
exampleProgramIsFixed = wlpCheck exampleProgramFixed 7

-- |The example program E from the assignment, with invariant
exampleProgramInv :: Program
exampleProgramInv = program "exampleProgram" [("x", int)] [("y", int)] [
        assume $ i 0 <=. ref "x",
        While (Just $ ref "x" >=. i 0) (i 0 <. ref "x") $ foldSequence [
            assignN ["x"] [ref "x" -. i 1]
        ],
        assignN ["y"] [ref "x"],
        assert $ ref "y" ==. i 0
    ]

exampleProgramInvWorks :: IO CheckResult
exampleProgramInvWorks = wlpCheck exampleProgramInv 7

-- |The example program E from the assignment, with invariant
exampleProgramInvWrong :: Program
exampleProgramInvWrong = program "exampleProgram" [("x", int)] [("y", int)] [
        assume $ i (-1) <=. ref "x",
        While (Just $ ref "x" >=. i 0) (i 0 <. ref "x") $ foldSequence [
            assignN ["x"] [ref "x" -. i 1]
        ],
        assignN ["y"] [ref "x"],
        assert $ ref "y" ==. i 0
    ]

exampleProgramInvIsWrong :: IO CheckResult
exampleProgramInvIsWrong = wlpCheck exampleProgramInvWrong 7

-- |The minind program from assignment 1
minind :: Program
minind = program "minind" [("a", Array IntType), ("i", int), ("N", int)] [("r", int)] [
        assume $ (ref "N" >. ref "i") /\. (ref "i" ==. ref "i'"),
        var [("min", int)] [
            assignN ["min", "r"] ["a" !!. ref "i", ref "i"],
            while (ref "i" <. ref "N") [
                if_ (("a" !!. ref "i") <. ref "min") [
                    assignN ["min", "r"] ["a" !!. ref "i", ref "i"]
                ] [],
                assignN ["i"] [ref "i" +. i 1]
            ]
        ],
        assert $ forall "j" int $ ((ref "j" >=. ref "i'") /\. (ref "j" <. ref "N")) =>.
            (("a" !!. ref "j") >=. ("a" !!. ref "r"))
    ]

minindWorks :: IO CheckResult
minindWorks = wlpCheck minind 20

-- |The minind program from assignment 1 with a broken postcondition
minindWrong :: Program
minindWrong = program "minind" [("a", Array IntType), ("i", int), ("N", int)] [("r", int)] [
        assume $ (ref "N" >. ref "i") /\. (ref "i" ==. ref "i'"),
        var [("min", int)] [
            assignN ["min", "r"] ["a" !!. ref "i", ref "i"],
            while (ref "i" <. ref "N") [
                if_ (("a" !!. ref "i") <. ref "min") [
                    assignN ["min", "r"] ["a" !!. ref "i", ref "i"]
                ] [],
                assignN ["i"] [ref "i" +. i 1]
            ]
        ],
        assert $ forall "j" int $ ((ref "j" >=. ref "i'") /\. (ref "j" <. ref "N")) =>.
            (("a" !!. ref "j") <=. ("a" !!. ref "r"))
    ]

minindIsWrong :: IO CheckResult
minindIsWrong = wlpCheck minindWrong 20

swap :: Program
swap = program "swap" [("a", Array IntType), ("i", int), ("j", int)] [("a'", Array IntType)] [
        assume $ (("a" !!. ref "i") ==. ref "x") /\. (("a" !!. ref "j") ==. ref "y"),
        var [("tmp", int)] [
            assignN ["tmp"] ["a" !!. ref "i"],
            Assign [ArrTarget "a" (ref "i")] ["a" !!. ref "j"],
            Assign [ArrTarget "a" (ref "j")] [ref "tmp"],
            assignN ["a'"] [ref "a"]
        ],
        assert $ (("a'" !!. ref "j") ==. ref "x") /\. (("a'" !!. ref "i") ==. ref "y")
    ]
swap' :: Program
swap' = program "swap'" [("a", Array IntType), ("i", int), ("j", int)] [("a'", Array IntType)] [
        assume $ (("a" !!. ref "i") ==. ref "x") /\. (("a" !!. ref "j") ==. ref "y"),
        Assign [ArrTarget "a" (ref "i"), ArrTarget "a" (ref "j")] ["a" !!. ref "j", "a" !!. ref "i"],
        assignN ["a'"] [ref "a"],
        assert $ (("a'" !!. ref "j") ==. ref "x") /\. (("a'" !!. ref "i") ==. ref "y")
    ]

swapWorks :: IO CheckResult
swapWorks = wlpCheck swap 10
swap'Works :: IO CheckResult
swap'Works = wlpCheck swap' 10

swapWrong :: Program
swapWrong = program "swap" [("a", Array IntType), ("i", int), ("j", int)] [("a'", Array IntType)] [
        assume $ (("a" !!. ref "i") ==. ref "x") /\. (("a" !!. ref "j") ==. ref "y"),
        var [("tmp", int)] [
            assignN ["tmp"] ["a" !!. ref "i"],
            Assign [ArrTarget "a" (ref "i")] ["a" !!. ref "j"],
            Assign [ArrTarget "a" (ref "j")] [ref "tmp"],
            assignN ["a'"] [ref "a"]
        ],
        assert $ (("a'" !!. ref "i") ==. ref "x") /\. (("a'" !!. ref "j") ==. ref "y")
    ]

swapIsWrong :: IO CheckResult
swapIsWrong = wlpCheck swapWrong 10

-- |A program that doesn't work but requires quantifiers to prove.
findNonzeroWrong :: Program
findNonzeroWrong = program "findNonzero" [("a", Array IntType)] [("i", int)] [
        assume $ neg $ forall "j" int $ ("a" !!. ref "j") ==. i 0,
        while (("a" !!. ref "i") ==. i 0) [
            var [("j", int)] [
                if_ (("a" !!. ref "j") !=. i 0) [
                    assignN ["i"] [ref "j"]
                ] []
            ]
        ],
        assert $ ("a" !!. ref "i") ==. i 0
    ]

findNonzeroIsWrong :: IO CheckResult
findNonzeroIsWrong = wlpCheck findNonzeroWrong 20

findNonzero :: Program
findNonzero = program "findNonzero" [("a", Array IntType)] [("i", int)] [
        assume $ neg $ forall "j" int $ ("a" !!. ref "j") ==. i 0,
        while (("a" !!. ref "i") ==. i 0) [
            var [("j", int)] [
                if_ (("a" !!. ref "j") !=. i 0) [
                    assignN ["i"] [ref "j"]
                ] []
            ]
        ],
        assert $ ("a" !!. ref "i") !=. i 0
    ]

findNonzeroWorks :: IO CheckResult
findNonzeroWorks = wlpCheck findNonzero 20

sort :: Program
sort = program "sort" [("a", Array IntType), ("N", int)] [("a'", Array IntType)] [
        assume $ ref "N" >=. i 0,
        var [("i", int)] [
            assignN ["i"] [i 0],
            while (ref "i" <. (ref "N" -. i 1)) [
                call ["m"] minind [ref "a", ref "i" +. i 1, ref "N"],
                if_ (("a" !!. ref "m") <. ("a" !!. ref "i")) [
                    call ["a"] swap' [ref "a", ref "i", ref "m"]
                ] []
            ]
        ],
        assignN ["a'"] [ref "a"],
        assert $ forall "i" int $ ((i 0 <=. ref "i") /\. (ref "i" <. (ref "N" -. i 1))) =>.
            (("a'" !!. ref "i") <=. ("a'" !!. (ref "i" +. i 1)))
    ]

sortWorks :: IO CheckResult
sortWorks = wlpCheck sort 20

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
            , Quantify <$> arbitraryBoundedEnum <*> arbitrary <*>
                resize (size-1) (arbitraryTyped bool)
            ]

-- |Check that prenex normalization gives predicates in prenex form
prop_prenexGivesPrenex :: Property
prop_prenexGivesPrenex = forAll (arbitraryTyped bool) $
        isPrenex . prenex
    where
    isPrenex :: Predicate -> Bool
    isPrenex (LiteralExpr _) = True
    isPrenex (NameExpr _) = True
    isPrenex (Operated _ p q) = isQuantifierFree p && isQuantifierFree q
    isPrenex (Negation p) = isQuantifierFree p
    isPrenex (Quantify _ _ p) = isPrenex p

-- |Check that normalization doesn't break predicates
prop_normalizeIsEquivalent :: Property
prop_normalizeIsEquivalent = forAll (arbitraryTyped bool) doCheck
    where
    doCheck pred = isQuantifierFree pred ==> isEquivalent pred (normalize pred)
    isEquivalent p1 p2 = testPredicate ((p1 =>. p2) /\. (p2 =>. p1))

-- |Refreshing should only refresh the given free variables
prop_refreshKeepsVars :: Property
prop_refreshKeepsVars = forAll (arbitraryTyped bool :: Gen Expression) $ (\expr ->
        freeVars expr == freeVars (refresh Set.empty Set.empty expr))

-- |Make sure the wlp after assignment of arrays is calculated correctly
prop_wlpArrayAssign :: Property
prop_wlpArrayAssign = once $ wlp' stmt q === expectedP
    where
    stmt = assignN ["x'"] [ref "x"]
    q = Index (ref "x'") (i 0) ==. i 0
    expectedP = Index (ref "x") (i 0) ==. i 0
-- |Make sure the wlp after assignment of array indices is calculated correctly
prop_wlpIndexAssign :: Property
prop_wlpIndexAssign = once $ wlp' stmt q === expectedP
    where
    stmt = Assign [ArrTarget "a" $ i 0] [ref "x"]
    q = ("a" !!. i 0) ==. i 42
    expectedP = Index (Repby (ref "a") (i 0) (ref "x")) (i 0) ==. i 42
-- |Make sure the wlp after assignment from and to array indices is calculated correctly
prop_wlpIndicesAssign :: Property
prop_wlpIndicesAssign = once $ wlp' stmt q === expectedP
    where
    stmt = Assign [ArrTarget "a" $ i 0] ["x" !!. i 1]
    q = ("a" !!. i 0) ==. i 42
    expectedP = Index (Repby (ref "a") (i 0) ("x" !!. i 1)) (i 0) ==. i 42

-- |Replacing variables inside an assignment shouldn't break array indexing
prop_replaceArrayIndex :: Property
prop_replaceArrayIndex = once $ replace stmt replacements === stmt'
    where
    stmt = Assign [ArrTarget "a" $ ref "i"] [ref "x"]
    stmt' = Assign [ArrTarget "b" $ ref "j"] [ref "y"]
    replacements = Map.fromList
        [ ("a", ref "b")
        , ("i", ref "j")
        , ("x", ref "y")
        ]

prop_unionAliases :: Property
prop_unionAliases = once $ unionAliasRange ranges aliases === expected
    where
    ranges :: RangeMap
    ranges = Map.fromList
        [ (NameTarget "x", rightInfinite (-1))
        , (NameTarget "y", leftInfinite 1)
        ]
    aliases :: AliasMap
    aliases = symmetrical (NameTarget "x") (NameTarget "y")
    expected :: RangeAliasMap
    expected = Map.fromList
        [ (NameTarget "x", Right $ NameTarget "y")
        , (NameTarget "y", Left $ bounded (-1) 1)
        ]
-- Evil QuickCheck TemplateHaskell hackery
return []
runTests = $quickCheckAll

main = do
    runTests
    putStrLn "The following programs should fail:"
    exampleProgramIsWrong
    exampleProgramInvIsWrong
    minindIsWrong
    swapIsWrong
    findNonzeroIsWrong

    putStrLn "The following programs should work:"
    exampleProgramIsFixed
    exampleProgramInvWorks
    minindWorks
    swapWorks
    swap'Works
    findNonzeroWorks
    sortWorks

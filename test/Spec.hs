{-# LANGUAGE TemplateHaskell #-}

import Lib
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
               assign ["r"] [i n]
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
            assign ["r"] [ref "x"]
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
        assign ["x", "y"] [ref "y", ref "x"]
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
        assign ["y"] [i 0 -. ref "x"],
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
            assign ["x"] [i 37]
        ],
        assign ["y"] [ref "x"]
    ]

-- |Overwriting a local variable shouldn't overwrite the other variable.
prop_localVarsWork :: Property
prop_localVarsWork = once $ p === expectedP
    where
    q = ref "y" <. i 0
    p = wlp overwriteLocalVar q
    expectedP = ref "x" <. i 0

-- Evil QuickCheck TemplateHaskell hackery
return []
main = $quickCheckAll

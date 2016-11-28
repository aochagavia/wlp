import Lib

assertEq :: (Eq a, Show a, Show e) => a -> a -> e -> IO ()
assertEq x y e
    | x == y = putStrLn "Correct"
    | otherwise = do
        putStrLn $ "Error: " ++ (show e)
        putStrLn $ "Left: " ++ (show x)
        putStrLn $ "Right: " ++ (show y)

-- |A program that does absolutely nothing
void :: Program
void = program [] [] []

testVoid :: IO ()
testVoid = do
    let q = (ref "x") =>. (ref "y")
    let p = wlp void q
    assertEq p q "testVoid"

-- |A program that always returns 42
intConst :: Program
intConst = program [] [("r", int)] [
               assign ["r"] [i 42]
           ]

testIntConst :: IO ()
testIntConst = do
    let q = (ref "r") ==. (i 42)
    let expectedP = (i 42) ==. (i 42)
    let p = wlp intConst q
    assertEq p expectedP "testIntConst"

-- |An identity program for integers
intId :: Program
intId = program [("x", int)] [("r", int)] [
            assign ["r"] [ref "x"]
        ]

testIntId :: IO ()
testIntId = do
    let q = (ref "r") ==. (ref "x")
    let expectedP = (ref "x") ==. (ref "x")
    let p = wlp intId q
    assertEq p expectedP "testIntId"

-- |A special test for bound variables
testIntConstBound :: IO ()
testIntConstBound = do
    let q = forall "r" int (ref "r" >. i 100)
    let p = wlp intId q
    assertEq p q "testIntConstBound"

main :: IO ()
main = do
    testVoid
    testIntConst
    testIntConstBound
    testIntId

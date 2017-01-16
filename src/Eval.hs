module Eval where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Syntax

-- |Cast a literal to bool.
-- Errors when the literal isn't actually a bool.
-- (This isn't a problem
literalToBool :: Literal -> Bool
literalToBool (LiteralBool b) = b
literalToBool _ = error "TypeError: can't convert non-bool to bool"

-- |Encodes the catamorphisms of a Statement
type StatementAlgebra a =
    ( a -- Skip
    , Expression -> a -- Assert
    , Expression -> a -- Assume
    , AsgTargets -> Expressions -> a -- Assign
    , a -> a -> a -- Sequence
    , Expression -> a -> a -> a -- If
    , Expression -> Expression -> a -> a -- While
    , Variables -> a -> a -- Var
    , Program -> AsgTargets -> Expressions -> a -- ProgramCall
    )
foldStatement :: StatementAlgebra a -> Statement -> a
foldStatement (skip, assert, assume, assign, sequence, if_, while, var, program) = fold' where
    fold' Skip = skip
    fold' (Assert e) = assert e
    fold' (Assume e) = assume e
    fold' (Assign ts es) = assign ts es
    fold' (Sequence s1 s2) = sequence (fold' s1) (fold' s2)
    fold' (If c t e) = if_ c (fold' t) (fold' e)
    fold' (While i c b) = while i c (fold' b)
    fold' (Var vs b) = var vs (fold' b)
    fold' (ProgramCall p ts es) = program p ts es

-- |Encodes the catamorphisms of an Expression
type ExpressionAlgebra a =
    ( Literal -> a -- LiteralExpr
    , Name -> a -- NameExpr
    , BinaryOp -> a -> a -> a -- Operated
    , a -> a -- Negation
    , a -> a -> a -- Index
    , a -> a -> a -> a -- Repby
    , Quantifier -> BoundVariable -> a -> a -- Quantify
    )

-- |Turn an algebra into a catamorphism
foldExpression :: ExpressionAlgebra a -> Expression -> a
foldExpression (literal, name, operated, negation, index, repby, quantify) = fold' where
    fold' (LiteralExpr l) = literal l
    fold' (NameExpr n) = name n
    fold' (Operated op e1 e2) = operated op (fold' e1) (fold' e2)
    fold' (Negation e) = negation (fold' e)
    fold' (Index a e) = index (fold' a) (fold' e)
    fold' (Repby a i e) = repby (fold' a) (fold' i) (fold' e)
    fold' (Quantify q n e) = quantify q n (fold' e)

-- |Evaluate the binary operation.
-- Errors if the types of the arguments are wrong.
operate :: BinaryOp -> Literal -> Literal -> Literal
operate Plus (LiteralInt n1) (LiteralInt n2) = LiteralInt $ n1 + n2
operate Minus (LiteralInt n1) (LiteralInt n2) = LiteralInt $ n1 - n2
operate Wedge (LiteralBool b1) (LiteralBool b2) = LiteralBool $ b1 && b2
operate Vee (LiteralBool b1) (LiteralBool b2) = LiteralBool $ b1 || b2
operate Implies (LiteralBool b1) (LiteralBool b2) = LiteralBool $ not b1 || b2
operate LessThan (LiteralInt n1) (LiteralInt n2) = LiteralBool $ n1 < n2
operate LessEqual (LiteralInt n1) (LiteralInt n2) = LiteralBool $ n1 <= n2
operate Equal (LiteralInt n1) (LiteralInt n2) = LiteralBool $ n1 == n2
operate op _ _ = error $ "TypeError: call to " ++ show op ++ " with wrong argument types"

-- |Given values for some of the free variables in the expression,
-- evaluate the expression to a single value, or a free variable without value.
evaluateClosed :: Expression -> Map.Map AsgTarget Literal -> Either AsgTarget Literal
evaluateClosed expr env = fold' expr where
    fold' (LiteralExpr l) = literal l
    fold' (NameExpr n) = name n
    fold' (Operated op e1 e2) = operated op (fold' e1) (fold' e2)
    fold' (Negation e) = negation (fold' e)
    fold' (Index a e) = index a (fold' e) -- Note that we do this differently!
    fold' (Quantify q n e) = quantify q n (fold' e)
    -- Look up the value for the variable, or indicate it's missing.
    tryLookup :: AsgTarget -> Either AsgTarget Literal
    tryLookup target = case Map.lookup target env of
        Just literal -> Right literal
        Nothing -> Left target
    literal l = Right l
    name n = tryLookup $ NameTarget n
    operated op e1' e2' = do
        -- Try to look up the values
        e1 <- e1'
        e2 <- e2'
        return $ operate op e1 e2
    negation :: Either AsgTarget Literal -> Either AsgTarget Literal
    negation b' = do
        b <- b'
        case b of
            LiteralBool b1 -> pure $ LiteralBool $ not $ b1
            _ -> error "TypeError: call to negation with wrong argument types"
    index :: Expression -> Either AsgTarget Literal -> Either AsgTarget Literal
    index (Repby arrExpr repExpr asgExpr) i' = do
        i <- i'
        rep <- fold' repExpr
        if i == rep
        then fold' asgExpr
        else index arrExpr i'
    index (NameExpr name) i' = do
        i <- i'
        tryLookup $ ArrTarget name $ LiteralExpr i
    quantify = error "Cannot decide predicate! Use testPredicate to remove quantifiers."

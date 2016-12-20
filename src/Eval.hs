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

-- |Encodes the catamorphisms of an Expression
type ExpressionAlgebra a =
    ( Literal -> a -- LiteralExpr
    , Name -> a -- NameExpr
    , BinaryOp -> a -> a -> a -- Operated
    , a -> a -- Negation
    , Name -> a -> a -- Index
    , BoundVariable -> a -> a -- Forall
    )

-- |Turn an algebra into a catamorphism
foldExpression :: ExpressionAlgebra a -> Expression -> a
foldExpression (literal, name, operated, negation, index, forall) = fold' where
    fold' (LiteralExpr l) = literal l
    fold' (NameExpr n) = name n
    fold' (Operated op e1 e2) = operated op (fold' e1) (fold' e2)
    fold' (Negation e) = negation (fold' e)
    fold' (Index n e) = index n (fold' e)
    fold' (Forall n e) = forall n (fold' e)

-- |Given values for all the free variables in the expression,
-- evaluate the expression to a single value.
evaluateClosed :: Expression -> Map.Map Name Literal -> Literal
evaluateClosed expr env = foldExpression closedAlgebra expr where
    closedAlgebra = (literal, name, operated, negation, index, forall)
    literal l = l
    name n = env Map.! n
    operated Plus (LiteralInt n1) (LiteralInt n2) = LiteralInt $ n1 + n2
    operated Minus (LiteralInt n1) (LiteralInt n2) = LiteralInt $ n1 - n2
    operated Wedge (LiteralBool b1) (LiteralBool b2) = LiteralBool $ b1 && b2
    operated Vee (LiteralBool b1) (LiteralBool b2) = LiteralBool $ b1 || b2
    operated Implies (LiteralBool b1) (LiteralBool b2) = LiteralBool $ not b1 || b2
    operated LessThan (LiteralInt n1) (LiteralInt n2) = LiteralBool $ n1 < n2
    operated LessEqual (LiteralInt n1) (LiteralInt n2) = LiteralBool $ n1 <= n2
    operated Equal (LiteralInt n1) (LiteralInt n2) = LiteralBool $ n1 == n2
    operated op _ _ = error $ "TypeError: call to " ++ show op ++ " with wrong argument types"
    negation (LiteralBool b1) = LiteralBool $ not b1
    negation _ = error "TypeError: call to negation with wrong argument types"
    index = undefined
    forall = undefined

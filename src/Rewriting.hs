module Rewriting where

import Syntax

import qualified Data.Map as Map
import qualified Data.Set as Set

-- |Replace the variable if it occurs in the map, keep it the same otherwise
replaceVar :: Name -> Map.Map Name Expression -> Expression
replaceVar name substs = case Map.lookup name substs of
    Just result -> result
    Nothing -> NameExpr name

-- |Replace all occurrences of given free variables by the given expressions.
-- Will also nicely handle the case of simultaneous substitutions.
replaceVars :: Expression -> Map.Map Name Expression -> Expression
replaceVars (LiteralExpr l) _ = LiteralExpr l
replaceVars (NameExpr name) substs = replaceVar name substs
replaceVars (Operated op left right) substs = Operated op left' right'
    where
    left' = replaceVars left substs
    right' = replaceVars right substs
replaceVars (Negation e) substs = Negation $ replaceVars e substs
replaceVars (Index name e) substs = Index name $ replaceVars e substs
replaceVars f@(Forall v@(Variable name _) e) substs = Forall v $ replaceVars e substs'
    where
    substs' = Map.delete name substs

-- |Replace all occurrences of given free variables by the given expressions.
-- Will also nicely handle the case of simultaneous substitutions.
replaceVarsStmt :: Statement -> Map.Map Name Expression -> Statement
replaceVarsStmt Skip _ = Skip
replaceVarsStmt (Assert expr) substs = Assert $ replaceVars expr substs
replaceVarsStmt (Assume expr) substs = Assume $ replaceVars expr substs
replaceVarsStmt (Assign vars exprs) substs = Assign replacedVars replacedExprs
    where
    replacedVars = map (flip replaceVar' substs) vars
    replaceVar' name substs = case replaceVar name substs of
        NameExpr result -> result
    replacedExprs = map (flip replaceVars substs) exprs
replaceVarsStmt (Sequence stmt1 stmt2) substs = Sequence stmt1' stmt2'
    where
    stmt1' = replaceVarsStmt stmt1 substs
    stmt2' = replaceVarsStmt stmt2 substs
replaceVarsStmt (If cond stmt1 stmt2) substs = If cond' stmt1' stmt2'
    where
    cond' = replaceVars cond substs
    stmt1' = replaceVarsStmt stmt1 substs
    stmt2' = replaceVarsStmt stmt2 substs
replaceVarsStmt (While cond stmt) substs = While cond' stmt'
    where
    cond' = replaceVars cond substs
    stmt' = replaceVarsStmt stmt substs
replaceVarsStmt (Var vars stmt) substs = Var vars $ replaceVarsStmt stmt substs'
    where
    substs' = foldr (Map.delete) substs $ map toName vars

-- |Determine all free variables of the statement
freeVarsStmt :: Statement -> Set.Set Name
freeVarsStmt Skip = Set.empty
freeVarsStmt (Assert expr) = freeVarsExpr expr
freeVarsStmt (Assume expr) = freeVarsExpr expr
freeVarsStmt (Assign vars exprs) = Set.fromList vars `Set.union` concatMapSet freeVarsExpr exprs
    where
    concatMapSet :: Ord b => (a -> Set.Set b) -> [a] -> Set.Set b
    concatMapSet f xs = foldr Set.union Set.empty $ map f xs
freeVarsStmt (Sequence stmt1 stmt2) = freeVarsStmt stmt1 `Set.union` freeVarsStmt stmt2
freeVarsStmt (If cond stmt1 stmt2) = freeVarsExpr cond `Set.union` freeVarsStmt stmt1 `Set.union` freeVarsStmt stmt2
freeVarsStmt (While cond stmt) = freeVarsExpr cond `Set.union` freeVarsStmt stmt
freeVarsStmt (Var exclude stmt) = Set.difference (freeVarsStmt stmt) (Set.fromList $ map toName exclude)

-- |Infer the type of all free variables in the expression.
-- We need to know the type the expression returns to handle the case of NameExpr.
typeInferExpr :: Type -> Expression -> Map.Map Name Type
typeInferExpr return (LiteralExpr _) = Map.empty
typeInferExpr return (NameExpr name) = Map.singleton name return
typeInferExpr (Primitive BoolType) (Negation expr) = typeInferExpr bool expr
typeInferExpr (Primitive prim) (Index name expr) = inserted
    where
    inserted = Map.insert name arrayType indexMap
    arrayType = Array prim
    indexMap = typeInferExpr int expr
typeInferExpr (Primitive BoolType) (Forall (Variable name _) expr) = deleted
    where
    deleted = name `Map.delete` typeInferExpr bool expr
typeInferExpr return (Operated op expr1 expr2) = left `Map.union` right
    where
    -- TODO: type checking!
    (expectedReturn, expectedLeft, expectedRight) = operatorType op
    left = typeInferExpr expectedLeft expr1
    right = typeInferExpr expectedRight expr2

-- |Determine all free variables of the expression.
-- This is more general than keysSet . typeInferExpr because we also accept untyped expressions.
freeVarsExpr :: Expression -> Set.Set Name
freeVarsExpr (LiteralExpr _) = Set.empty
freeVarsExpr (NameExpr name) = Set.singleton name
freeVarsExpr (Operated _ expr1 expr2) = freeVarsExpr expr1 `Set.union` freeVarsExpr expr2
freeVarsExpr (Negation expr) = freeVarsExpr expr
freeVarsExpr (Index name expr) = name `Set.insert` freeVarsExpr expr
freeVarsExpr (Forall (Variable name _) expr) = name `Set.delete` freeVarsExpr expr

-- |Replace all given variables so that they don't clash with the free variables
refresh :: [Name] -> Set.Set Name -> Statement -> Statement
refresh old exclude = flip replaceVarsStmt replacements
    where
    newVars = filter (not . (`Set.member` exclude)) ["x" ++ show n | n <- [1..]]
    replacements = Map.fromList $ zip old $ map ref newVars

{-# LANGUAGE FlexibleInstances #-}

module Rewriting where

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import Syntax

-- |Replace the variable if it occurs in the map, keep it the same otherwise
replaceVar :: Name -> Map.Map Name Expression -> Expression
replaceVar name substs = fromMaybe (NameExpr name) (Map.lookup name substs)

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
    replacedVars :: [AsgTarget]
    replacedVars = map (`replaceVar'` substs) (map toName vars)
    replaceVar' :: Name -> Map.Map Name Expression -> AsgTarget
    replaceVar' name substs = case replaceVar name substs of
        NameExpr result -> NameTarget result
    replacedExprs :: [Expression]
    replacedExprs = map (`replaceVars` substs) exprs
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
    substs' = foldr (Map.delete . toName) substs vars

-- |So the AsgTarget and Variable and Name types aren't too cumbersome.
class Bindable var where
    toName :: var -> Name

-- (since Name is an alias for String which is an alias for [Char])
instance Bindable [Char] where
    toName = id
instance Bindable Variable where
    toName (Variable name _) = name
instance Bindable AsgTarget where
    toName (NameTarget name) = name
    toName (ArrTarget name _) = name

-- |Used to filter out bound variables.
sameName :: (Bindable v, Bindable w) => v -> w -> Bool
sameName v w = toName v == toName w

-- |When we have a list of free variables, we can bind one.
-- Basically filters out the AsgTargets with the given name.
makeBound :: Bindable var => var -> Set.Set AsgTarget -> Set.Set AsgTarget
makeBound bound = Set.filter (not . sameName bound)

-- |Determine all free variables of the statement
freeVarsStmt :: Statement -> Set.Set AsgTarget
freeVarsStmt Skip = Set.empty
freeVarsStmt (Assert expr) = freeVarsExpr expr
freeVarsStmt (Assume expr) = freeVarsExpr expr
freeVarsStmt (Assign vars exprs) = Set.fromList vars `Set.union` concatMapSet freeVarsExpr exprs
    where
    -- |Equivalent to concatMap but makes a set instead of a list.
    concatMapSet :: Ord b => (a -> Set.Set b) -> [a] -> Set.Set b
    concatMapSet f = foldr (Set.union . f) Set.empty
freeVarsStmt (Sequence stmt1 stmt2) = freeVarsStmt stmt1 `Set.union` freeVarsStmt stmt2
freeVarsStmt (If cond stmt1 stmt2) = freeVarsExpr cond `Set.union` freeVarsStmt stmt1 `Set.union` freeVarsStmt stmt2
freeVarsStmt (While cond stmt) = freeVarsExpr cond `Set.union` freeVarsStmt stmt
freeVarsStmt (Var excluded stmt) = Set.filter isStillFree $ freeVarsStmt stmt
    where
    -- |Is the target declared in this scope?
    isStillFree :: AsgTarget -> Bool
    isStillFree (NameTarget name) = all (not . sameName name) excluded
    isStillFree (ArrTarget name _) = all (not . sameName name) excluded

-- |Infer the type of all free variables in the expression.
-- We need to know the type the expression returns to handle the case of NameExpr.
typeInferExpr :: Type -> Expression -> Map.Map Name Type
typeInferExpr return (LiteralExpr _) = Map.empty
typeInferExpr return (NameExpr name) = Map.singleton name return
typeInferExpr (Primitive BoolType) (Negation expr) = typeInferExpr bool expr
typeInferExpr (Primitive prim) (Index arr index) = indexMap `Map.union` arrMap
    where
    indexMap = typeInferExpr int index
    arrMap = typeInferExpr (Array prim) arr
typeInferExpr (Primitive BoolType) (Forall (Variable name _) expr) = deleted
    where
    deleted = name `Map.delete` typeInferExpr bool expr
typeInferExpr return (Operated op expr1 expr2) = left `Map.union` right
    where
    -- Note that we ignore type checking for now.
    -- (It will get checked when we (try to) evaluate the expression.)
    (expectedReturn, expectedLeft, expectedRight) = operatorType op
    left = typeInferExpr expectedLeft expr1
    right = typeInferExpr expectedRight expr2

-- |Determine all free variables of the expression.
-- This is more general than keysSet . typeInferExpr because we also accept untyped expressions.
freeVarsExpr :: Expression -> Set.Set AsgTarget
freeVarsExpr (LiteralExpr _) = Set.empty
freeVarsExpr (NameExpr name) = Set.singleton $ NameTarget name
freeVarsExpr (Operated _ expr1 expr2) = freeVarsExpr expr1 `Set.union` freeVarsExpr expr2
freeVarsExpr (Negation expr) = freeVarsExpr expr
freeVarsExpr (Index arr expr) = freeVarsExpr arr `Set.union` freeVarsExpr expr
freeVarsExpr (Forall var expr) = makeBound var $ freeVarsExpr expr

-- |Replace all given variables so that they don't clash with the free variables
refresh :: [Name] -> Set.Set Name -> Statement -> Statement
refresh old exclude = flip replaceVarsStmt replacements
    where
    newVars = filter (not . (`Set.member` exclude)) ["x" ++ show n | n <- [1..]]
    replacements = Map.fromList $ zip old $ map ref newVars

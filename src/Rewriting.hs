{-# LANGUAGE FlexibleInstances #-}

module Rewriting where

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import Syntax

-- ^Various tools to replace parts of syntax with other syntax.

-- |Represents a piece of syntax that refers to a variable.
-- So the AsgTarget and Variable and Name types aren't too cumbersome to mix.
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
-- |Do the same as makeBound for a map instead of a set.
makeBoundMap :: Bindable var => var -> Map.Map AsgTarget v -> Map.Map AsgTarget v
makeBoundMap bound = Map.filterWithKey (const . not . sameName bound)

-- |We will need to operate on the free variables quite a bit,
-- both on statements and on expressions.
-- To avoid replaceExpr, replaceStmt, etc. we made it a typeclass.
class FreeVars syntax where
    -- |Give a set of any free variables in this piece of syntax.
    freeVars :: syntax -> Set.Set AsgTarget
    -- |Replace any free variables in the map with the given expression.
    replace :: syntax -> Map.Map Name Expression -> syntax
    -- |Give new names to all the given free variables.
    -- The names will not match any of the names in the exclusion list afterward.
    refresh :: Set.Set Name -> Set.Set Name -> syntax -> syntax
    refresh toRefresh exclude expr = replace expr freeToFresh
        where
        shouldRefresh :: Name -> Bool
        shouldRefresh = anySameName toRefresh
        anySameName :: (Bindable v, Bindable w) => Set.Set w -> v -> Bool
        anySameName toMatch v = Set.fold (\w -> (|| sameName v w)) False toMatch
        oldVars = Set.map toName $ freeVars expr
        newVars = ["x" ++ show n | n <- [1..]]
        -- The bound variables to replace
        toReplace = filter shouldRefresh $ Set.toList oldVars
        -- Don't replace the variables with bound variables
        replaceWith = map ref $ filter (not . anySameName (exclude `Set.union` toRefresh)) newVars
        freeToFresh = Map.fromList $ zip toReplace replaceWith

-- |Replace the variable if it occurs in the map, keep it the same otherwise.
-- Note that this isn't an instance of Replacable since we get an Expression.
replaceVar :: Name -> Map.Map Name Expression -> Expression
replaceVar name substs = fromMaybe (NameExpr name) (Map.lookup name substs)

-- |Replace the variable if its replacement is also a variable.
-- Errors if the replacement is not a NameExpr.
-- Also substitutes in the index of an array lookup.
replaceInVar :: AsgTarget -> Map.Map Name Expression -> AsgTarget
replaceInVar (NameTarget name) substs
    = case replaceVar name substs of
        NameExpr result -> NameTarget result
replaceInVar (ArrTarget arr index) substs
    = case replaceVar arr substs of
        NameExpr result -> ArrTarget result $ replace index substs

-- |Determine all the free variables in a list of syntax items.
allFreeVars :: FreeVars syntax => [syntax] -> Set.Set AsgTarget
allFreeVars = concatMapSet freeVars
    where
    -- |Equivalent to concatMap but makes a set instead of a list.
    concatMapSet :: Ord b => (a -> Set.Set b) -> [a] -> Set.Set b
    concatMapSet f = foldr (Set.union . f) Set.empty

instance FreeVars Expression where
    freeVars (LiteralExpr _) = Set.empty
    freeVars (NameExpr name) = Set.singleton $ NameTarget name
    freeVars (Operated _ expr1 expr2) = freeVars expr1 `Set.union` freeVars expr2
    freeVars (Negation expr) = freeVars expr
    freeVars (Index arr expr) = freeVars arr `Set.union` freeVars expr
    freeVars (Repby arr index expr)
        = freeVars arr `Set.union` freeVars index `Set.union` freeVars expr
    freeVars (Quantify _ var expr) = makeBound var $ freeVars expr

    replace (LiteralExpr l) _ = LiteralExpr l
    replace (NameExpr name) substs = replaceVar name substs
    replace (Operated op left right) substs = Operated op left' right'
        where
        left' = replace left substs
        right' = replace right substs
    replace (Negation e) substs = Negation $ replace e substs
    replace (Index a i) substs = Index (replace a substs) $ replace i substs
    replace (Repby a i e) substs
        = Repby (replace a substs) (replace i substs) (replace e substs)
    replace f@(Quantify q (Variable name ty) expr) substs
        = result
        where
        result = Quantify q v $ replace e substs'
        substs' = Map.delete name substs
        -- Prevent the name from accidentally getting bound by the substitutions
        f'@(Quantify _ v e) = if name `Set.member` freeInSubsts
            then Quantify q (Variable freshName ty) freshE
            else f
        freeInSubsts = Map.keysSet substs' `Set.union`
            Set.map toName (allFreeVars $ Map.elems substs')
        freshName = head $ filter (not . (`Set.member` freeInSubsts)) ["x" ++ show n | n <- [1..]]
        freshE = replace expr (Map.singleton name (NameExpr freshName))

instance FreeVars Statement where
    -- |Determine all free variables of the statement
    freeVars Skip = Set.empty
    freeVars (Assert expr) = freeVars expr
    freeVars (Assume expr) = freeVars expr
    freeVars (Assign vars exprs) = Set.fromList vars `Set.union` allFreeVars exprs
    freeVars (Sequence stmt1 stmt2) = freeVars stmt1 `Set.union` freeVars stmt2
    freeVars (If cond stmt1 stmt2)
        = freeVars cond `Set.union` freeVars stmt1 `Set.union` freeVars stmt2
    freeVars (While Nothing cond stmt)
        = freeVars cond `Set.union` freeVars stmt
    freeVars (While (Just inv) cond stmt)
        = freeVars inv `Set.union` freeVars cond `Set.union` freeVars stmt
    freeVars (Var excluded stmt) = Set.filter isStillFree $ freeVars stmt
        where
        -- |Is the target declared in this scope?
        isStillFree :: AsgTarget -> Bool
        isStillFree (NameTarget name) = all (not . sameName name) excluded
        isStillFree (ArrTarget name _) = all (not . sameName name) excluded
    freeVars (ProgramCall prog vars args) = Set.fromList vars `Set.union` allFreeVars args

    replace Skip _ = Skip
    replace (Assert expr) substs = Assert $ replace expr substs
    replace (Assume expr) substs = Assume $ replace expr substs
    replace (Assign vars exprs) substs = Assign replacedVars replacedExprs
        where
        replacedVars = map (`replaceInVar` substs) vars
        replacedExprs = map (`replace` substs) exprs
    replace (Sequence stmt1 stmt2) substs = Sequence stmt1' stmt2'
        where
        stmt1' = replace stmt1 substs
        stmt2' = replace stmt2 substs
    replace (If cond stmt1 stmt2) substs = If cond' stmt1' stmt2'
        where
        cond' = replace cond substs
        stmt1' = replace stmt1 substs
        stmt2' = replace stmt2 substs
    replace (While inv cond stmt) substs = While inv' cond' stmt'
        where
        inv' = flip replace substs <$> inv
        cond' = replace cond substs
        stmt' = replace stmt substs
    replace (Var vars stmt) substs = Var vars $ replace stmt substs'
        where
        substs' = foldr (Map.delete . toName) substs vars
    replace (ProgramCall prog vars exprs) substs = ProgramCall prog replacedVars replacedExprs
        where
        replacedVars = map (`replaceInVar` substs) vars
        replacedExprs = map (`replace` substs) exprs

instance FreeVars Program where
    freeVars (Program _ inParams outParams code) = codeVars `Set.union` inVars `Set.union` outVars
        where
        codeVars = freeVars code
        inVars = Set.fromList $ map (NameTarget . toName) inParams
        outVars = Set.fromList $ map (NameTarget . toName) outParams
    replace (Program n inParams outParams code) substs = Program n inParams' outParams' code'
        where
        code' = replace code substs
        inParams' = map replaceVariable inParams
        outParams' = map replaceVariable outParams
        replaceVariable :: Variable -> Variable
        replaceVariable (Variable name ty) = case replaceVar name substs of
            NameExpr result -> Variable result ty

-- |Infer the type of all free variables in the expression.
-- We need to know the type the expression returns to handle the case of NameExpr.
typeInferExpr :: Type -> Expression -> Map.Map AsgTarget Type
typeInferExpr return (LiteralExpr _) = Map.empty
typeInferExpr return (NameExpr name) = Map.singleton (NameTarget name) return
typeInferExpr (Primitive BoolType) (Negation expr) = typeInferExpr bool expr
typeInferExpr (Primitive prim) (Index arr index) = result
    where
    result = Map.insert (ArrTarget (arrName arr) index) (Primitive prim) $
        indexMap `Map.union` arrMap
    indexMap = typeInferExpr int index
    -- We need to know that we want to index the array at a given point
    arrName (NameExpr name) = name
    arrName (Repby arr _ _) = arrName arr
    arrMap = typeInferExpr (Array prim) arr
typeInferExpr (Primitive BoolType) (Quantify q (Variable name _) expr) = deleted
    where
    deleted = makeBoundMap name $ typeInferExpr bool expr
typeInferExpr return (Operated op expr1 expr2) = left `Map.union` right
    where
    -- Note that we ignore type checking for now.
    -- (It will get checked when we (try to) evaluate the expression.)
    (expectedReturn, expectedLeft, expectedRight) = operatorType op
    left = typeInferExpr expectedLeft expr1
    right = typeInferExpr expectedRight expr2
typeInferExpr (Array prim) (Repby arr index expr) = result
    where
    result = arrMap `Map.union` indexMap `Map.union` exprMap
    arrMap = typeInferExpr (Array prim) arr
    indexMap = typeInferExpr int index
    exprMap = typeInferExpr (Primitive prim) expr
typeInferExpr ty expr = error $ "Type error: cannot infer " ++ show ty ++ " for " ++ show expr

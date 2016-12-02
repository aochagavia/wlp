module Lib where

import Rewriting
import Syntax
import Util

import qualified Data.Map as Map
import qualified Data.Set as Set

-- |Calculate the wlp of a program based on the given postcondition
wlp :: Program -> Expression -> Expression
wlp (Program _ _ s) q = wlp' s q -- TODO: recursion requires that we store this value somewhere

-- | Calculate the wlp of a statement based on the given postcondition
wlp' :: Statement -> Expression -> Expression
wlp' Skip q = q
-- Assignment requires simultaneously replacing all free variables in the postcondition
wlp' (Assign targets exprs) q = replaceVars q $ Map.fromList $ zip targets exprs
wlp' (Sequence stmt1 stmt2) q = wlp' stmt1 $ wlp' stmt2 q
wlp' (Assert condition) q = condition /\. q
wlp' (Assume condition) q = condition =>. q
-- Local variables get renamed so they don't clash with those in the condition
wlp' (Var vars stmt) q = wlp' (refresh names currentFree stmt) q
    where
    currentFree :: Set.Set Name
    currentFree = freeVarsStmt stmt `Set.union` freeVarsExpr q
    names :: [Name]
    names = map toName vars
wlp' stmt q = error $ "Statement " ++ show stmt ++ " has no wlp defined!"



someFunc :: IO ()
someFunc = putStrLn "someFunc"

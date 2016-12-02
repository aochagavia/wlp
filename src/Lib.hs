module Lib where

import Util

import qualified Data.Map as Map
import qualified Data.Set as Set

-- *Small syntax
-- Various smaller-scale syntax such as tokens and lists of them.

-- |We represent a variable name with a plain string.
-- (TODO: should we use another type?)
type Name = String
-- |Input and output of a 'Program'.
type Parameters = [Variable]
-- |Local variables in a 'Var' declaration.
type Variables = [Variable]
-- |Variable declaration, with 'Name' and 'Type'.
data Variable = Variable Name Type
    deriving (Eq, Ord, Show)
-- |Variable bound in a quantifier.
type BoundVariable = Variable
-- |Names of variables to be assigned to.
type AsgTargets = [AsgTarget]
-- |Name of variable to be assigned to.
type AsgTarget = Name
-- |Several expressions to be evaluated.
type Expressions = [Expression]
-- |Binary operators used in an 'Expression'.
data BinaryOp
    = Plus -- ^Add two numbers.
    | Minus -- ^Subtract two numbers.
    | Wedge -- ^Conjunction of two propositions.
    | Vee -- ^Disjunction of two propositions.
    | Implies -- ^Implication of two propositions.
    | LessThan -- ^Strict inequality of two numbers.
    | LessEqual -- ^Loose inequality of two numbers.
    | Equal -- ^Equality of two numbers.
    deriving (Eq, Ord)

instance Show BinaryOp where
    show Plus = "+"
    show Minus = "-"
    show Wedge = "/\\"
    show Vee = "\\/"
    show Implies = "=>"
    show LessThan = "<"
    show LessEqual = "<="
    show Equal = "=="

-- |The type of a variable.
data Type
    = Primitive PrimitiveType -- ^Types that can't be reduced further.
    | Array PrimitiveType -- ^An array that can be indexed to get that type.
    deriving (Eq, Ord, Show)
-- |Types that can't be reduced further.
data PrimitiveType
    = IntType -- ^Integer number.
    | BoolType -- ^Boolean proposition.
    deriving (Eq, Ord, Show)
-- |A value of a PrimitiveType
data Literal
    = LiteralInt Int
    | LiteralBool Bool
    deriving (Eq, Ord)
instance Show Literal where
    show (LiteralInt i) = show i
    show (LiteralBool b) = show b

-- *Big syntax
-- Pieces of syntax that are much more complicated structures of small syntax.

-- |Can be called, somewhat like a function in imperative languages.
data Program = Program
    { inParams :: Parameters -- ^The parameters that are passed during call.
    , outParams :: Parameters -- ^The parameters that are returned.
    , body :: Statement -- ^The code that will be called. Usually multiple statements long.
    }
    deriving (Eq, Ord, Show)

-- |A bit of code that modifies the state.
data Statement
    = Skip
        -- ^Do nothing.
    | Assert Expression
        -- ^Strengthen precondition
    | Assume Expression
        -- ^Weaken precondition
    | Assign AsgTargets Expressions
        -- ^Set variables to values
    | Sequence Statement Statement
        -- ^Perform one statement, then another.
        -- We will usually express this using a list of 'Statements',
        -- which gets passed to the other AST-building functions.
    | If Expression Statement Statement
        -- ^Conditional execution.
    | While Expression Statement
        -- ^Repeated execution.
        -- TODO: include an invariant here?
    | Var Variables Statement
        -- ^Local variable declaration
    deriving (Eq, Ord, Show)

-- |A bit of code that calculates a value.
data Expression
    = LiteralExpr Literal
        -- ^Built-in literal value.
    | NameExpr Name
        -- ^Look up a variable in the scope.
    | Operated BinaryOp Expression Expression
        -- ^Apply an operator to two expressions.
    | Negation Expression
        -- ^Negation of a proposition.
        -- TODO: this feels too hard-coded compared to 'BinaryOp'.
    | Index Name Expression
        -- ^Look up an index in an array.
    | Forall BoundVariable Expression
        -- ^Quantify a predicate over all values the variable can assume.
    deriving (Eq, Ord)

instance Show Expression where
    show (LiteralExpr l) = "(" ++ show l ++ ")"
    show (NameExpr n) = n
    show (Operated op ex1 ex2) = "(" ++ show ex1 ++ " " ++ show op ++ " " ++ show ex2 ++ ")"
    show (Negation expr) = "~(" ++ show expr ++ ")"
    show (Index var expr) = var ++ "[" ++ show expr ++ "]"
    show (Forall var expr) = "(forall " ++ show var ++ " . " ++ show expr ++ ")"

-- *Building an AST
-- The data types defined above are quite impractical, so let's make them easier to read.

-- |Make a list of 'Statement's into a single 'Statement'.
-- Folds all the 'Statement's together using 'Sequence'.
-- An empty list is interpreted as 'Skip', but no other 'Skip' is inserted.
foldSequence :: [Statement] -> Statement
foldSequence [] = Skip
foldSequence xs = foldr1 Sequence xs

-- |Convert a list of names and types to a list of 'Variable's
toVariables :: [(Name, Type)] -> [Variable]
toVariables = map makeVariable
    where
    makeVariable = uncurry Variable

-- |Define a program using a list of 'Statement's.
program :: [(Name, Type)] -> [(Name, Type)] -> [Statement] -> Program
program ins outs stmts = Program inParams outParams $ foldSequence stmts
    where
    inParams = toVariables ins
    outParams = toVariables outs

-- |A datatype-agnostic way to write the constructor.
skip :: Statement
skip = Skip
-- |A datatype-agnostic way to write the constructor.
assert, assume :: Expression -> Statement
assert = Assert
assume = Assume
-- |A datatype-agnostic way to write the constructor.
-- Does not check the number of variables versus expressions.
assign :: [Name] -> [Expression] -> Statement
assign vars exprs = Assign vars exprs
-- |A datatype-agnostic way to write the constructor.
if_ :: Expression -> [Statement] -> [Statement] -> Statement
if_ cond thens elses = If cond (foldSequence thens) (foldSequence elses)
-- |A datatype-agnostic way to write the constructor.
while :: Expression -> [Statement] -> Statement
while cond body = While cond $ foldSequence body
-- |A datatype-agnostic way to write the constructor.
var :: [(Name, Type)] -> [Statement] -> Statement
var vars stmts = Var (toVariables vars) $ foldSequence stmts

-- |An integer literal.
i :: Int -> Expression
i = LiteralExpr . LiteralInt
-- |A boolean literal.
b :: Bool -> Expression
b = LiteralExpr . LiteralBool
-- |Reference to a variable.
ref :: Name -> Expression
ref = NameExpr
-- |A binary operator.
-- Each operator is written as a Haskell equivalent followed by a `.`.
(+.), (-.), (/\.), (\/.), (=>.), (<.), (<=.), (==.), (>.), (>=.), (!=.)
    :: Expression -> Expression -> Expression
(+.) = Operated Plus
(-.) = Operated Minus
(/\.) = Operated Wedge
(\/.) = Operated Vee
(=>.) = Operated Implies
(<.) = Operated LessThan
(<=.) = Operated LessEqual
(==.) = Operated Equal
(>.) = Negation ... Operated LessEqual
(>=.) = Negation ... Operated LessThan
(!=.) = Negation ... Operated Equal
-- |A unary operator.
neg :: Expression -> Expression
neg = Negation
-- |Array indexing.
(!!.) :: Name -> Expression -> Expression
(!!.) = Index
-- |A quantifier.
forall, exists :: Name -> Type -> Expression -> Expression
forall = Forall ... Variable
exists name ty = neg . forall name ty . neg

-- |One of the possible types.
int, bool, ints, bools :: Type
int = Primitive IntType
bool = Primitive BoolType
ints = Array IntType
bools = Array BoolType

-- |Remove type specifier from variable declaration.
toName :: Variable -> Name
toName (Variable name _) = name

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

-- |Determine all free variables of the expression
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

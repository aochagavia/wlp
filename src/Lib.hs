module Lib where

import Util

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
    deriving (Eq, Ord, Show)
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
    deriving (Eq, Ord, Show)

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
    deriving (Eq, Ord, Show)

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

-- |Replace all occurrences of a free variable by the given expression
replaceVar :: Expression -> (Name, Expression) -> Expression
replaceVar q (n, expr) = r q
    where r :: Expression -> Expression
          r (LiteralExpr l) = LiteralExpr l
          r (NameExpr name) = if name == n then expr else NameExpr name
          r (Operated op left right) = Operated op (r left) (r right)
          r (Negation e) = Negation (r e)
          r (Index name e) = Index name (r e)
          r f@(Forall v@(Variable name _) e) = if name == n then f else Forall v (r e)

-- |Calculate the wlp of a program based on the given postcondition
wlp :: Program -> Expression -> Expression
wlp (Program _ _ s) q = wlp' s q -- TODO: recursion requires that we store this value somewhere

-- | Calculate the wlp of a statement based on the given postcondition
wlp' :: Statement -> Expression -> Expression
wlp' Skip q = q
-- Assignment requires simultaneously replacing all free variables in the postcondition
wlp' (Assign targets exprs) q = foldr (flip replaceVar) q (zip targets exprs)


someFunc :: IO ()
someFunc = putStrLn "someFunc"

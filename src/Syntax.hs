module Syntax where

import Range
import Util

-- *Small syntax
-- Various smaller-scale syntax such as tokens and lists of them.

-- |We represent a variable name with a plain string.
type Name = String
-- |Input and output of a 'Program'.
type Parameters = [Variable]
-- |Local variables in a 'Var' declaration.
type Variables = [Variable]
-- |Variable declaration, with 'Name' and 'Type'.
data Variable = Variable Name Type
    deriving (Eq, Ord)

instance Show Variable where
    show (Variable n t) = n ++ " : " ++ show t

-- |Variable bound in a quantifier.
type BoundVariable = Variable
-- |Names of variables to be assigned to.
type AsgTargets = [AsgTarget]
-- |Variable to be assigned to, or as C calls it, an lvalue.
-- Can also be an array with index.
data AsgTarget
    = NameTarget Name
    | ArrTarget Name Expression
    deriving (Eq, Ord)

instance Show AsgTarget where
    show (NameTarget n) = n
    show (ArrTarget n expr) = n ++ "[" ++ show expr ++ "]"

-- |Is this a 'NameTarget' instead of an 'ArrTarget'?
isNameTarget :: AsgTarget -> Bool
isNameTarget (NameTarget _) = True
isNameTarget _ = False

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
    deriving (Eq, Ord, Enum, Bounded)

instance Show BinaryOp where
    show Plus = "+"
    show Minus = "-"
    show Wedge = "/\\"
    show Vee = "\\/"
    show Implies = "=>"
    show LessThan = "<"
    show LessEqual = "<="
    show Equal = "=="

-- |A quantifier, used to express predicates.
data Quantifier
    = ForAll
    | Exists
    deriving (Eq, Ord, Enum, Bounded)

instance Show Quantifier where
    show ForAll = "!A"
    show Exists = "?E"

-- |The type of a variable.
data Type
    = Primitive PrimitiveType -- ^Types that can't be reduced further.
    | Array PrimitiveType -- ^An array that can be indexed to get that type.
    deriving (Eq, Ord)

instance Show Type where
    show (Primitive ty) = show ty
    show (Array ty) = "[" ++ show ty ++ "]"

-- |Types that can't be reduced further.
data PrimitiveType
    = IntType -- ^Integer number.
    | BoolType -- ^Boolean proposition.
    deriving (Eq, Ord, Bounded, Enum)
instance Show PrimitiveType where
    show IntType = "int"
    show BoolType = "bool"

-- |A value of a PrimitiveType
data Literal
    = LiteralInt Int
    | LiteralBool Bool
    | LiteralArray Range
    deriving (Eq, Ord)
instance Show Literal where
    show (LiteralInt i) = show i
    show (LiteralBool b) = show b
    show (LiteralArray r) = "[" ++ show r ++ "]"

-- *Big syntax
-- Pieces of syntax that are much more complicated structures of small syntax.

-- |Can be called, somewhat like a function in imperative languages.
data Program = Program
    { name :: Name -- ^The program's name, used for pretty-printing.
    , inParams :: Parameters -- ^The parameters that are passed during call.
    , outParams :: Parameters -- ^The parameters that are returned.
    , body :: Statement -- ^The code that will be called. Usually multiple statements long.
    }
    deriving (Eq, Ord)

instance Show Program where
    show (Program name inParams outParams body)
        = "def " ++ name ++ " " ++ show inParams ++ " " ++ show outParams
            ++ block 0 body

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
        -- We support simultaneous assignment except the following cases:
        -- * assignment to the same lvalue is sequenced in an arbitrary way
        -- * assignment to a lvalue and to a subscript of this lvalue are
        --    sequenced in an arbitrary way
    | Sequence Statement Statement
        -- ^Perform one statement, then another.
        -- We will usually express this using a list of 'Statements',
        -- which gets passed to the other AST-building functions.
    | If Expression Statement Statement
        -- ^Conditional execution.
    | While (Maybe Expression) Expression Statement
        -- ^Repeated execution.
        -- Note: the first expression is an optional invariant.
    | Var Variables Statement
        -- ^Local variable declaration
    | ProgramCall Program AsgTargets Expressions
        -- ^Call a program with a given list of arguments and store the results
    deriving (Eq, Ord)

-- |Indent the string with a given number of tabs.
-- Used for formatting statements.
indentation :: Int -> String
indentation = flip replicate '\t'

-- |Start a block at the given indentation level.
-- Note that the block opening brace is not on a new line.
block :: Int -> Statement -> String
block n stmt = " {\n" ++ indent (n+1) stmt ++ "\n" ++ indentation n ++ "}"

-- |Nicely format a statement at a given indentation level.
indent :: Int -> Statement -> String
indent n Skip = indentation n ++ "skip"
indent n (Assert expr) = indentation n ++ "assert " ++ show expr
indent n (Assume expr) = indentation n ++ "assume " ++ show expr
indent n (Assign ts es) = indentation n ++ show ts ++ " = " ++ show es
indent n (Sequence s1 s2) = indent n s1 ++ ";\n" ++ indent n s2
indent n (If c t e) = indentation n ++ "if " ++ show c ++ block n t ++ " else" ++ block n e
indent n (While Nothing c b)
    = indentation n ++ "while " ++ show c ++ block n b
indent n (While (Just i) c b)
    = indentation n ++ "while [" ++ show i ++ "] " ++ show c ++ block n b
indent n (Var vs b) = indentation n ++ "var " ++ show vs ++ block n b
indent n (ProgramCall p ts es) = indentation n ++ show ts ++ " = " ++ name p ++ " " ++ show es

instance Show Statement where
    show = indent 0

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
    | Index Expression Expression
        -- ^Look up an index in an array.
    | Quantify Quantifier BoundVariable Expression
        -- ^Quantify a predicate over all values the variable can assume.
    | Repby Expression Expression Expression
        -- ^Used for translating array assignments.
        -- Replace the value in `array` at index `index` with `expression`.
        -- You shouldn't write this expression in an actual program!
    deriving (Eq, Ord)

-- |Optionally surround the string in parentheses.
parentheses :: Bool -> String -> String
parentheses False str = str
parentheses True str = "(" ++ str ++ ")"

-- |Make a string representation of the expression, with optional parentheses.
pretty :: Bool -> Expression -> String
pretty _ (LiteralExpr l) = show l
pretty _ (NameExpr n) = n
pretty b (Operated op ex1 ex2) = parentheses b $
    pretty True ex1 ++ " " ++ show op ++ " " ++ pretty True ex2
pretty _ (Negation expr) = "~" ++ pretty True expr
pretty _ (Index arr expr) = pretty True arr ++ "[" ++ pretty False expr ++ "]"
pretty _ (Repby arr index expr)
    = pretty True arr ++ "[" ++ pretty False index ++ "<-" ++ pretty False expr ++ "]"
pretty _ (Quantify q var expr)
    = show q ++ " " ++ show var ++ " . " ++ pretty True expr

instance Show Expression where
    show = pretty False

-- *Building an AST
-- The data types defined above are quite impractical, so let's make them easier to read.

-- |Make a list of 'Statement's into a single 'Statement'.
-- Folds all the 'Statement's together using 'Sequence'.
-- An empty list is interpreted as 'Skip', but no other 'Skip' is inserted.
foldSequence :: [Statement] -> Statement
foldSequence [] = Skip
foldSequence xs = foldr1 Sequence xs

-- |Make a single 'Statement' into a list of 'Statement's.
-- Is not exactly the inverse of 'foldSequence' since 'Skip' will result in '[Skip]'.
unSequence :: Statement -> [Statement]
unSequence (Sequence s1 s2) = unSequence s1 ++ unSequence s2
unSequence stmt = [stmt]

-- |Convert a list of names and types to a list of 'Variable's
toVariables :: [(Name, Type)] -> [Variable]
toVariables = map makeVariable
    where
    makeVariable = uncurry Variable

-- |Define a program using a list of 'Statement's.
program :: Name -> [(Name, Type)] -> [(Name, Type)] -> [Statement] -> Program
program name ins outs stmts = Program name inParams outParams $ foldSequence stmts
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
assignN :: [Name] -> [Expression] -> Statement
assignN = Assign . map NameTarget
-- |A datatype-agnostic way to write the constructor.
if_ :: Expression -> [Statement] -> [Statement] -> Statement
if_ cond thens elses = If cond (foldSequence thens) (foldSequence elses)
-- |A datatype-agnostic way to write the constructor.
while :: Expression -> [Statement] -> Statement
while cond body = While Nothing cond $ foldSequence body
-- |A datatype-agnostic way to write the constructor.
var :: [(Name, Type)] -> [Statement] -> Statement
var vars stmts = Var (toVariables vars) $ foldSequence stmts
-- |Call a program with a set of arguments.
call :: [Name] -> Program -> [Expression] -> Statement
call names program = ProgramCall program $ map NameTarget names

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
e1 >. e2 = Operated LessThan e2 e1
e1 >=. e2 = Operated LessEqual e2 e1
(!=.) = Negation ... Operated Equal
-- |A unary operator.
neg :: Expression -> Expression
neg = Negation
-- |Array indexing.
(!!.) :: Name -> Expression -> Expression
(!!.) = Index . ref
-- |A quantifier.
forall, exists :: Name -> Type -> Expression -> Expression
forall = Quantify ForAll ... Variable
exists = Quantify Exists ... Variable

-- |One of the possible types.
int, bool, ints, bools :: Type
int = Primitive IntType
bool = Primitive BoolType
ints = Array IntType
bools = Array BoolType

-- |Get the return type and argument types to the operator, for type checking.
operatorType :: BinaryOp -> (Type, Type, Type)
operatorType Plus = (int, int, int)
operatorType Minus = (int, int, int)
operatorType Wedge = (bool, bool, bool)
operatorType Vee = (bool, bool, bool)
operatorType Implies = (bool, bool, bool)
operatorType LessThan = (bool, int, int)
operatorType LessEqual = (bool, int, int)
operatorType Equal = (bool, int, int)

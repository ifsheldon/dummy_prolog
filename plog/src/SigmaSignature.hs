module SigmaSignature
  ( Constant (..),
    Variable (..),
    Term (..),
    Function (..),
    Relation (..),
    Formula (..),
    Quantifier (..),
    validateFormula,
    validateTerm,
    validateTerms,
    varTermFromName,
    forallVarFormula,
    existVarFormula,
  )
where

data Constant = A | B | C | D | E | F deriving (Show) -- predefined constant symbols

data Variable = Variable {name_v :: [Char]}
instance Show Variable where
  show (Variable name) = "Var_"++name

data Term = ConstTerm Constant | VarTerm Variable | FuncTerm Function [Term]
instance Show Term where
  show t = case t of 
    ConstTerm const -> show const
    VarTerm var -> show var
    FuncTerm f terms -> show f ++"("++show terms++")"

data Function = Function {name_f :: [Char], arity_f :: Int}
instance Show Function where
  show (Function name _arity) = "Function_"++ name

data Relation = Relation {name_r :: [Char], arity_r :: Int}
instance Show Relation where 
  show (Relation name _arity) = "Relation_"++ name

data Quantifier = EXIST | FORALL deriving (Show)

data Formula
  = AtomicFormula Relation [Term]
  | NOT Formula
  | AND Formula Formula
  | OR Formula Formula
  | IMPLY Formula Formula
  | EQUIV Formula Formula
  | QFormula Quantifier Variable Formula --NOTICE: need to construct variables first, and reuse variables

instance Show Formula where
  show formula = case formula of 
    AtomicFormula relation terms -> "Atomic("++ show relation ++ show terms ++ ")"
    NOT f -> "NOT (" ++ show f ++ ")"
    AND f1 f2 -> "AND (" ++ show f1 ++") ("++ show f2 ++ ")"
    OR f1 f2 -> "OR (" ++ show f1 ++") ("++ show f2 ++ ")"
    IMPLY f1 f2 -> "IMPLY (" ++ show f1 ++") ("++ show f2 ++ ")"
    EQUIV f1 f2 -> "EQUIV (" ++ show f1 ++") ("++ show f2 ++ ")"
    QFormula quantifier var f -> show quantifier ++ " {"++ show var ++"} ("++ show f ++ ")"

validateTerm :: Term -> Bool
validateTerm term = case term of
  ConstTerm const -> True
  VarTerm var -> True
  FuncTerm function terms ->
    let functionArity = arity_f function
        arityMatch = length terms == functionArity
     in arityMatch && _validateTerms True terms

_validateTerms :: Bool -> [Term] -> Bool
_validateTerms isValidUntilNow terms =
  if isValidUntilNow
    then let (t : ts) = terms in _validateTerms (validateTerm t) ts
    else False

validateTerms :: [Term] -> Bool
validateTerms = _validateTerms True

validateFormula :: Formula -> Bool
validateFormula formula = case formula of
  AtomicFormula relation terms ->
    let relationArity = arity_r relation
        arityMatch = length terms == relationArity
     in arityMatch && validateTerms terms
  QFormula quantifier var f -> validateFormula f
  NOT f -> validateFormula f
  a `AND` b -> validateFormula a && validateFormula b
  a `OR` b -> validateFormula a && validateFormula b
  a `IMPLY` b -> validateFormula a && validateFormula b
  a `EQUIV` b -> validateFormula a && validateFormula b

------------helper functions
varTermFromName :: [Char] -> Term
varTermFromName = VarTerm . Variable

forallVarFormula :: Variable -> Formula -> Formula
forallVarFormula = QFormula FORALL

existVarFormula :: Variable -> Formula -> Formula
existVarFormula = QFormula EXIST

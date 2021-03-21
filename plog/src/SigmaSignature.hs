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

data Variable = Variable {name_v :: [Char]} deriving (Show) -- [Char] for variable name

data Term = ConstTerm Constant | VarTerm Variable | FuncTerm Function [Term] deriving (Show)

data Function = Function {name_f :: [Char], arity_f :: Int} deriving (Show)

data Relation = Relation {name_r :: [Char], arity_r :: Int} deriving (Show) -- [Char] for relation name, Int for arity

data Quantifier = EXIST | FORALL deriving (Show)

data Formula
  = AtomicFormula Relation [Term]
  | NOT Formula
  | AND Formula Formula
  | OR Formula Formula
  | IMPLY Formula Formula
  | EQUIV Formula Formula
  | QFormula Quantifier Variable Formula --NOTICE: need to construct variables first, and reuse variables
  deriving (Show)

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
varTermFromName name = VarTerm (Variable name)

forallVarFormula :: Variable -> Formula -> Formula
forallVarFormula = QFormula FORALL

existVarFormula :: Variable -> Formula -> Formula
existVarFormula = QFormula EXIST

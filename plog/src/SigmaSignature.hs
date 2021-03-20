module SigmaSignature
  ( Constant (..),
    Variable (..),
    Term (..),
    Function(..),
    Relation(..),
    Formula (..),
    Quantifier (..),
    validateFormula,
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
  | AND Formula  Formula
  | OR Formula  Formula
  | IMPLY Formula Formula
  | EQUIV Formula Formula
  | QFormula Quantifier Variable Formula --NOTICE: need to construct variables first, and reuse variables
  deriving (Show)

validateFormula :: Formula -> Bool
validateFormula formula = case formula of
  QFormula EXIST var f -> True -- TODO
  QFormula FORALL var f -> True -- TODO
  NOT f -> validateFormula f
  a `AND` b -> validateFormula a && validateFormula b
  a `OR` b -> validateFormula a && validateFormula b
  a `IMPLY` b -> validateFormula a && validateFormula b
  a `EQUIV` b -> validateFormula a && validateFormula b
  _ -> True

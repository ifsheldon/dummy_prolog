module SigmaSignature
  ( Constant,
    Variable,
    Term,
    Function,
    Relation,
    Formula,
    validateFormula,
  )
where

data Constant = A | B | C | D | E | F deriving (Show) -- predefined constant symbols

data Variable = Variable [Char] deriving (Show) -- [Char] for variable name

data Term = ConstTerm Constant | VarTerm Variable deriving (Show)

data Function = Function ([Term] -> Term)

data Relation = Relation [Char] Int deriving (Show) -- [Char] for relation name, Int for arity

data Formula
  = AtomicFormula Relation [Term]
  | NOT Formula
  | Formula `AND` Formula
  | Formula `OR` Formula
  | Formula `IMPLY` Formula
  | Formula `EQUIV` Formula
  | FORALL Variable Formula --TODO: need to check this, according to definition Var should be free in Formula
  | EXIST Variable Formula --TODO: need to check this
  deriving (Show)

validateFormula :: Formula -> Bool
validateFormula formula = case formula of
  FORALL var f -> True -- TODO
  EXIST var f -> True -- TODO
  NOT f -> validateFormula f
  a `AND` b -> validateFormula a && validateFormula b
  a `OR` b -> validateFormula a && validateFormula b
  a `IMPLY` b -> validateFormula a && validateFormula b
  a `EQUIV` b -> validateFormula a && validateFormula b
  _ -> True

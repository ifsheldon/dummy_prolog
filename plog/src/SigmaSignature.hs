module SigmaSignature
  ( Constant,
    Variable,
    Term,
    Function,
    Relation,
    Formula,
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
  | Formula `EQUI` Formula
  | FORALL Variable Formula --TODO: need to check this, according to definition Var should be free in Formula
  | EXIST Variable Formula --TODO: need to check this
  deriving (Show)
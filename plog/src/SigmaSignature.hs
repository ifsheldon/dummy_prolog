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
    var,
    forall,
    exist,
  )
where

import Data.Hashable

data Constant = A | B | C | D | E | F | ExistConst [Char] deriving (Show, Eq) -- predefined constant symbols

instance Hashable Constant where
  hashWithSalt salt const = hashWithSalt salt (show const)

data Variable = Variable {name_v :: [Char]} deriving (Eq)

instance Show Variable where
  show (Variable name) = "Var_" ++ name

instance Hashable Variable where
  hashWithSalt salt var = hashWithSalt salt (show var)

data Term = ConstTerm Constant | VarTerm Variable | FuncTerm Function [Term] deriving (Eq)

instance Hashable Term where
  hashWithSalt salt term = hashWithSalt salt (show term)

instance Show Term where
  show t = case t of
    ConstTerm const -> show const
    VarTerm var -> show var
    FuncTerm f terms -> show f ++ "(" ++ show terms ++ ")"

data Function = Function {name_f :: [Char], arity_f :: Int} deriving (Eq)

instance Hashable Function where
  hashWithSalt salt function = hashWithSalt salt (show function)

instance Show Function where
  show (Function name _arity) = "Function_" ++ name

data Relation = Relation {name_r :: [Char], arity_r :: Int} deriving (Eq)

instance Hashable Relation where
  hashWithSalt salt relation = hashWithSalt salt (show relation)

instance Show Relation where
  show (Relation name _arity) = "Relation_" ++ name

data Quantifier = EXIST | FORALL deriving (Show, Eq)

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
    AtomicFormula relation terms -> "Atomic(" ++ show relation ++ show terms ++ ")"
    NOT f -> "NOT (" ++ show f ++ ")"
    AND f1 f2 -> "AND (" ++ show f1 ++ ") (" ++ show f2 ++ ")"
    OR f1 f2 -> "OR (" ++ show f1 ++ ") (" ++ show f2 ++ ")"
    IMPLY f1 f2 -> "IMPLY (" ++ show f1 ++ ") (" ++ show f2 ++ ")"
    EQUIV f1 f2 -> "EQUIV (" ++ show f1 ++ ") (" ++ show f2 ++ ")"
    QFormula quantifier var f -> show quantifier ++ " {" ++ show var ++ "} (" ++ show f ++ ")"

instance Eq Formula where -- added place equality invariance compared to derived Eq
  f1 == f2 = case (f1, f2) of
    (AtomicFormula r1 terms1, AtomicFormula r2 terms2) -> r1 == r2 && terms1 == terms2
    (NOT sf1, NOT sf2) -> sf1 == sf2
    (AND sf11 sf12, AND sf21 sf22) -> (sf11 == sf21 && sf12 == sf22) || (sf11 == sf22 && sf12 == sf21)
    (OR sf11 sf12, OR sf21 sf22) -> (sf11 == sf21 && sf12 == sf22) || (sf11 == sf22 && sf12 == sf21)
    (EQUIV sf11 sf12, EQUIV sf21 sf22) -> (sf11 == sf21 && sf12 == sf22) || (sf11 == sf22 && sf12 == sf21)
    (IMPLY sf11 sf12, IMPLY sf21 sf22) -> sf11 == sf21 && sf12 == sf22
    (QFormula q1 v1 f1, QFormula q2 v2 f2) -> q1 == q2 && v1 == v2 && f1 == f2 --restricted version
    _ -> False

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
var :: [Char] -> Term
var = VarTerm . Variable

forall :: Variable -> Formula -> Formula
forall = QFormula FORALL

exist :: Variable -> Formula -> Formula
exist = QFormula EXIST

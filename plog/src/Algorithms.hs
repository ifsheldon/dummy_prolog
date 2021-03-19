module Algorithms
  ( stripArrows,
    negateFormula,
  )
where

import SigmaSignature

stripDoubleNot :: Formula -> Formula
stripDoubleNot formula = case formula of
  NOT (NOT f) -> stripDoubleNot f
  QFormula quantifier var f -> QFormula quantifier var (stripDoubleNot f)
  _ -> formula

negateFormula :: Formula -> Formula --finished CNF 2.
-- negateFormula formula = stripDoubleNot (NOT formula)
negateFormula formula = case formula of 
  NOT subformula -> stripDoubleNot(subformula)
  st1 `OR` st2 -> stripDoubleNot(negateFormula st1 `AND` negateFormula st2)
  st1 `AND` st2 -> stripDoubleNot(negateFormula st1 `OR` negateFormula st2)
  st1 `IMPLY` st2 -> stripDoubleNot(negateFormula (stripArrows (st1 `IMPLY` st2)))
  st1 `EQUIV` st2 -> stripDoubleNot(negateFormula (stripArrows (st1 `EQUIV` st2)))
  QFormula FORALL var f -> QFormula EXIST var (stripDoubleNot(negateFormula f))
  QFormula EXIST var f -> QFormula FORALL var (stripDoubleNot(negateFormula f))
  _ -> stripDoubleNot (NOT formula)


stripArrows :: Formula -> Formula -- finished CNF 1.
stripArrows formula = case formula of
  f0 `IMPLY` f1 -> negateFormula (stripArrows f0) `OR` stripArrows f1
  f0 `EQUIV` f1 -> (negateFormula sf0 `OR` sf1) `AND` (negateFormula sf1 `OR` sf0)
    where
      sf0 = stripArrows f0
      sf1 = stripArrows f1
  NOT f -> negateFormula (stripArrows f)
  st1 `AND` st2 -> stripArrows st1 `AND` stripArrows st2
  st1 `OR` st2 -> stripArrows st1 `AND` stripArrows st2
  QFormula quantifier var f -> QFormula quantifier var (stripArrows f)
  _ -> formula

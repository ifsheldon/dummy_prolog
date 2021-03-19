module Algorithms
  ( stripArrows,
    negateFormula,
  )
where

import SigmaSignature

stripDoubleNot :: Formula -> Formula
stripDoubleNot formula = case formula of
  NOT (NOT f) -> stripDoubleNot f
  _ -> formula

negateFormula :: Formula -> Formula
negateFormula formula = stripDoubleNot (NOT formula)

stripArrows :: Formula -> Formula
stripArrows formula = case formula of
  f0 `IMPLY` f1 -> negateFormula (stripArrows f0) `OR` stripArrows f1
  f0 `EQUIV` f1 -> (negateFormula sf0 `OR` sf1) `AND` (negateFormula sf1 `OR` sf0)
    where
      sf0 = stripArrows f0
      sf1 = stripArrows f1
  _ -> formula -- TODO

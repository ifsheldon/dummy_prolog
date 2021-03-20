module Algorithms
  ( stripArrows,
    negateFormula,
  )
where

import SigmaSignature
import Data.HashMap.Strict as HashMap
import Data.Maybe
------------------ This part is for CNF conversion
------------------
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

replaceTerm :: HashMap [Char] [Char] -> Term -> Term
replaceTerm mappings term = case term of 
  ConstTerm const -> term
  VarTerm (Variable varName) -> 
    if varName `member` mappings then
      let mappedName = fromJust (varName `HashMap.lookup` mappings)
        in VarTerm (Variable mappedName)
    else
      term

replaceVarNameInTerms :: HashMap [Char] [Char] -> [Term] -> [Term]
replaceVarNameInTerms nameMappings = Prelude.map (replaceTerm nameMappings)

checkVarNameAndUpdate :: ([Char], HashMap [Char] [Char], Int) -> ([Char], HashMap [Char] [Char], Int)
checkVarNameAndUpdate (oldVarName, nameMappings, usedNameCount) = 
  if oldVarName `member` nameMappings then
    let newName = "v" ++ show usedNameCount
        newMappings = insert oldVarName newName nameMappings
    in
      (newName, newMappings, usedNameCount + 1)
  else
    let newMapping = insert oldVarName oldVarName nameMappings
    in
      (oldVarName, newMapping, usedNameCount + 1)


standardize :: (Formula, HashMap [Char] [Char], Int) -> (Formula, HashMap [Char] [Char], Int )
standardize (formula, nameMappings, usedNameCount) = case formula of 
  AtomicFormula relation terms -> (AtomicFormula relation (replaceVarNameInTerms nameMappings terms), nameMappings, usedNameCount)
  NOT subformula -> standardize (subformula, nameMappings, usedNameCount)
  AND sf0 sf1 -> (AND newsf0 newsf1, nameMappingsAfterStandardizeSf1, usedNameCountAfterStardardizeSf1) where
    (newsf0, nameMappingsAfterStandardizeSf0, usedNameCountAfterStardardizeSf0) = standardize (sf0, nameMappings, usedNameCount)
    (newsf1, nameMappingsAfterStandardizeSf1, usedNameCountAfterStardardizeSf1) = standardize (sf1, nameMappingsAfterStandardizeSf0, usedNameCountAfterStardardizeSf0)
  OR sf0 sf1 -> (OR newsf0 newsf1, nameMappingsAfterStandardizeSf1, usedNameCountAfterStardardizeSf1) where
    (newsf0, nameMappingsAfterStandardizeSf0, usedNameCountAfterStardardizeSf0) = standardize (sf0, nameMappings, usedNameCount)
    (newsf1, nameMappingsAfterStandardizeSf1, usedNameCountAfterStardardizeSf1) = standardize (sf1, nameMappingsAfterStandardizeSf0, usedNameCountAfterStardardizeSf0)
  QFormula quantifier (Variable varName) subformula -> (newQformula, newMapping, newCount) where
    (newVarName, mappingAfterEvaluateVarName, countAfterEvaluateVarName) = checkVarNameAndUpdate (varName, nameMappings, usedNameCount)
    (newSubFormula, newMapping, newCount) = standardize (subformula, mappingAfterEvaluateVarName, countAfterEvaluateVarName)
    newQformula = QFormula quantifier (Variable newVarName) newSubFormula
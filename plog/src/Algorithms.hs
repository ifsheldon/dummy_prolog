module Algorithms
  ( stripArrows,
    negateFormula,
    standardize,
    VarRecord(..),
    emptyVarRecord
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
negateFormula formula = 
  stripDoubleNot intermediate where
    intermediate = case formula of 
      NOT subformula -> subformula
      st1 `OR` st2 -> negateFormula st1 `AND` negateFormula st2
      st1 `AND` st2 -> negateFormula st1 `OR` negateFormula st2
      st1 `IMPLY` st2 -> negateFormula (stripArrows (st1 `IMPLY` st2))
      st1 `EQUIV` st2 -> negateFormula (stripArrows (st1 `EQUIV` st2))
      QFormula FORALL var f -> QFormula EXIST var (negateFormula f)
      QFormula EXIST var f -> QFormula FORALL var (negateFormula f)
      _ -> NOT formula


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

data VarRecord = VarRecord {nameMappings :: HashMap [Char] [Char], 
                            variableTrack :: [[Char]],
                            variableCount :: Int } deriving (Show)

emptyVarRecord :: VarRecord
emptyVarRecord = VarRecord {nameMappings=empty, variableTrack=[], variableCount=0}

replaceTerm :: VarRecord -> Term -> (VarRecord, Term)
replaceTerm varRecord term = case term of
  ConstTerm const -> (varRecord,term)
  VarTerm (Variable varName) -> 
    let mappings = nameMappings varRecord
        varTrack = variableTrack varRecord
        varCount = variableCount varRecord
        bounded = varName `elem` varTrack
        nameUsed = varName `member` mappings
    in
      if nameUsed && bounded then
        let mappedName = fromJust (varName `HashMap.lookup` mappings)
          in (varRecord, VarTerm (Variable mappedName))
      else if nameUsed && not bounded then
        let newName = "#v" ++ show varCount
            newTerm = VarTerm (Variable newName)
            newMapping = insert newName newName mappings
            newCount = varCount + 1
        in 
          (VarRecord newMapping varTrack newCount, newTerm)
      else if bounded then -- not used but bounded, should not happen
        (varRecord, VarTerm (Variable "#?"))
      else --unused and unbounded, no need to change var name
        (varRecord, term)

replaceVarNameInTerms :: (VarRecord, [Term]) -> (VarRecord, [Term]) -- TODO: fix this
replaceVarNameInTerms (varRecord, terms) = case terms of
  [] -> (varRecord, terms)
  (t:ts) -> 
    let (record, newTerm) = replaceTerm varRecord t 
        (newRecord, newTerms) = replaceVarNameInTerms (record, ts)
    in
      (newRecord, newTerm : newTerms)

checkVarNameAndUpdate :: ([Char], VarRecord) -> ([Char], VarRecord)
checkVarNameAndUpdate (oldVarName, varRecord) = 
  let varTrack = variableTrack varRecord
      varCount = variableCount varRecord
      usedNameMappings = nameMappings varRecord
  in 
    if oldVarName `member` usedNameMappings then
      let newName = "#v" ++ show varCount
          newMappings = insert oldVarName newName usedNameMappings
      in
        (newName, VarRecord newMappings varTrack (varCount + 1))
    else
      let newMappings = insert oldVarName oldVarName usedNameMappings
      in
        (oldVarName, VarRecord newMappings varTrack (varCount + 1))


standardize :: (Formula, VarRecord) -> (Formula, VarRecord)
standardize (formula, varRecord) = let varTrack = variableTrack varRecord in
  case formula of 
    AtomicFormula relation terms -> 
      let (newRecord, newTerms) = replaceVarNameInTerms (varRecord, terms)
          newFormula = AtomicFormula relation newTerms
      in (newFormula, newRecord)
    NOT subformula -> let (sbf, record) = standardize (subformula, varRecord) 
                          newRecord = VarRecord (nameMappings record) varTrack (variableCount record)
                      in (negateFormula sbf, newRecord)
    AND sf0 sf1 -> (AND newsf0 newsf1, newRecord) where
      (newsf0, newRecordAfterStandardizeSf0) = standardize (sf0, varRecord)
      (newsf1, newRecordAfterStandardizeSf1) = standardize (sf1, newRecordAfterStandardizeSf0)
      newRecord = VarRecord (nameMappings newRecordAfterStandardizeSf1) varTrack (variableCount newRecordAfterStandardizeSf1)
    OR sf0 sf1 -> (OR newsf0 newsf1, newRecord) where
      (newsf0, newRecordAfterStandardizeSf0) = standardize (sf0, varRecord)
      (newsf1, newRecordAfterStandardizeSf1) = standardize (sf1, newRecordAfterStandardizeSf0)
      newRecord = VarRecord (nameMappings newRecordAfterStandardizeSf1) varTrack (variableCount newRecordAfterStandardizeSf1)
    QFormula quantifier (Variable varName) subformula -> (newQformula, newRecord) where
      (newVarName, record) = checkVarNameAndUpdate (varName, varRecord)
      intermediateRecord = VarRecord (nameMappings record) (varName : varTrack) (variableCount record)
      (newSubFormula, newRecord) = standardize (subformula, intermediateRecord)
      newQformula = QFormula quantifier (Variable newVarName) newSubFormula
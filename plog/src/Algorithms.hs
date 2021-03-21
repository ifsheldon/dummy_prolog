module Algorithms
  ( stripArrows,
    negateFormula,
    standardize,
    VarRecord (..),
    emptyVarRecord,
  )
where

import Data.HashMap.Strict as HashMap
import Data.List (elemIndex)
import Data.Maybe
import SigmaSignature

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
  stripDoubleNot intermediate
  where
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

data VarRecord = VarRecord
  { nameMappings :: HashMap [Char] [Char],
    unboundedVarMappings :: HashMap [Char] [Char],
    variableCount :: Int
  }
  deriving (Show)

emptyVarRecord :: VarRecord
emptyVarRecord = VarRecord {nameMappings = empty, unboundedVarMappings = empty, variableCount = 0}

replaceTerm :: VarRecord -> [[Char]] -> Term -> (VarRecord, Term)
replaceTerm varRecord varTrack term = case term of
  ConstTerm const -> (varRecord, term)
  FuncTerm function termsInFunc -> (newVarRecord, newTerm)
    where
      (newVarRecord, newTermsInFunc) = replaceVarNameInTerms (varRecord, varTrack, termsInFunc)
      newTerm = FuncTerm function newTermsInFunc
  VarTerm (Variable varName) ->
    let mappings = nameMappings varRecord
        varCount = variableCount varRecord
        bounded = varName `elem` varTrack
        nameUsed = varName `member` mappings
        uvm = unboundedVarMappings varRecord
     in if nameUsed && bounded
          then
            let mappedName = fromJust (varName `HashMap.lookup` mappings)
             in (varRecord, VarTerm (Variable mappedName))
          else
            if nameUsed && not bounded
              then
                if varName `member` uvm -- encountered a seen unbounded variable
                  then let mappedName = fromJust (varName `HashMap.lookup` uvm) in (varRecord, VarTerm (Variable mappedName))
                  else -- encounter a new unbounded variable

                    let newName = "#v" ++ show varCount
                        newTerm = VarTerm (Variable newName)
                        intermediateMapping = insert newName newName mappings
                        newMapping = insert varName newName intermediateMapping
                        newGUVM = insert varName newName uvm
                        newCount = varCount + 1
                     in (VarRecord newMapping newGUVM newCount, newTerm)
              else
                if bounded -- not used but bounded, should not happen
                  then (varRecord, VarTerm (Variable "#?"))
                  else --unused and unbounded, no need to change var name
                    (varRecord, term)

replaceVarNameInTerms :: (VarRecord, [[Char]], [Term]) -> (VarRecord, [Term])
replaceVarNameInTerms (varRecord, varTrack, terms) = case terms of
  [] -> (varRecord, terms)
  (t : ts) ->
    let (record, newTerm) = replaceTerm varRecord varTrack t
        (newRecord, newTerms) = replaceVarNameInTerms (record, varTrack, ts)
     in (newRecord, newTerm : newTerms)

checkVarNameAndUpdate :: ([Char], VarRecord) -> ([Char], VarRecord)
checkVarNameAndUpdate (oldVarName, varRecord) =
  let varCount = variableCount varRecord
      usedNameMappings = nameMappings varRecord
   in if oldVarName `member` usedNameMappings
        then
          let newName = "#v" ++ show varCount
              newMappings = insert oldVarName newName usedNameMappings
           in (newName, VarRecord newMappings (unboundedVarMappings varRecord) (varCount + 1))
        else
          let newMappings = insert oldVarName oldVarName usedNameMappings
           in (oldVarName, VarRecord newMappings (unboundedVarMappings varRecord) (varCount + 1))

standardize :: (Formula, [[Char]], VarRecord) -> (Formula, VarRecord)
standardize (formula, varTrack, varRecord) =
  case formula of
    AtomicFormula relation terms ->
      let (newRecord, newTerms) = replaceVarNameInTerms (varRecord, varTrack, terms)
          newFormula = AtomicFormula relation newTerms
       in (newFormula, newRecord)
    NOT subformula ->
      let (sbf, newRecord) = standardize (subformula, varTrack, varRecord)
       in (negateFormula sbf, newRecord)
    AND sf0 sf1 -> (AND newsf0 newsf1, newRecordAfterStandardizeSf1)
      where
        (newsf0, newRecordAfterStandardizeSf0) = standardize (sf0, varTrack, varRecord)
        (newsf1, newRecordAfterStandardizeSf1) = standardize (sf1, varTrack, newRecordAfterStandardizeSf0)
    OR sf0 sf1 -> (OR newsf0 newsf1, newRecordAfterStandardizeSf1)
      where
        (newsf0, newRecordAfterStandardizeSf0) = standardize (sf0, varTrack, varRecord)
        (newsf1, newRecordAfterStandardizeSf1) = standardize (sf1, varTrack, newRecordAfterStandardizeSf0)
    QFormula quantifier (Variable varName) subformula -> (newQformula, newRecord)
      where
        (newVarName, record) = checkVarNameAndUpdate (varName, varRecord)
        (newSubFormula, newRecord) = standardize (subformula, varName : varTrack, record)
        newQformula = QFormula quantifier (Variable newVarName) newSubFormula

data QuantifierTrack = QuantifierTrack
  { seenBoundVarName :: [[Char]],
    seenQuantifiers :: [Quantifier]
  }
  deriving (Show)

processVarTerm :: (QuantifierTrack, Int, Term) -> (Int, Term)
processVarTerm (quantifierTrack, instanceCount, term) =
  let (VarTerm (Variable name)) = term
      seenNames = seenBoundVarName quantifierTrack
      quantifiers = seenQuantifiers quantifierTrack
      (nameSeen, nameIdx) = case name `elemIndex` seenNames of
        Just n -> (True, n)
        Nothing -> (False, -1)
   in if nameSeen
        then
          let quantifier = quantifiers !! nameIdx
           in case quantifier of
                FORALL -> (instanceCount, term)
                EXIST ->
                  if nameIdx == 0 -- meaning it's first
                    then (instanceCount + 1, VarTerm (Variable ("#e" ++ show instanceCount)))
                    else (instanceCount, term) -- TODO
        else -- unbounded variable
          (instanceCount, term)

eliminateExistentialInOneTerm :: (QuantifierTrack, Int, Term) -> (Int, Term)
eliminateExistentialInOneTerm (quantifierTrack, instanceCount, term) =
  case term of
    ConstTerm _ -> (instanceCount, term)
    VarTerm variable -> processVarTerm (quantifierTrack, instanceCount, term)
    FuncTerm function functionTerms -> (newInstanceCount, FuncTerm function newTerms)
      where
        (newTerms, newInstanceCount) = eliminateExistentialInTerms (quantifierTrack, instanceCount, functionTerms)

eliminateExistentialInTerms :: (QuantifierTrack, Int, [Term]) -> ([Term], Int)
eliminateExistentialInTerms (quantifierTrack, instanceCount, terms) =
  case terms of
    [] -> ([], instanceCount)
    (t : ts) -> (terms, instanceCount) --TODO

eliminateExistential :: (Formula, QuantifierTrack, Int) -> (Formula, Int)
eliminateExistential (formula, quantifierTrack, instanceCount) =
  case formula of
    AtomicFormula relation terms -> (formula, instanceCount) -- TODO

module Algorithms
  ( stripArrows,
    negateFormula,
    _standardize,
    VarRecord (..),
    emptyVarRecord,
    eliminateExistentialInFormula,
    dropUniversals,
    distributeANDOR,
    naiveRemoveDuplicate
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
  ConstTerm _ -> (varRecord, term)
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

_standardize :: (Formula, [[Char]], VarRecord) -> (Formula, VarRecord)
_standardize (formula, varTrack, varRecord) =
  case formula of
    AtomicFormula relation terms ->
      let (newRecord, newTerms) = replaceVarNameInTerms (varRecord, varTrack, terms)
          newFormula = AtomicFormula relation newTerms
       in (newFormula, newRecord)
    NOT subformula ->
      let (sbf, newRecord) = _standardize (subformula, varTrack, varRecord)
       in (negateFormula sbf, newRecord)
    AND sf0 sf1 -> (AND newsf0 newsf1, newRecordAfterStandardizeSf1)
      where
        (newsf0, newRecordAfterStandardizeSf0) = _standardize (sf0, varTrack, varRecord)
        (newsf1, newRecordAfterStandardizeSf1) = _standardize (sf1, varTrack, newRecordAfterStandardizeSf0)
    OR sf0 sf1 -> (OR newsf0 newsf1, newRecordAfterStandardizeSf1)
      where
        (newsf0, newRecordAfterStandardizeSf0) = _standardize (sf0, varTrack, varRecord)
        (newsf1, newRecordAfterStandardizeSf1) = _standardize (sf1, varTrack, newRecordAfterStandardizeSf0)
    QFormula quantifier (Variable varName) subformula -> (newQformula, newRecord)
      where
        (newVarName, record) = checkVarNameAndUpdate (varName, varRecord)
        (newSubFormula, newRecord) = _standardize (subformula, varName : varTrack, record)
        newQformula = QFormula quantifier (Variable newVarName) newSubFormula

standardize :: Formula -> Formula 
standardize formula = newFormula
  where
    (newFormula, _) = _standardize (formula, [], emptyVarRecord)

data QuantifierTrack = QuantifierTrack
  { seenBoundVarName :: [[Char]],
    seenQuantifiers :: [Quantifier]
  }
  deriving (Show)

processVarTerm :: (QuantifierTrack, Int, HashMap [Char] Term, Term) -> (Int, HashMap [Char] Term, Term)
processVarTerm (quantifierTrack, instanceCount, existMappings, term) =
  let (VarTerm (Variable name)) = term
      seenNames = seenBoundVarName quantifierTrack
      quantifiers = seenQuantifiers quantifierTrack
      (nameSeen, nameIdx) = case name `elemIndex` seenNames of
        Just n -> (True, n)
        Nothing -> (False, -1)
      nameInExistMappings = name `member` existMappings
   in if nameSeen
        then
          let quantifier = quantifiers !! nameIdx
           in case quantifier of
                FORALL -> (instanceCount, existMappings, term)
                EXIST ->
                  if nameInExistMappings
                    then (instanceCount, existMappings, fromJust (name `HashMap.lookup` existMappings))
                    else -- no previous mapping, create one
                      let 
                        seenQuantifiersBeforeExist = take nameIdx quantifiers
                        seenNamesBeforeExist = take nameIdx seenNames
                        seenQuantifiersWithNameBeforeExist = zip seenQuantifiersBeforeExist seenNamesBeforeExist
                        seenForallWithNameBeforeExist =
                          Prelude.filter
                            ( \(q, _) -> case q of
                                FORALL -> True
                                EXIST -> False
                            )
                            seenQuantifiersWithNameBeforeExist
                        seenForallNames = Prelude.map snd seenForallWithNameBeforeExist
                        functionArity = length seenForallNames
                      in
                        if functionArity == 0 then -- no FORALL dependencies
                          let newExistConstTerm = ConstTerm (ExistConst ("#e" ++ show instanceCount))
                              newMappings = insert name newExistConstTerm existMappings
                          in (instanceCount + 1, newMappings, newExistConstTerm)
                        else
                          let 
                            functionTerms = Prelude.map (VarTerm . Variable) seenForallNames
                            functionName = "#f" ++ show instanceCount
                            newFuncTerm = FuncTerm (Function {name_f = functionName, arity_f = functionArity}) functionTerms
                            newMappings = insert name newFuncTerm existMappings
                          in
                            (instanceCount + 1, newMappings, newFuncTerm)
        else -- unbounded variable
          (instanceCount, existMappings, term)

eliminateExistentialInOneTerm :: (QuantifierTrack, Int, HashMap [Char] Term, Term) -> (Int, HashMap [Char] Term, Term)
eliminateExistentialInOneTerm (quantifierTrack, instanceCount, existMappings, term) =
  case term of
    ConstTerm _ -> (instanceCount, existMappings, term)
    VarTerm _variable -> processVarTerm (quantifierTrack, instanceCount, existMappings, term)
    FuncTerm function functionTerms -> (newInstanceCount, newExistMappings, FuncTerm function newTerms)
      where
        (newTerms, newInstanceCount, newExistMappings) = eliminateExistentialInTerms (quantifierTrack, instanceCount, existMappings, functionTerms)

eliminateExistentialInTerms :: (QuantifierTrack, Int, HashMap [Char] Term, [Term]) -> ([Term], Int, HashMap [Char] Term)
eliminateExistentialInTerms (quantifierTrack, instanceCount, existMappings, terms) =
  -- OPTIMIZE: use foldl
  case terms of
    [] -> ([], instanceCount, existMappings)
    (t : ts) -> (newTerms, newCount, newExistMappings)
      where
        (intermediateCount, intermediateExistMappings, newTerm) = eliminateExistentialInOneTerm (quantifierTrack, instanceCount, existMappings, t)
        (newSubTerms, newCount, newExistMappings) = eliminateExistentialInTerms (quantifierTrack, intermediateCount, intermediateExistMappings, ts)
        newTerms = newTerm : newSubTerms

_eliminateExistential :: (Formula, QuantifierTrack, Int, HashMap [Char] Term) -> (Formula, Int, HashMap [Char] Term)
_eliminateExistential (formula, quantifierTrack, instanceCount, existMappings) =
  case formula of
    AtomicFormula relation terms -> (newAtomicFormula, newCount, newExistMappings)
      where
        (newTerms, newCount, newExistMappings) = eliminateExistentialInTerms (quantifierTrack, instanceCount, existMappings, terms)
        newAtomicFormula = AtomicFormula relation newTerms
    NOT nf -> (newFormula, newCount, newExistMappings)
      where
        (f, newCount, newExistMappings) = _eliminateExistential (nf, quantifierTrack, instanceCount, existMappings)
        newFormula = negateFormula f
    AND f1 f2 -> (newAndFormula, newCount, newExistMappings)
      where
        (processedF1, intermediateCount, intermediateExistMappings) = _eliminateExistential (f1, quantifierTrack, instanceCount, existMappings)
        (processedF2, newCount, newExistMappings) = _eliminateExistential (f2, quantifierTrack, intermediateCount, intermediateExistMappings)
        newAndFormula = AND processedF1 processedF2
    OR f1 f2 -> (newOrFormula, newCount, newExistMappings)
      where
        (processedF1, intermediateCount, intermediateExistMappings) = _eliminateExistential (f1, quantifierTrack, instanceCount, existMappings)
        (processedF2, newCount, newExistMappings) = _eliminateExistential (f2, quantifierTrack, intermediateCount, intermediateExistMappings)
        newOrFormula = OR processedF1 processedF2
    QFormula FORALL var subformula -> (newQformula, newCount, newExistMappings)
      where
        (Variable varName) = var
        newSeenBoundNames = seenBoundVarName quantifierTrack ++ [varName]
        newSeenQuantifiers = seenQuantifiers quantifierTrack ++ [FORALL]
        newQuantifierTrack = QuantifierTrack newSeenBoundNames newSeenQuantifiers
        (newSubformula, newCount, newExistMappings) = _eliminateExistential (subformula, newQuantifierTrack, instanceCount, existMappings)
        newQformula = QFormula FORALL var newSubformula
    QFormula EXIST var subformula -> (newFormula, newCount, newExistMappings)
      where
        (Variable varName) = var
        newSeenBoundNames = seenBoundVarName quantifierTrack ++ [varName]
        newSeenQuantifiers = seenQuantifiers quantifierTrack ++ [EXIST]
        newQuantifierTrack = QuantifierTrack newSeenBoundNames newSeenQuantifiers
        (newFormula, newCount, newExistMappings) = _eliminateExistential (subformula, newQuantifierTrack, instanceCount, existMappings)

eliminateExistentialInFormula :: Formula -> Formula
eliminateExistentialInFormula formula = newFormula
  where
    (newFormula, _, _) = _eliminateExistential (formula, QuantifierTrack [] [], 0, empty)

dropUniversals :: Formula -> Formula
dropUniversals formula = 
  case formula of 
    AtomicFormula relation terms -> formula
    NOT f -> negateFormula (dropUniversals f)
    AND f1 f2 -> AND (dropUniversals f1) (dropUniversals f2)
    OR f1 f2 -> OR (dropUniversals f1) (dropUniversals f2)
    QFormula FORALL _var f -> dropUniversals f

distributeANDOR :: Formula -> Formula 
distributeANDOR formula = case formula of 
  AtomicFormula _relation _terms -> formula
  NOT f -> formula -- since all NOTs have been pushed to inner-most
  AND f1 f2 -> AND (distributeANDOR f1) (distributeANDOR f2)
  OR f1 f2 -> 
    case f1 of 
      -- (f1s1 and f1s2) or f2
      AND f1s1 f1s2 -> AND (distributeANDOR(OR df1s1 df2)) (distributeANDOR(OR df1s2 df2))
        where df1s1 = distributeANDOR f1s1
              df1s2 = distributeANDOR f1s2
              df2 = distributeANDOR f2
      _ -> case f2 of -- case 1: (f1s1 or f1s2) or f2, case 2: f1(atomic) or f2, case 3: NOT subf1 or f2
            AND f2s1 f2s2 -> AND (distributeANDOR(OR df1 df2s1)) (distributeANDOR(OR df1 df2s2)) -- f1 or (f2s1 and f2s2)
              where df1 = distributeANDOR f1
                    df2s1 = distributeANDOR f2s1
                    df2s2 = distributeANDOR f2s2
            _ -> formula -- case 1: f1 or (f2s1 or f2s2), case 2: f1 or f2(atomic)

naiveRemoveDuplicate :: Formula -> Formula 
naiveRemoveDuplicate formula = case formula of 
  AtomicFormula _relation _terms -> formula
  NOT f -> formula -- since NOTs have been push to atomic formulas
  AND f1 f2 -> if f1 == f2 
    then naiveRemoveDuplicate f1
    else
      AND (naiveRemoveDuplicate f1) (naiveRemoveDuplicate f2)
  OR f1 f2 -> if f1 == f2 
    then naiveRemoveDuplicate f1
    else
      OR (naiveRemoveDuplicate f1) (naiveRemoveDuplicate f2)
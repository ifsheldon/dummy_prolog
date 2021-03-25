module Algorithms
  ( stripArrows,
    eliminateExistentialInFormula,
    dropUniversals,
    distributeANDOR,
    naiveRemoveDuplicate,
    findMGU,
    resolveClauses,
    ResolveResult(..),
    _getClausesFromFormula,
    getClausesFromFormula
  )
where

import Data.HashMap.Strict as HashMap
import Data.List (elemIndex, subsequences)
import Data.Maybe
import Literals
import SigmaSignature
import Data.HashSet as HashSet
import Data.Hashable

import Debug.Trace (trace)

_trace msg arg = trace (msg ++ show arg) arg

------------------ This part is for CNF conversion
------------------
_stripDoubleNot :: Formula -> Formula
_stripDoubleNot formula = case formula of
  NOT (NOT f) -> _stripDoubleNot f
  QFormula quantifier var f -> QFormula quantifier var (_stripDoubleNot f)
  _ -> formula

_negateFormula :: Formula -> Formula --finished CNF 2.
-- negateFormula formula = stripDoubleNot (NOT formula)
_negateFormula formula =
  _stripDoubleNot intermediate
  where
    intermediate = case formula of
      NOT subformula -> subformula
      st1 `OR` st2 -> _negateFormula st1 `AND` _negateFormula st2
      st1 `AND` st2 -> _negateFormula st1 `OR` _negateFormula st2
      st1 `IMPLY` st2 -> _negateFormula (stripArrows (st1 `IMPLY` st2))
      st1 `EQUIV` st2 -> _negateFormula (stripArrows (st1 `EQUIV` st2))
      QFormula FORALL var f -> QFormula EXIST var (_negateFormula f)
      QFormula EXIST var f -> QFormula FORALL var (_negateFormula f)
      _ -> NOT formula

stripArrows :: Formula -> Formula -- finished CNF 1.
stripArrows formula = case formula of
  f0 `IMPLY` f1 -> _negateFormula (stripArrows f0) `OR` stripArrows f1
  f0 `EQUIV` f1 -> (_negateFormula sf0 `OR` sf1) `AND` (_negateFormula sf1 `OR` sf0)
    where
      sf0 = stripArrows f0
      sf1 = stripArrows f1
  NOT f -> _negateFormula (stripArrows f)
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

_emptyVarRecord :: VarRecord
_emptyVarRecord = VarRecord {nameMappings = HashMap.empty, unboundedVarMappings = HashMap.empty, variableCount = 0}

_replaceTerm :: VarRecord -> [[Char]] -> Term -> (VarRecord, Term)
_replaceTerm varRecord varTrack term = case term of
  ConstTerm _ -> (varRecord, term)
  FuncTerm function termsInFunc -> (newVarRecord, newTerm)
    where
      (newVarRecord, newTermsInFunc) = _replaceVarNameInTerms (varRecord, varTrack, termsInFunc)
      newTerm = FuncTerm function newTermsInFunc
  VarTerm (Variable varName) ->
    let mappings = nameMappings varRecord
        varCount = variableCount varRecord
        bounded = varName `elem` varTrack
        nameUsed = varName `HashMap.member` mappings
        uvm = unboundedVarMappings varRecord
     in if nameUsed && bounded
          then
            let mappedName = fromJust (varName `HashMap.lookup` mappings)
             in (varRecord, VarTerm (Variable mappedName))
          else
            if nameUsed && not bounded
              then
                if varName `HashMap.member` uvm -- encountered a seen unbounded variable
                  then let mappedName = fromJust (varName `HashMap.lookup` uvm) in (varRecord, VarTerm (Variable mappedName))
                  else -- encounter a new unbounded variable

                    let newName = "#v" ++ show varCount
                        newTerm = VarTerm (Variable newName)
                        intermediateMapping = HashMap.insert newName newName mappings
                        newMapping = HashMap.insert varName newName intermediateMapping
                        newGUVM = HashMap.insert varName newName uvm
                        newCount = varCount + 1
                     in (VarRecord newMapping newGUVM newCount, newTerm)
              else
                if bounded -- not used but bounded, should not happen
                  then (varRecord, VarTerm (Variable "#?"))
                  else --unused and unbounded, no need to change var name
                    (varRecord, term)

_replaceVarNameInTerms :: (VarRecord, [[Char]], [Term]) -> (VarRecord, [Term])
_replaceVarNameInTerms (varRecord, varTrack, terms) = case terms of
  [] -> (varRecord, terms)
  (t : ts) ->
    let (record, newTerm) = _replaceTerm varRecord varTrack t
        (newRecord, newTerms) = _replaceVarNameInTerms (record, varTrack, ts)
     in (newRecord, newTerm : newTerms)

_checkVarNameAndUpdate :: ([Char], VarRecord) -> ([Char], VarRecord)
_checkVarNameAndUpdate (oldVarName, varRecord) =
  let varCount = variableCount varRecord
      usedNameMappings = nameMappings varRecord
   in if oldVarName `HashMap.member` usedNameMappings
        then
          let newName = "#v" ++ show varCount
              newMappings = HashMap.insert oldVarName newName usedNameMappings
           in (newName, VarRecord newMappings (unboundedVarMappings varRecord) (varCount + 1))
        else
          let newMappings = HashMap.insert oldVarName oldVarName usedNameMappings
           in (oldVarName, VarRecord newMappings (unboundedVarMappings varRecord) (varCount + 1))

_standardize :: (Formula, [[Char]], VarRecord) -> (Formula, VarRecord)
_standardize (formula, varTrack, varRecord) =
  case formula of
    AtomicFormula relation terms ->
      let (newRecord, newTerms) = _replaceVarNameInTerms (varRecord, varTrack, terms)
          newFormula = AtomicFormula relation newTerms
       in (newFormula, newRecord)
    NOT subformula ->
      let (sbf, newRecord) = _standardize (subformula, varTrack, varRecord)
       in (_negateFormula sbf, newRecord)
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
        (newVarName, record) = _checkVarNameAndUpdate (varName, varRecord)
        (newSubFormula, newRecord) = _standardize (subformula, varName : varTrack, record)
        newQformula = QFormula quantifier (Variable newVarName) newSubFormula

standardize :: Formula -> Formula
standardize formula = newFormula
  where
    (newFormula, _) = _standardize (formula, [], _emptyVarRecord)

data QuantifierTrack = QuantifierTrack
  { seenBoundVarName :: [[Char]],
    seenQuantifiers :: [Quantifier]
  }
  deriving (Show)

_processVarTerm :: (QuantifierTrack, Int, HashMap [Char] Term, Term) -> (Int, HashMap [Char] Term, Term)
_processVarTerm (quantifierTrack, instanceCount, existMappings, term) =
  let (VarTerm (Variable name)) = term
      seenNames = seenBoundVarName quantifierTrack
      quantifiers = seenQuantifiers quantifierTrack
      (nameSeen, nameIdx) = case name `elemIndex` seenNames of
        Just n -> (True, n)
        Nothing -> (False, -1)
      nameInExistMappings = name `HashMap.member` existMappings
   in if nameSeen
        then
          let quantifier = quantifiers !! nameIdx
           in case quantifier of
                FORALL -> (instanceCount, existMappings, term)
                EXIST ->
                  if nameInExistMappings
                    then (instanceCount, existMappings, fromJust (name `HashMap.lookup` existMappings))
                    else -- no previous mapping, create one

                      let seenQuantifiersBeforeExist = take nameIdx quantifiers
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
                       in if functionArity == 0 -- no FORALL dependencies
                            then
                              let newExistConstTerm = ConstTerm (ExistConst ("#e" ++ show instanceCount))
                                  newMappings = HashMap.insert name newExistConstTerm existMappings
                               in (instanceCount + 1, newMappings, newExistConstTerm)
                            else
                              let functionTerms = Prelude.map (VarTerm . Variable) seenForallNames
                                  functionName = "#f" ++ show instanceCount
                                  newFuncTerm = FuncTerm (Function {name_f = functionName, arity_f = functionArity}) functionTerms
                                  newMappings = HashMap.insert name newFuncTerm existMappings
                               in (instanceCount + 1, newMappings, newFuncTerm)
        else -- unbounded variable
          (instanceCount, existMappings, term)

_eliminateExistentialInOneTerm :: (QuantifierTrack, Int, HashMap [Char] Term, Term) -> (Int, HashMap [Char] Term, Term)
_eliminateExistentialInOneTerm (quantifierTrack, instanceCount, existMappings, term) =
  case term of
    ConstTerm _ -> (instanceCount, existMappings, term)
    VarTerm _variable -> _processVarTerm (quantifierTrack, instanceCount, existMappings, term)
    FuncTerm function functionTerms -> (newInstanceCount, newExistMappings, FuncTerm function newTerms)
      where
        (newTerms, newInstanceCount, newExistMappings) = _eliminateExistentialInTerms (quantifierTrack, instanceCount, existMappings, functionTerms)

_eliminateExistentialInTerms :: (QuantifierTrack, Int, HashMap [Char] Term, [Term]) -> ([Term], Int, HashMap [Char] Term)
_eliminateExistentialInTerms (quantifierTrack, instanceCount, existMappings, terms) =
  -- OPTIMIZE: use foldl
  case terms of
    [] -> ([], instanceCount, existMappings)
    (t : ts) -> (newTerms, newCount, newExistMappings)
      where
        (intermediateCount, intermediateExistMappings, newTerm) = _eliminateExistentialInOneTerm (quantifierTrack, instanceCount, existMappings, t)
        (newSubTerms, newCount, newExistMappings) = _eliminateExistentialInTerms (quantifierTrack, intermediateCount, intermediateExistMappings, ts)
        newTerms = newTerm : newSubTerms

_eliminateExistential :: (Formula, QuantifierTrack, Int, HashMap [Char] Term) -> (Formula, Int, HashMap [Char] Term)
_eliminateExistential (formula, quantifierTrack, instanceCount, existMappings) =
  case formula of
    AtomicFormula relation terms -> (newAtomicFormula, newCount, newExistMappings)
      where
        (newTerms, newCount, newExistMappings) = _eliminateExistentialInTerms (quantifierTrack, instanceCount, existMappings, terms)
        newAtomicFormula = AtomicFormula relation newTerms
    NOT nf -> (newFormula, newCount, newExistMappings)
      where
        (f, newCount, newExistMappings) = _eliminateExistential (nf, quantifierTrack, instanceCount, existMappings)
        newFormula = _negateFormula f
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
    (newFormula, _, _) = _eliminateExistential (formula, QuantifierTrack [] [], 0, HashMap.empty)

dropUniversals :: Formula -> Formula
dropUniversals formula =
  case formula of
    AtomicFormula relation terms -> formula
    NOT f -> _negateFormula (dropUniversals f)
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
      AND f1s1 f1s2 -> AND (distributeANDOR (OR df1s1 df2)) (distributeANDOR (OR df1s2 df2))
        where
          df1s1 = distributeANDOR f1s1
          df1s2 = distributeANDOR f1s2
          df2 = distributeANDOR f2
      _ -> case f2 of -- case 1: (f1s1 or f1s2) or f2, case 2: f1(atomic) or f2, case 3: NOT subf1 or f2
        AND f2s1 f2s2 -> AND (distributeANDOR (OR df1 df2s1)) (distributeANDOR (OR df1 df2s2)) -- f1 or (f2s1 and f2s2)
          where
            df1 = distributeANDOR f1
            df2s1 = distributeANDOR f2s1
            df2s2 = distributeANDOR f2s2
        _ -> formula -- case 1: f1 or (f2s1 or f2s2), case 2: f1 or f2(atomic)

naiveRemoveDuplicate :: Formula -> Formula
naiveRemoveDuplicate formula = case formula of
  AtomicFormula _relation _terms -> formula
  NOT f -> formula -- since NOTs have been push to atomic formulas
  AND f1 f2 ->
    if f1 == f2
      then naiveRemoveDuplicate f1
      else AND (naiveRemoveDuplicate f1) (naiveRemoveDuplicate f2)
  OR f1 f2 ->
    if f1 == f2
      then naiveRemoveDuplicate f1
      else OR (naiveRemoveDuplicate f1) (naiveRemoveDuplicate f2)

------------------ This part is for MGU
------------------
data Substitution = Term `BY` Term deriving (Show, Eq)

data Disagreement = NONE | NONUNIFIABLE | UNIFIABLE {replacee :: Term, replacement :: Term} deriving (Show, Eq)

_stripNOT :: Formula -> Formula
_stripNOT literalFormula =
  case literalFormula of
    NOT f -> f
    _ -> literalFormula

_getVarInTerms :: [Term] -> [Variable] -> [Variable]
_getVarInTerms terms varlist =
  case terms of
    [] -> varlist
    (t : ts) ->
      case t of
        ConstTerm _ -> varlist
        VarTerm var -> var : varlist
        FuncTerm _ funcTerms -> newVarList
          where
            intermediateVarList = _getVarInTerms funcTerms varlist
            newVarList = _getVarInTerms ts intermediateVarList

_findDisagreementInTerms :: [Term] -> [Term] -> Disagreement
_findDisagreementInTerms ts1 ts2 =
  let termPairs = zip ts1 ts2
   in case termPairs of
        [] -> NONE
        (tp : tps) ->
          let (ts1rest, ts2rest) = unzip tps
          in 
            if fst tp == snd tp 
              then _findDisagreementInTerms ts1rest ts2rest
              else 
                case tp of
                  (ConstTerm t1, ConstTerm t2) -> if t1 == t2 
                    then _findDisagreementInTerms ts1rest ts2rest
                    else NONUNIFIABLE --ignoring the case (concrete const, existential const)
                  (ConstTerm t1, VarTerm t2) -> UNIFIABLE (snd tp) (fst tp)
                  (ConstTerm _, FuncTerm _ _) -> NONUNIFIABLE
                  (VarTerm t1, ConstTerm t2) -> uncurry UNIFIABLE tp
                  (VarTerm t1, VarTerm t2) -> if t1 == t2 
                    then _findDisagreementInTerms ts1rest ts2rest
                    else uncurry UNIFIABLE tp
                  (VarTerm t1, FuncTerm _ funcTerms) ->
                    if t1 `elem` varsInFuncTerms then NONUNIFIABLE else uncurry UNIFIABLE tp
                    where
                      varsInFuncTerms = _getVarInTerms funcTerms []
                  (FuncTerm _ _, ConstTerm _) -> NONUNIFIABLE
                  (FuncTerm _ funcTerms, VarTerm t2) ->
                    if t2 `elem` varsInFuncTerms then NONUNIFIABLE else UNIFIABLE (snd tp) (fst tp)
                    where
                      varsInFuncTerms = _getVarInTerms funcTerms []
                  (FuncTerm f1 fts1, FuncTerm f2 fts2) ->
                    if f1 == f2
                      then _findDisagreementInTerms fts1 fts2
                      else NONUNIFIABLE

_findOneDisagreement :: Literal -> Literal -> Disagreement
_findOneDisagreement l1 l2 =
  let (Literal lf1, Literal lf2) = (l1, l2) -- literal formulas
      (af1, af2) = (_stripNOT lf1, _stripNOT lf2) -- atomic formulas
      (AtomicFormula r1 terms1, AtomicFormula r2 terms2) = (af1, af2)
   in if r1 == r2 then _findDisagreementInTerms terms1 terms2 else NONUNIFIABLE

_applySubstitutionOnOneTerm :: Substitution -> Term -> Term
_applySubstitutionOnOneTerm sub term =
  case term of
    FuncTerm f termsInFunc -> FuncTerm f (_applySubstitutionOnTerms sub termsInFunc)
    _ -> if term == t0 then t1 else term where (t0 `BY` t1) = sub

_applySubstitutionOnTerms :: Substitution -> [Term] -> [Term]
_applySubstitutionOnTerms sub = Prelude.map (_applySubstitutionOnOneTerm sub)

_applySubstitutionOnLiteral :: Substitution -> Literal -> Literal
_applySubstitutionOnLiteral sub literal =
  let (Literal literalFormula) = literal
      simplifiedAF = _stripNOT literalFormula
      (AtomicFormula _relation terms) = simplifiedAF
      transformedTerms = _applySubstitutionOnTerms sub terms
   in case literalFormula of
        (NOT (AtomicFormula r terms)) -> Literal (NOT (AtomicFormula r transformedTerms))
        (AtomicFormula r terms) -> Literal (AtomicFormula r transformedTerms)

findMGU :: (Literal, Literal, Maybe [Substitution]) -> (Literal, Literal, Maybe [Substitution])
findMGU (l1, l2, substitutions) =
  let disagreement = _findOneDisagreement l1 l2
      (finished, unifiable) = case disagreement of
        NONE -> (True, True)
        NONUNIFIABLE -> (True, False)
        UNIFIABLE _ _ -> (False, True)
   in if finished && unifiable
        then (l1, l2, substitutions)
        else
          if finished && not unifiable
            then (l1, l2, Nothing)
            else
              let sub = replacee disagreement `BY` replacement disagreement
                  newSubstitutions = case substitutions of
                    Nothing -> Just [sub]
                    Just subs -> Just (subs ++ [sub])
                  (newl1, newl2) = (_applySubstitutionOnLiteral sub l1, _applySubstitutionOnLiteral sub l2)
               in findMGU (newl1, newl2, newSubstitutions)

------------------ This part is for FOL resolution
------------------
data ClauseRecord = CR { claus :: Clause , relationSet :: HashSet [Char]}
instance Show ClauseRecord where
  show cr = show (claus cr)
instance Hashable ClauseRecord where
  hashWithSalt salt cl = hashWithSalt salt (claus cl)

instance Eq ClauseRecord where
  cr1 == cr2 = claus cr1 == claus cr2

data ResolveResult = IRRESOLVABLE | RESOLVABLE (Maybe ClauseRecord) deriving(Show, Eq)

_getLiteralsFromClause :: Clause -> [Literal]
_getLiteralsFromClause clause = literals where (Clause literals) = clause

_getAtomicFormulaFromLiteral :: Literal -> Formula
_getAtomicFormulaFromLiteral literal = atomicFormula where (Literal atomicFormula) = literal

_countRelationNames :: [Char] -> HashMap [Char] Int -> HashMap [Char] Int
_countRelationNames relationName nameCounts =
  if relationName `HashMap.member` nameCounts then
    let count = nameCounts ! relationName
    in HashMap.insert relationName (count + 1) nameCounts
  else
    HashMap.insert relationName 1 nameCounts

_checkAloneRelation :: [Clause] -> Bool 
_checkAloneRelation clauses = 
  let allLiterals = Prelude.foldr (++) [] (Prelude.map _getLiteralsFromClause clauses)
      allAFs = Prelude.map _getAtomicFormulaFromLiteral allLiterals
      allRelationNames = Prelude.map (\af -> let (AtomicFormula (Relation relationName _) _) = _stripNOT af in relationName) allAFs
      relationCount = Prelude.foldr _countRelationNames HashMap.empty allRelationNames
      allCounts = HashMap.elems relationCount
      contains1 = 1 `elem` allCounts
  in
    contains1

_clauseToCR :: Clause -> ClauseRecord
_clauseToCR clause =
  let (Clause literals) = clause
      rSet = HashSet.fromList (Prelude.map (\(Literal literalFormula) -> let af = _stripNOT literalFormula 
                                                                             (AtomicFormula (Relation rName _) _) = af 
                                                                          in rName ) literals)
  in
    CR clause rSet

_tryResolveTwoLiteral :: Literal -> Literal -> [Substitution] -> Maybe [Substitution]
_tryResolveTwoLiteral l1 l2 subs =
  let (Literal af1, Literal af2) = (l1, l2)
  in case (af1, af2) of
    (AtomicFormula _ _, AtomicFormula _ _) -> Nothing 
    (NOT (AtomicFormula _ _), NOT (AtomicFormula _ _)) -> Nothing 
    _ -> -- either one has a NOT, the other has no NOT
      let (_newl1, _newl2, newsubs) = findMGU (l1, l2, Just subs)
      in
        case newsubs of
          Nothing -> Nothing -- since the two are not unifiable, they cannot resolve, so returning Nothing
          Just newsubstituions -> newsubs -- the two can resolve each other, returnning a new substituion list that is appended with new substituions that unify the two literals

__resolveOneLiteralWithLiteralSet :: Literal -> [Literal] -> [Literal] -> Maybe ([Literal], [Substitution])
__resolveOneLiteralWithLiteralSet resolver resolvees preresolvees =
  case resolvees of 
    [] -> Nothing 
    (resolvee : rs) ->
      let maybeNewSubs = _tryResolveTwoLiteral resolver resolvee []
      in
        case maybeNewSubs of -- if find one pair that can be resolve, stop
          Nothing -> __resolveOneLiteralWithLiteralSet resolver rs (resolvee : preresolvees)
          Just subs -> Just (preresolvees ++ rs , subs)

_resolveOneLiteralWithLiteralSet :: Literal -> [Literal] -> Maybe ([Literal], [Substitution])
_resolveOneLiteralWithLiteralSet resolver resolvees = __resolveOneLiteralWithLiteralSet resolver resolvees []

_applySubsOnLiteral :: [Substitution] -> Literal -> Literal
_applySubsOnLiteral subs literal =
  case subs of
    [] -> literal
    (sub:restsubs) -> _applySubsOnLiteral restsubs (_applySubstitutionOnLiteral sub literal)

_addToSet :: Literal -> HashSet Literal -> HashSet Literal
_addToSet literal literalSet =
  let negatedLiteral = case literal of 
        (Literal (NOT af)) -> Literal af
        (Literal af) -> Literal (NOT af)
  in
    if negatedLiteral `HashSet.member` literalSet
      then
        HashSet.delete negatedLiteral literalSet
      else
        HashSet.insert literal literalSet


_filterOutPosNegLiteralPairsInLiterals :: [Literal] -> [Literal]
_filterOutPosNegLiteralPairsInLiterals literals = HashSet.toList (Prelude.foldr _addToSet HashSet.empty literals)

__resolveTwoLiteralSets :: [Literal] -> [Literal]-> [Literal] -> Maybe ClauseRecord
__resolveTwoLiteralSets ls1 prels1 ls2 =
  case ls1 of
    [] -> Nothing 
    (l : ls) ->
      let maybeResolveResult = _resolveOneLiteralWithLiteralSet l ls2
      in
        case maybeResolveResult of 
          Nothing -> __resolveTwoLiteralSets ls (l:prels1) ls2
          Just (newls2, subs) ->
            let newls1 = prels1 ++ ls
                newls1WithSubs = Prelude.map (_applySubsOnLiteral subs) newls1
                newls2WithSubs = Prelude.map (_applySubsOnLiteral subs) newls2
                newClause = Clause (_filterOutPosNegLiteralPairsInLiterals (newls1WithSubs ++ newls2WithSubs))
            in
              Just (_clauseToCR newClause)

_resolveTwoLiteralSets :: [Literal] -> [Literal] -> Maybe ClauseRecord
_resolveTwoLiteralSets ls1 ls2 = __resolveTwoLiteralSets ls1 [] ls2

_resolve1on1Clause :: ClauseRecord -> ClauseRecord -> ResolveResult
_resolve1on1Clause clause1 clause2 =
  let relationsInClause1 = relationSet (_trace "------ \n clause1: " clause1)
      relationsInClause2 = relationSet (_trace "clause2: " clause2)
      (Clause literalsInC1, Clause literalsInC2) = (claus clause1, claus clause2)
      commonRelations = HashSet.intersection relationsInClause1 relationsInClause2
  in 
    if HashSet.size commonRelations /= 0
      then
        let maybeNewClause = _resolveTwoLiteralSets literalsInC1 literalsInC2
        in
          case maybeNewClause of
            Nothing -> IRRESOLVABLE
            Just newClauseRecord -> 
              let (Clause newLiterals) = claus newClauseRecord
              in
                if Prelude.null newLiterals -- if resulting clause has no literals, then found contradiction
                  then
                    RESOLVABLE Nothing
                  else
                    RESOLVABLE (Just newClauseRecord)
      else -- if not having common relations, two clauses for sure cannot resolve
        IRRESOLVABLE

_allCombinations :: [ClauseRecord] -> [(ClauseRecord, ClauseRecord)]
_allCombinations clauses = Prelude.map (\x -> (x !! 0, x !! 1)) (Prelude.filter ((2==).length) (subsequences clauses))

_genCombinations :: ClauseRecord -> [ClauseRecord] -> [(ClauseRecord, ClauseRecord)]
_genCombinations newClause existingClauses = Prelude.map (\claus -> (newClause, claus)) existingClauses

_resolveClausePairs :: [(ClauseRecord, ClauseRecord)] -> HashSet ClauseRecord -> ([(ClauseRecord, ClauseRecord)], HashSet ClauseRecord, ResolveResult)
_resolveClausePairs clausePairs clauseSet =
  case clausePairs of 
    [] -> (clausePairs, clauseSet, IRRESOLVABLE)
    ((clause1, clause2) : restClausePairs) -> 
      let resolveResultOfThePair = _resolve1on1Clause clause1 clause2
      in
        case (_trace "resolve result: "  resolveResultOfThePair) of 
          IRRESOLVABLE -> _resolveClausePairs restClausePairs clauseSet
          RESOLVABLE Nothing -> (clausePairs, clauseSet, RESOLVABLE Nothing) -- found contradictions, return
          RESOLVABLE (Just newClauseRecord) -> 
            if newClauseRecord `HashSet.member` clauseSet
              then _resolveClausePairs restClausePairs clauseSet
            else
              let newClauseSet = HashSet.insert newClauseRecord clauseSet
                  newClausePairs = restClausePairs ++ _genCombinations newClauseRecord (HashSet.toList clauseSet)
              in _resolveClausePairs newClausePairs newClauseSet


resolveClauses :: [Clause] -> ResolveResult
resolveClauses clauses =
  if _checkAloneRelation clauses then
    IRRESOLVABLE -- if clauses containing one or more relations that occur once, cannot resolve, return []
  else 
    let clauseRecordList = Prelude.map _clauseToCR clauses
        clauseRecordSet = HashSet.fromList clauseRecordList
        initialCombinations = _allCombinations clauseRecordList
    in
      let (_, _, resolveResult) = _resolveClausePairs initialCombinations clauseRecordSet
      in 
        case resolveResult of 
          IRRESOLVABLE -> IRRESOLVABLE
          RESOLVABLE Nothing -> RESOLVABLE Nothing

------------------ This part is for FOL resolution integration
------------------

_getClausesFromFormula :: Formula -> [Clause]
_getClausesFromFormula formula = 
  let strippedArrowFormula = _trace "\nAfter eliminating arrows: " (stripArrows formula)
      standardizedFormula = _trace "\nAfter standardization: "(standardize strippedArrowFormula)
      eliminatedExistFormula = _trace "\nAfter eliminating Existentials: " (eliminateExistentialInFormula standardizedFormula)
      droppedUniversalFormula = _trace "\nAfter dropping Universals: " (dropUniversals eliminatedExistFormula)
      distributedANDORFormula = _trace "After distributing AND OR: " (distributeANDOR droppedUniversalFormula)
      removedDuplicateFormula = _trace "After naively remove duplications: " (naiveRemoveDuplicate distributedANDORFormula)
  in fromCNFFormulaToClauses removedDuplicateFormula

getClausesFromFormula :: Formula -> [Clause]
getClausesFromFormula = 
  fromCNFFormulaToClauses . naiveRemoveDuplicate 
    . distributeANDOR . dropUniversals . eliminateExistentialInFormula . standardize . stripArrows
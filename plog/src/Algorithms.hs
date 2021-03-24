module Algorithms
  ( stripArrows,
    negateFormula,
    _standardize,
    VarRecord (..),
    emptyVarRecord,
    eliminateExistentialInFormula,
    dropUniversals,
    distributeANDOR,
    naiveRemoveDuplicate,
    findMGU,
    Substitution (..),
    Disagreement (..),
    findOneDisagreement,
    applySubstitutionOnLiteral,
    applySubstitutionOnOneTerm
  )
where

import Data.HashMap.Strict as HashMap
import Data.List (elemIndex)
import Data.Maybe
import Literals
import SigmaSignature
import Data.HashSet as HashSet
import Data.Hashable

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
emptyVarRecord = VarRecord {nameMappings = HashMap.empty, unboundedVarMappings = HashMap.empty, variableCount = 0}

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
    (newFormula, _, _) = _eliminateExistential (formula, QuantifierTrack [] [], 0, HashMap.empty)

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

findDisagreementInTerms :: [Term] -> [Term] -> Disagreement
findDisagreementInTerms ts1 ts2 =
  let termPairs = zip ts1 ts2
   in case termPairs of
        [] -> NONE
        (tp : tps) ->
          let (ts1rest, ts2rest) = unzip tps
          in 
            if fst tp == snd tp 
              then findDisagreementInTerms ts1rest ts2rest
              else 
                case tp of
                  (ConstTerm t1, ConstTerm t2) -> if t1 == t2 
                    then findDisagreementInTerms ts1rest ts2rest
                    else NONUNIFIABLE --ignoring the case (concrete const, existential const)
                  (ConstTerm t1, VarTerm t2) -> UNIFIABLE (snd tp) (fst tp)
                  (ConstTerm _, FuncTerm _ _) -> NONUNIFIABLE
                  (VarTerm t1, ConstTerm t2) -> uncurry UNIFIABLE tp
                  (VarTerm t1, VarTerm t2) -> if t1 == t2 
                    then findDisagreementInTerms ts1rest ts2rest
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
                      then findDisagreementInTerms fts1 fts2
                      else NONUNIFIABLE

findOneDisagreement :: Literal -> Literal -> Disagreement
findOneDisagreement l1 l2 =
  let (Literal lf1, Literal lf2) = (l1, l2) -- literal formulas
      (af1, af2) = (_stripNOT lf1, _stripNOT lf2) -- atomic formulas
      (AtomicFormula r1 terms1, AtomicFormula r2 terms2) = (af1, af2)
   in if r1 == r2 then findDisagreementInTerms terms1 terms2 else NONUNIFIABLE

applySubstitutionOnOneTerm :: Substitution -> Term -> Term
applySubstitutionOnOneTerm sub term =
  case term of
    FuncTerm f termsInFunc -> FuncTerm f (applySubstitutionOnTerms sub termsInFunc)
    _ -> if term == t0 then t1 else term where (t0 `BY` t1) = sub

applySubstitutionOnTerms :: Substitution -> [Term] -> [Term]
applySubstitutionOnTerms sub = Prelude.map (applySubstitutionOnOneTerm sub)

applySubstitutionOnLiteral :: Substitution -> Literal -> Literal
applySubstitutionOnLiteral sub literal =
  let (Literal literalFormula) = literal
      simplifiedAF = _stripNOT literalFormula
      (AtomicFormula _relation terms) = simplifiedAF
      transformedTerms = applySubstitutionOnTerms sub terms
   in case literalFormula of
        (NOT (AtomicFormula r terms)) -> Literal (NOT (AtomicFormula r transformedTerms))
        (AtomicFormula r terms) -> Literal (AtomicFormula r transformedTerms)

findMGU :: (Literal, Literal, Maybe [Substitution]) -> (Literal, Literal, Maybe [Substitution])
findMGU (l1, l2, substitutions) =
  let disagreement = findOneDisagreement l1 l2
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
                  (newl1, newl2) = (applySubstitutionOnLiteral sub l1, applySubstitutionOnLiteral sub l2)
               in findMGU (newl1, newl2, newSubstitutions)

------------------ This part is for FOL resolution
------------------
data ClauseRecord = CR { claus :: Clause , relationSet :: HashSet [Char]} deriving (Show)
instance Hashable ClauseRecord where
  hashWithSalt salt cl = hashWithSalt salt (claus cl)

instance Eq ClauseRecord where
  cr1 == cr2 = claus cr1 == claus cr2

data ResolveResult = IRRESOLVABLE | RESOLVABLE (Maybe ClauseRecord) deriving(Show, Eq)

getLiteralsFromClause :: Clause -> [Literal]
getLiteralsFromClause clause = literals where (Clause literals) = clause

getAtomicFormulaFromLiteral :: Literal -> Formula
getAtomicFormulaFromLiteral literal = atomicFormula where (Literal atomicFormula) = literal

countRelationNames :: [Char] -> HashMap [Char] Int -> HashMap [Char] Int
countRelationNames relationName nameCounts = 
  if relationName `HashMap.member` nameCounts then
    let count = nameCounts ! relationName
    in HashMap.insert relationName (count + 1) nameCounts
  else
    HashMap.insert relationName 1 nameCounts

_checkAloneRelation :: [Clause] -> Bool 
_checkAloneRelation clauses = 
  let allLiterals = Prelude.foldr (++) [] (Prelude.map getLiteralsFromClause clauses)
      allAFs = Prelude.map getAtomicFormulaFromLiteral allLiterals
      allRelationNames = Prelude.map (\af -> let (AtomicFormula (Relation relationName _) _) = af in relationName) allAFs
      relationCount = Prelude.foldr countRelationNames HashMap.empty allRelationNames
      allCounts = HashMap.elems relationCount
      contains1 = 1 `elem` allCounts
  in
    contains1

recordR2LRMapping :: ([Char], Literal) -> HashMap [Char] [Literal] -> HashMap [Char] [Literal]
recordR2LRMapping lrWithRName r2lrMappings = 
  let (relationName, lr) = lrWithRName
  in
    if relationName `HashMap.member` r2lrMappings
      then
        let lrList = r2lrMappings ! relationName
        in HashMap.insert relationName (lr : lrList) r2lrMappings
    else
      HashMap.insert relationName [lr] r2lrMappings

clauseToCR :: Clause -> ClauseRecord
clauseToCR clause = 
  let (Clause literals) = clause
      rSet = HashSet.fromList (Prelude.map (\(Literal literalFormula) -> let af = _stripNOT literalFormula 
                                                                             (AtomicFormula (Relation rName _) _) = af 
                                                                          in rName ) literals)
  in
    CR clause rSet

tryResolveTwoLiteral :: Literal -> Literal -> [Substitution] -> Maybe [Substitution]
tryResolveTwoLiteral l1 l2 subs = 
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

_resolveOneLiteralWithLiteralSet :: Literal -> [Literal] -> [Literal] -> Maybe ([Literal], [Substitution])
_resolveOneLiteralWithLiteralSet resolver resolvees preresolvees = 
  case resolvees of 
    [] -> Nothing 
    (resolvee : rs) ->
      let maybeNewSubs = tryResolveTwoLiteral resolver resolvee []
      in
        case maybeNewSubs of -- if find one pair that can be resolve, stop
          Nothing -> _resolveOneLiteralWithLiteralSet resolver rs (resolvee : preresolvees)
          Just subs -> Just (preresolvees ++ rs , subs)

resolveOneLiteralWithLiteralSet :: Literal -> [Literal] -> Maybe ([Literal], [Substitution])
resolveOneLiteralWithLiteralSet resolver resolvees = _resolveOneLiteralWithLiteralSet resolver resolvees []

applySubsOnLiteral :: [Substitution] -> Literal -> Literal
applySubsOnLiteral subs literal =
  case subs of
    [] -> literal
    (sub:restsubs) -> applySubsOnLiteral restsubs (applySubstitutionOnLiteral sub literal)

_resolveTwoLiteralSets :: [Literal] -> [Literal]-> [Literal] -> Maybe ClauseRecord
_resolveTwoLiteralSets ls1 prels1 ls2 =
  case ls1 of
    [] -> Nothing 
    (l : ls) ->
      let maybeResolveResult = resolveOneLiteralWithLiteralSet l ls2
      in
        case maybeResolveResult of 
          Nothing -> _resolveTwoLiteralSets ls (l:prels1) ls2
          Just (newls2, subs) ->
            let newls1 = prels1 ++ ls
                newls1WithSubs = Prelude.map (applySubsOnLiteral subs) newls1
                newls2WithSubs = Prelude.map (applySubsOnLiteral subs) newls2
                newClause = Clause (newls1WithSubs ++ newls2WithSubs)
            in
              Just (clauseToCR newClause)

resolveTwoLiteralSets :: [Literal] -> [Literal] -> Maybe ClauseRecord
resolveTwoLiteralSets ls1 ls2 = _resolveTwoLiteralSets ls1 [] ls2

resolve1on1Clause :: ClauseRecord -> ClauseRecord -> ResolveResult
resolve1on1Clause clause1 clause2 = 
  let relationsInClause1 = relationSet clause1
      relationsInClause2 = relationSet clause2
      commonRelations = HashSet.intersection relationsInClause1 relationsInClause2
  in 
    if HashSet.size commonRelations /= 0
      then -- TODO
        IRRESOLVABLE
      else -- if not having common relations, two clauses for sure cannot resolve
        IRRESOLVABLE

resolve :: ClauseRecord -> [ClauseRecord] -> Maybe [ClauseRecord]
resolve clause toResolveClauses = 
  case toResolveClauses of 
    [] -> Just [] -- todo: check this logic
    (c : trcs) ->
      let resolveResult = resolve1on1Clause clause c
      in 
        case resolveResult of
          IRRESOLVABLE -> Just [] 
          RESOLVABLE resolvedClause ->
            case resolvedClause of
              Nothing -> Nothing -- resolution succeeded
              Just resultedClause -> Nothing -- TODO

resolveClauses :: [Clause] -> Maybe [Clause]
resolveClauses clauses =
  if _checkAloneRelation clauses then
    Just [] -- if clauses containing one or more relations that occur once, cannot resolve, return []
  else 
    let clauseRecordList = Prelude.map clauseToCR clauses
        numClauses = length clauseRecordList
        indices = [0,1..(numClauses-1)]
        crWithIdx = zip indices clauseRecordList
        toDoList = Prelude.map (\(idx, cr)-> let toResolveCRs = Prelude.filter (\(cridx, _) -> cridx /= idx) crWithIdx in (cr, toResolveCRs)) crWithIdx
        toDoMap = HashMap.fromList toDoList
    in
      Nothing -- TODO
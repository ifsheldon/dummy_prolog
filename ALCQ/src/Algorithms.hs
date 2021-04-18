module Algorithms
  ( toNNF,
    constructABRFromABox,
    ABoxRecord (..),
    applyExistRule,
    applyForallRule,
    applyAndRule,
    applyOrRule,
    tableauAlgorithm,
  )
where

import ABox
import Data.HashMap.Strict as HashMap
import Data.HashSet as HashSet
import Numeric (showHex)

stripDoubleNot :: Concept -> Concept
stripDoubleNot concept =
  case concept of
    Not (Not c) -> stripDoubleNot c
    Forall r c -> Forall r (stripDoubleNot c)
    Exist r c -> Exist r (stripDoubleNot c)
    _ -> concept

stripArrows :: Concept -> Concept
stripArrows concept = case concept of
  Imply c1 c2 -> negateConcept (stripArrows c1) `Or` stripArrows c2
  Equiv c1 c2 -> stripArrows (Imply c1 c2) `And` stripArrows (Imply c2 c1)
  Not c -> negateConcept (stripArrows c)
  c1 `And` c2 -> stripArrows c1 `And` stripArrows c2
  c1 `Or` c2 -> stripArrows c1 `Or` stripArrows c2
  Forall r c -> Forall r (stripArrows c)
  Exist r c -> Exist r (stripArrows c)
  _ -> concept

toNNF = stripArrows

negateConcept :: Concept -> Concept
negateConcept concept = stripDoubleNot intermediate
  where
    intermediate = case concept of
      Not c -> c
      And c1 c2 -> Or (negateConcept c1) (negateConcept c2)
      Or c1 c2 -> And (negateConcept c1) (negateConcept c2)
      Imply _ _ -> negateConcept (stripArrows concept)
      Equiv _ _ -> negateConcept (stripArrows concept)
      Forall r c -> Exist r (negateConcept c)
      Exist r c -> Forall r (negateConcept c)
      Primitive _ -> Not concept

toNNFAssertion :: Assertion -> Assertion
toNNFAssertion assertion =
  case assertion of
    RAssert _ _ _ -> assertion
    CAssert concept individual -> CAssert (toNNF concept) individual

data ABoxRecord = ABR
  { relationMapping :: HashMap Relation (HashMap Individual (HashSet Individual)),
    conceptAssertionList :: [Assertion]
  }

insertRAssertionIntoRelationMap :: Assertion -> HashMap Relation (HashMap Individual (HashSet Individual)) -> HashMap Relation (HashMap Individual (HashSet Individual))
insertRAssertionIntoRelationMap r_assertion relationMap =
  case r_assertion of
    RAssert relation i1 i2 ->
      case HashMap.lookup relation relationMap of
        Nothing ->
          -- relation not found in relation map
          HashMap.insert relation new_individual_map relationMap
          where
            new_individual_set = HashSet.singleton i2
            new_individual_map = HashMap.singleton i1 new_individual_set
        Just individual_map ->
          -- found relation in relation map
          case HashMap.lookup i1 individual_map of
            -- i1 not found in individual map
            Nothing ->
              HashMap.insert relation new_individual_map relationMap
              where
                new_individual_set = HashSet.singleton i2
                new_individual_map = HashMap.insert i1 new_individual_set individual_map
            Just individual_set ->
              -- i1 found in individual map
              HashMap.insert relation new_individual_map relationMap
              where
                new_individual_set = HashSet.insert i2 individual_set
                new_individual_map = HashMap.insert i1 new_individual_set individual_map

addAssertionToABR :: Assertion -> ABoxRecord -> ABoxRecord
addAssertionToABR assertion abr =
  case assertion of
    RAssert _ _ _ -> ABR (insertRAssertionIntoRelationMap assertion (relationMapping abr)) (conceptAssertionList abr)
    CAssert _ _ -> ABR (relationMapping abr) (assertion : conceptAssertionList abr)

constructABRFromABox :: ABox -> ABoxRecord
constructABRFromABox abox =
  let Abox assertionSet = abox
      nnfAssertionSet = HashSet.map toNNFAssertion assertionSet
      emptyABR = ABR HashMap.empty []
   in HashSet.foldr addAssertionToABR emptyABR assertionSet

applyAndRuleForOneABox :: ABoxRecord -> (ABoxRecord, Bool)
applyAndRuleForOneABox abr =
  let runningRecord = (abr, False)
   in Prelude.foldr
        ( \concept_assert (intermediateAbr, applied) -> case concept_assert of
            CAssert (And c1 c2) individual ->
              let concept_assertion_list = conceptAssertionList intermediateAbr
                  c1Assertion = CAssert c1 individual
                  c2Assertion = CAssert c2 individual
                  c1InList = c1Assertion `elem` concept_assertion_list
                  listAfterCheckingC1 = if c1InList then concept_assertion_list else c1Assertion : concept_assertion_list
                  c2InList = c2Assertion `elem` listAfterCheckingC1
                  listAfterCheckingC2 = if c2InList then listAfterCheckingC1 else c2Assertion : listAfterCheckingC1
               in (ABR (relationMapping intermediateAbr) listAfterCheckingC2, not (c1InList && c2InList))
            _ -> (intermediateAbr, applied)
        )
        runningRecord
        (conceptAssertionList abr)

applyAndRule :: [ABoxRecord] -> ([ABoxRecord], Bool)
applyAndRule abrs =
  case abrs of
    [] -> ([], False)
    _ ->
      let (newAbrs, appliedResults) = unzip (Prelude.map applyAndRuleForOneABox abrs)
       in (newAbrs, or appliedResults)

findOrRuleApplicable :: [Assertion] -> [Assertion] -> Maybe Assertion
findOrRuleApplicable assertionList runningList = case runningList of
  [] -> Nothing
  (a : as) -> case a of
    CAssert (Or c1 c2) individual ->
      let c1Assertion = CAssert c1 individual
          c2Assertion = CAssert c2 individual
          c1InList = c1Assertion `elem` assertionList
          c2InList = c2Assertion `elem` assertionList
       in if (not c1InList) && (not c2InList)
            then Just a
            else findOrRuleApplicable assertionList as
    _ -> findOrRuleApplicable assertionList as

applyOrRuleForOneABox :: ABoxRecord -> ([ABoxRecord], Bool)
applyOrRuleForOneABox abr =
  let assertionList = conceptAssertionList abr
      relationMap = relationMapping abr
      applicableAssertion = findOrRuleApplicable assertionList assertionList
   in case applicableAssertion of
        Nothing -> ([abr], False)
        Just (CAssert (Or c1 c2) individual) ->
          let c1Assertion = CAssert c1 individual
              c2Assertion = CAssert c2 individual
              newAbr1 = ABR relationMap (c1Assertion : assertionList)
              newAbr2 = ABR relationMap (c2Assertion : assertionList)
           in ([newAbr1, newAbr2], True)

applyOrRule :: [ABoxRecord] -> ([ABoxRecord], Bool)
applyOrRule abrs =
  case abrs of
    [] -> ([], False)
    _ ->
      let (listOfnewAbrs, appliedResults) = unzip (Prelude.map applyOrRuleForOneABox abrs)
          newAbrs = concat listOfnewAbrs
       in (newAbrs, or appliedResults)

applyForallRuleForOneABox :: ABoxRecord -> (ABoxRecord, Bool)
applyForallRuleForOneABox abr =
  let initialRecord = (abr, False)
   in Prelude.foldr
        ( \concept_assert (intermediateAbr, applied) -> case concept_assert of
            CAssert (Forall relation concept) individual ->
              let relationMap = relationMapping intermediateAbr
                  concept_assertion_list = conceptAssertionList intermediateAbr
                  maybeIndividualMap = HashMap.lookup relation relationMap
               in case maybeIndividualMap of
                    Nothing -> (intermediateAbr, applied) -- relation not found in relation map, meaning no assertion about this relation
                    Just individualMap ->
                      -- relation found, then check if `individual` has some assertions, r(individual, someone)
                      let maybeIndividualSet = HashMap.lookup individual individualMap
                       in case maybeIndividualSet of
                            Nothing -> (intermediateAbr, applied) -- no r(individual, someone) in ABox
                            Just individualSet ->
                              -- found someone, such that r(individual, someone) in ABox
                              let assertions = Prelude.map (CAssert concept) (HashSet.toList individualSet)
                                  applicableAssertions = Prelude.filter (`notElem` concept_assertion_list) assertions
                                  newConceptAssertionList = concept_assertion_list ++ applicableAssertions
                               in (ABR relationMap newConceptAssertionList, True)
            _ -> (intermediateAbr, applied)
        )
        initialRecord
        (conceptAssertionList abr)

applyForallRule :: [ABoxRecord] -> ([ABoxRecord], Bool)
applyForallRule abrs =
  case abrs of
    [] -> ([], False)
    _ ->
      let (newAbrs, appliedResults) = unzip (Prelude.map applyForallRuleForOneABox abrs)
       in (newAbrs, or appliedResults)

findOneApplicableAssertionForExistRule :: ABoxRecord -> Maybe Assertion
findOneApplicableAssertionForExistRule abr =
  let ABR relation_map assertion_list = abr
   in case assertion_list of
        [] -> Nothing
        (a : as) -> case a of
          (CAssert (Exist relation concept) individual) ->
            case HashMap.lookup relation relation_map of
              Nothing ->
                -- relation not found in relation map
                Just a
              Just individual_map ->
                -- relation found in relation map
                case HashMap.lookup individual individual_map of
                  Nothing ->
                    -- relation(individual, someone) not found in individual map
                    Just a
                  Just individual_set ->
                    -- relation(individual, someone) found in individual map
                    let assertions = Prelude.map (CAssert concept) (HashSet.toList individual_set)
                        noC = not (any (`elem` assertion_list) assertions)
                     in if noC
                          then Just a
                          else findOneApplicableAssertionForExistRule (ABR relation_map as)
          _ -> findOneApplicableAssertionForExistRule (ABR relation_map as)

applyExistRuleForOneABox :: ABoxRecord -> Int -> (ABoxRecord, Bool)
applyExistRuleForOneABox abr order =
  let newIndividual = Individual ("#" ++ showHex order "")
      maybeApplicableAssertion = findOneApplicableAssertionForExistRule abr
      concept_assertion_list = conceptAssertionList abr
      relation_map = relationMapping abr
   in case maybeApplicableAssertion of
        Nothing -> (abr, False)
        Just (CAssert (Exist relation concept) individual) ->
          let r_assertion = RAssert relation individual newIndividual
              c_assertion = CAssert concept newIndividual
              new_concept_assertion_list = c_assertion : concept_assertion_list
              new_relation_map = insertRAssertionIntoRelationMap r_assertion relation_map
           in (ABR new_relation_map new_concept_assertion_list, True)

applyExistRule :: [ABoxRecord] -> Int -> ([ABoxRecord], Bool, Int)
applyExistRule abrs counter =
  case abrs of
    [] -> ([], False, counter)
    _ ->
      let abrNum = length abrs
          seqence = [counter .. counter + abrNum -1]
          (newAbrs, appliedResults) = unzip (zipWith applyExistRuleForOneABox abrs seqence)
       in (newAbrs, or appliedResults, counter + abrNum)

applyRules :: [ABoxRecord] -> Int -> ([ABoxRecord], Bool, Int)
applyRules abrs counter =
  let (abrsAfterAndRule, appliedAndRule) = applyAndRule abrs
      (abrsAfterOrRule, appliedOrRule) = applyOrRule abrsAfterAndRule
      (abrsAfterForallRule, appliedForallRule) = applyForallRule abrsAfterOrRule
      (abrsAfterExistRule, appliedExistRule, afterCounter) = applyExistRule abrsAfterForallRule counter
   in (abrsAfterExistRule, or [appliedAndRule, appliedExistRule, appliedOrRule, appliedForallRule], afterCounter)

checkABox :: HashSet Assertion -> [Assertion] -> Bool
checkABox c_assertion_set c_assertions =
  case c_assertions of
    [] -> True
    (a : as) ->
      let CAssert concept individual = a
          negated_assertion = CAssert (negateConcept concept) individual
       in not (HashSet.member negated_assertion c_assertion_set) && checkABox (HashSet.insert a c_assertion_set) as

checkABoxes :: [ABoxRecord] -> Bool
checkABoxes = any (checkABox HashSet.empty . conceptAssertionList)

_tableauAlgorithm :: [ABoxRecord] -> Int -> ([ABoxRecord], Int)
_tableauAlgorithm abrs counter =
  let (newAbrs, anyRuleApplied, newCounter) = applyRules abrs counter
   in if anyRuleApplied
        then _tableauAlgorithm newAbrs newCounter
        else (newAbrs, newCounter)

_tableauAlgorithmForTest :: Int -> Int -> [ABoxRecord] -> Int -> ([ABoxRecord], Int)
_tableauAlgorithmForTest max_loop_num loop_count abrs counter =
  let (newAbrs, anyRuleApplied, newCounter) = applyRules abrs counter
   in if anyRuleApplied && loop_count < max_loop_num
        then _tableauAlgorithmForTest max_loop_num (loop_count + 1) newAbrs newCounter
        else (newAbrs, newCounter)

tableauAlgorithm :: ABox -> Bool
tableauAlgorithm abox =
  let aboxRecord = constructABRFromABox abox
      (finalAbrs, _) = _tableauAlgorithm [aboxRecord] 0
   in checkABoxes finalAbrs

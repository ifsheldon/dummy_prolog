module Algorithms
  ( toNNF,
  )
where

import ABox
import Data.HashMap.Strict as HashMap
import Data.HashSet as HashSet

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

addAssertionToABR :: Assertion -> ABoxRecord -> ABoxRecord
addAssertionToABR assertion abr =
  case assertion of
    RAssert relation i1 i2 ->
      let relationMap = relationMapping abr
          concept_assertion_list = conceptAssertionList abr
          newRelationMap = case HashMap.lookup relation relationMap of
            Nothing ->
              -- if relation is not in relation map
              let individualSet = HashSet.singleton i2
                  individualMap = HashMap.singleton i1 individualSet
               in HashMap.insert relation individualMap relationMap
            Just individualMap ->
              -- if relation in relation map
              case HashMap.lookup i1 individualMap of
                Nothing ->
                  -- if i1 not in individual map
                  let individualSet = HashSet.singleton i2
                      newIndividualMap = HashMap.insert i1 individualSet individualMap
                   in HashMap.insert relation newIndividualMap relationMap
                Just individualSet ->
                  -- if i1 in individual map
                  let newIndividualSet = HashSet.insert i2 individualSet
                      newIndividualMap = HashMap.insert i1 newIndividualSet individualMap
                   in HashMap.insert relation newIndividualMap relationMap
       in ABR newRelationMap concept_assertion_list
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

--applyRules :: [ABoxRecord] -> ([ABoxRecord], Bool)
--applyRules abrs =
--  let (abrsAfterAndRule, appliedAndRule) = applyAndRule
--      (abrsAfterOrRule, appliedOrRule) = applyOrRule
--      (abrsAfterForallRule, appliedForallRule) = applyForallRule
--      (abrsAfterExistRule, appliedExistRule) = applyExistRule
--  in ([], False)

tableauAlgorithm :: ABox -> Bool
tableauAlgorithm abox =
  let aboxRecord = constructABRFromABox abox
   in False --TODO

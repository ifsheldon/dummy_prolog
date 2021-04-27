{-# LANGUAGE LambdaCase #-}

module Algorithms
  ( toNNF,
    constructABRFromABox,
    ABoxRecord (..),
    applyExistRule,
    applyForallRule,
    applyAndRule,
    applyOrRule,
    tableauAlgorithm,
    _tableauAlgorithmForTest,
    applyRules,
    anyOpenABoxes,
    querySubsumption,
  )
where

import ABox
import Data.Foldable (find)
import Data.HashMap.Strict as HashMap
import Data.HashSet as HashSet
import Data.List (subsequences)
import Data.Maybe (isNothing)
import Debug.Trace (trace)
import Numeric (showHex)

_trace msg arg = trace (msg ++ show arg) arg

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
      AtMost n r c -> AtLeast (n + 1) r c
      AtLeast n r c -> if n == 0 then getBottom else AtMost (n -1) r c

toNNFAssertion :: Assertion -> Assertion
toNNFAssertion assertion =
  case assertion of
    RAssert _ _ _ -> assertion
    CAssert concept individual -> CAssert (toNNF concept) individual

data ABoxRecord = ABR
  { relationMapping :: HashMap Relation (HashMap Individual (HashSet Individual)),
    conceptAssertionList :: [Assertion],
    neqSet :: HashSet Assertion
  }
  deriving (Show)

data Rule = EXIST | FORALL | OR | AND | AT_LEAST | AT_MOST | CHOOSE | NONE deriving (Eq, Show)

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
  let relation_map = relationMapping abr
      neq_set = neqSet abr
      c_assertion_list = conceptAssertionList abr
   in case assertion of
        RAssert _ _ _ -> ABR (insertRAssertionIntoRelationMap assertion relation_map) c_assertion_list neq_set
        CAssert _ _ -> ABR relation_map (assertion : c_assertion_list) neq_set
        Neq _ _ -> ABR relation_map c_assertion_list (HashSet.insert assertion neq_set)

constructABRFromABox :: ABox -> ABoxRecord
constructABRFromABox abox =
  let Abox assertionSet = abox
      nnfAssertionSet = HashSet.map toNNFAssertion assertionSet
      emptyABR = ABR HashMap.empty [] HashSet.empty
      all_individual_top_assertions =
        ( Prelude.map (CAssert getTop) . HashSet.toList . HashSet.fromList
            . concatMap
              ( \case
                  RAssert _ i1 i2 -> [i1, i2]
                  CAssert _ i -> [i]
                  Neq i1 i2 -> [i1, i2]
              )
            . HashSet.toList
        )
          assertionSet
      new_abr = HashSet.foldr addAssertionToABR emptyABR nnfAssertionSet
   in ABR (relationMapping new_abr) (conceptAssertionList new_abr ++ all_individual_top_assertions) (neqSet new_abr)

applyAndRuleForOneABox :: ABoxRecord -> (ABoxRecord, Bool)
applyAndRuleForOneABox abr =
  Prelude.foldr
    ( \concept_assert (intermediateAbr, ever_applied) -> case concept_assert of
        CAssert (And c1 c2) individual ->
          let concept_assertion_list = conceptAssertionList intermediateAbr
              c1Assertion = CAssert c1 individual
              c2Assertion = CAssert c2 individual
              c1InList = c1Assertion `elem` concept_assertion_list
              listAfterCheckingC1 = if c1InList then concept_assertion_list else c1Assertion : concept_assertion_list
              c2InList = c2Assertion `elem` listAfterCheckingC1
              listAfterCheckingC2 = if c2InList then listAfterCheckingC1 else c2Assertion : listAfterCheckingC1
           in (ABR (relationMapping intermediateAbr) listAfterCheckingC2 (neqSet intermediateAbr), ever_applied || not (c1InList && c2InList))
        _ -> (intermediateAbr, ever_applied)
    )
    (abr, False)
    (conceptAssertionList abr)

applyAndRule :: [ABoxRecord] -> ([ABoxRecord], Bool)
applyAndRule abrs =
  case abrs of
    [] -> ([], False)
    _ ->
      let (newAbrs, appliedResults) = unzip (Prelude.map applyAndRuleForOneABox abrs)
       in (newAbrs, or appliedResults)

findOrRuleApplicable :: [Assertion] -> Maybe Assertion
findOrRuleApplicable assertion_list =
  find
    ( \case
        CAssert (Or c1 c2) individual ->
          let c1Assertion = CAssert c1 individual
              c2Assertion = CAssert c2 individual
              is_not_top = getTop /= Or c1 c2
              c1InList = c1Assertion `elem` assertion_list
              c2InList = c2Assertion `elem` assertion_list
           in is_not_top && not c1InList && not c2InList
        _ -> False
    )
    assertion_list

applyOrRuleForOneABox :: ABoxRecord -> ([ABoxRecord], Bool)
applyOrRuleForOneABox abr =
  let assertionList = conceptAssertionList abr
      relationMap = relationMapping abr
      applicableAssertion = findOrRuleApplicable assertionList
   in case applicableAssertion of
        Nothing -> ([abr], False)
        Just (CAssert (Or c1 c2) individual) ->
          let c1Assertion = CAssert c1 individual
              c2Assertion = CAssert c2 individual
              newAbr1 = ABR relationMap (c1Assertion : assertionList) (neqSet abr)
              newAbr2 = ABR relationMap (c2Assertion : assertionList) (neqSet abr)
           in ([newAbr1, newAbr2], True)

applyOrRule :: [ABoxRecord] -> ([ABoxRecord], Bool)
applyOrRule abrs =
  case abrs of
    [] -> ([], False)
    _ ->
      let (listOfNewAbrs, appliedResults) = unzip (Prelude.map applyOrRuleForOneABox abrs)
          newAbrs = concat listOfNewAbrs
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
                               in (ABR relationMap newConceptAssertionList (neqSet intermediateAbr), not (Prelude.null applicableAssertions))
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
findOneApplicableAssertionForExistRule (ABR relation_map assertion_list _) =
  find
    ( \case
        (CAssert (Exist relation concept) individual) ->
          case HashMap.lookup relation relation_map of
            Nothing -> True -- relation not found in relation map
            Just individual_map ->
              -- relation found in relation map
              case HashMap.lookup individual individual_map of
                Nothing -> True -- relation(individual, someone) not found in individual map
                Just individual_set ->
                  -- relation(individual, someone) found in individual map
                  let assertions = Prelude.map (CAssert concept) (HashSet.toList individual_set)
                   in not (any (`elem` assertion_list) assertions)
        _ -> False
    )
    assertion_list

applyExistRuleForOneABox :: ABoxRecord -> Int -> (ABoxRecord, Bool)
applyExistRuleForOneABox abr order =
  let newIndividual = Individual ("#E-" ++ showHex order "")
      concept_assertion_list = conceptAssertionList abr
      maybeApplicableAssertion = findOneApplicableAssertionForExistRule abr
      relation_map = relationMapping abr
   in case maybeApplicableAssertion of
        Nothing -> (abr, False)
        Just (CAssert (Exist relation concept) individual) ->
          let r_assertion = RAssert relation individual newIndividual
              c_assertion = CAssert concept newIndividual
              top_assertion = CAssert getTop newIndividual
              new_concept_assertion_list = top_assertion : c_assertion : concept_assertion_list
              new_relation_map = insertRAssertionIntoRelationMap r_assertion relation_map
           in (ABR new_relation_map new_concept_assertion_list (neqSet abr), True)

applyExistRule :: [ABoxRecord] -> Int -> ([ABoxRecord], Bool, Int)
applyExistRule abrs counter =
  case abrs of
    [] -> ([], False, counter)
    _ ->
      let abrNum = length abrs
          count_num_sequence = [counter .. counter + abrNum -1]
          (newAbrs, appliedResults) = unzip (zipWith applyExistRuleForOneABox abrs count_num_sequence)
       in (newAbrs, or appliedResults, counter + abrNum)

findQualifiedIndividualsForAtLeastRule :: [Individual] -> Int -> HashSet Assertion -> Maybe [Individual]
findQualifiedIndividualsForAtLeastRule individuals num neq_set =
  let individual_sublists = if length individuals == num then [individuals] else Prelude.filter ((num ==) . length) (subsequences individuals)
   in find
        ( \indivs ->
            let all_neqs = (HashSet.fromList . Prelude.map (uncurry Neq) . genIndividualCombinations) indivs
             in all_neqs `isSubsetOf` neq_set
        )
        individual_sublists

applyAtLeastRuleForOneABox :: ABoxRecord -> Int -> (ABoxRecord, Bool, Int)
applyAtLeastRuleForOneABox abr counter =
  let neq_set = neqSet abr
      relation_map = relationMapping abr
      cassertions = conceptAssertionList abr
      maybeSuitableAtLeastAssertion =
        find
          ( \case
              CAssert (AtLeast n r c) a ->
                case HashMap.lookup r relation_map of
                  Nothing -> True
                  Just individual_map ->
                    case HashMap.lookup a individual_map of
                      Nothing -> True
                      Just individual_set ->
                        HashSet.size individual_set < n || (HashSet.size in_casserions_individuals < n) || isNothing maybeQualifiedIndividuals
                        where
                          in_casserions_individuals = HashSet.filter ((`elem` cassertions) . (CAssert c)) individual_set
                          maybeQualifiedIndividuals = findQualifiedIndividualsForAtLeastRule (HashSet.toList in_casserions_individuals) n neq_set
              _ -> False
          )
          cassertions
   in case maybeSuitableAtLeastAssertion of
        Nothing -> (abr, False, counter)
        Just (CAssert (AtLeast n r c) a) ->
          let new_counter = counter + n
              new_individuals = Prelude.map (\order -> Individual ("#AL" ++ showHex order "")) [counter .. new_counter -1]
              new_top_assertions = Prelude.map (CAssert getTop) new_individuals
              new_relation_assertions = Prelude.map (RAssert r a) new_individuals
              new_concept_assertions = Prelude.map (CAssert c) new_individuals
              new_neqs = (Prelude.map (uncurry Neq) . genIndividualCombinations) new_individuals
              new_cassertions = cassertions ++ new_concept_assertions ++ new_top_assertions
              new_neq_set = HashSet.union neq_set (HashSet.fromList new_neqs)
              new_relation_map = Prelude.foldr insertRAssertionIntoRelationMap relation_map new_relation_assertions
           in (ABR new_relation_map new_cassertions new_neq_set, True, new_counter)

applyAtLeastRule :: [ABoxRecord] -> Int -> ([ABoxRecord], Bool, Int)
applyAtLeastRule abrs counter =
  Prelude.foldr
    ( \abr (intermediate_abrs, ever_applied, running_counter) ->
        let (new_abr, applied, new_counter) = applyAtLeastRuleForOneABox abr running_counter
         in (new_abr : intermediate_abrs, applied || ever_applied, new_counter)
    )
    ([], False, counter)
    abrs

replaceIndividual :: (Individual, Individual) -> Individual -> Individual
replaceIndividual (original, replacement) x = if x == original then replacement else x

relationMapToRAssertions :: HashMap Relation (HashMap Individual (HashSet Individual)) -> [Assertion]
relationMapToRAssertions relation_map =
  let relation_list = HashMap.toList relation_map
   in concatMap
        ( \(relation, individual_map) ->
            concatMap
              (\(individual, individual_set) -> Prelude.map (RAssert relation individual) (HashSet.toList individual_set))
              (HashMap.toList individual_map)
        )
        relation_list

replaceIndividualInRelationMap :: HashMap Relation (HashMap Individual (HashSet Individual)) -> (Individual, Individual) -> HashMap Relation (HashMap Individual (HashSet Individual))
replaceIndividualInRelationMap relation_map (original, replacement) =
  let replace_individual = replaceIndividual (original, replacement)
      replace_individuals_in_r_assertion = (\(RAssert r i1 i2) -> RAssert r (replace_individual i1) (replace_individual i2))
      original_r_assertions = relationMapToRAssertions relation_map -- reconstruct RAssertions
      new_r_assertions = Prelude.map replace_individuals_in_r_assertion original_r_assertions
   in Prelude.foldr insertRAssertionIntoRelationMap HashMap.empty new_r_assertions -- construct new relation map

replaceIndividualInABox :: ABoxRecord -> (Individual, Individual) -> ABoxRecord
replaceIndividualInABox originalAbr (original, replacement) =
  let replace_individual = replaceIndividual (original, replacement)
      new_neq_set = HashSet.map (\(Neq i1 i2) -> Neq (replace_individual i1) (replace_individual i2)) (neqSet originalAbr)
      new_cassertion_list = (HashSet.toList . HashSet.fromList . Prelude.map (\(CAssert c i) -> CAssert c (replace_individual i))) (conceptAssertionList originalAbr)
      new_relation_map = replaceIndividualInRelationMap (relationMapping originalAbr) (original, replacement)
   in ABR new_relation_map new_cassertion_list new_neq_set

findQualifiedIndividualsForAtMostRule :: [Individual] -> Int -> HashSet Assertion -> Maybe [Individual]
findQualifiedIndividualsForAtMostRule individuals num neq_set =
  let individual_sublists = if length individuals == num then [individuals] else Prelude.filter ((num ==) . length) (subsequences individuals)
   in find
        ( \indivs ->
            let all_neqs = (HashSet.fromList . Prelude.map (uncurry Neq) . genIndividualCombinations) indivs
             in not (all_neqs `isSubsetOf` neq_set)
        )
        individual_sublists

findSuitableForAtMostRule :: ABoxRecord -> [Assertion] -> Maybe [Individual]
findSuitableForAtMostRule abr running_list =
  case running_list of
    [] -> Nothing
    (a : as) -> case a of
      (CAssert (AtMost n r c) individual) ->
        let relation_map = relationMapping abr
            neq_set = neqSet abr
            cassertions = conceptAssertionList abr
         in case HashMap.lookup r relation_map of
              Nothing -> findSuitableForAtMostRule abr as
              Just individual_map -> case HashMap.lookup individual individual_map of
                Nothing -> findSuitableForAtMostRule abr as
                Just individual_set ->
                  let in_cassertions_individuals = HashSet.filter (\x -> CAssert c x `elem` cassertions) individual_set
                      qualified_individuals = findQualifiedIndividualsForAtMostRule (HashSet.toList in_cassertions_individuals) (n + 1) neq_set
                   in if HashSet.size individual_set < n + 1 || HashSet.size in_cassertions_individuals < n + 1
                        then findSuitableForAtMostRule abr as
                        else case qualified_individuals of
                          Nothing -> findSuitableForAtMostRule abr as
                          Just suitable_individuals -> Just suitable_individuals
      _ -> findSuitableForAtMostRule abr as

genIndividualCombinations :: [Individual] -> [(Individual, Individual)]
genIndividualCombinations individuals =
  Prelude.map (\x -> (x !! 0, x !! 1)) (Prelude.filter ((2 ==) . length) (subsequences individuals))

applyAtMostRuleForOneABox :: ABoxRecord -> ([ABoxRecord], Bool)
applyAtMostRuleForOneABox abr =
  case findSuitableForAtMostRule abr (conceptAssertionList abr) of
    Nothing -> ([abr], False)
    Just suitable_individuals ->
      let combinations = genIndividualCombinations suitable_individuals
          new_abrs =
            Prelude.map
              ( \(i1, i2) ->
                  let Individual i1_name = i1
                      Individual i2_name = i2
                      replacement = Individual (i1_name ++ "+" ++ i2_name)
                      after_replace_i1 = replaceIndividualInABox abr (i1, replacement)
                   in replaceIndividualInABox after_replace_i1 (i2, replacement)
              )
              combinations
       in (new_abrs, True)

applyAtMostRule :: [ABoxRecord] -> ([ABoxRecord], Bool)
applyAtMostRule abrs =
  let (new_abrs_list, applied_results) = unzip (Prelude.map applyAtMostRuleForOneABox abrs)
   in (concat new_abrs_list, or applied_results)

findSuitableIndividualForChooseRule :: ABoxRecord -> [Assertion] -> Maybe (Concept, Individual)
findSuitableIndividualForChooseRule abr running_list =
  case running_list of
    [] -> Nothing
    (a : as) ->
      case a of
        CAssert (AtMost _ r c) individual ->
          let relation_map = relationMapping abr
              cassertions = conceptAssertionList abr
              individual_suitable =
                ( \b ->
                    let cb = CAssert c b
                        ncb = CAssert (negateConcept c) b
                     in cb `notElem` cassertions && ncb `notElem` cassertions
                )
           in case HashMap.lookup r relation_map of
                Nothing -> findSuitableIndividualForChooseRule abr as -- cannot find r in relation map
                Just individual_map ->
                  case HashMap.lookup individual individual_map of
                    Nothing -> findSuitableIndividualForChooseRule abr as -- found r but r(a, sth) is not found
                    Just individual_set ->
                      -- found r and found r(a, sth)
                      case find individual_suitable individual_set of
                        Nothing -> findSuitableIndividualForChooseRule abr as -- not found suitable individual
                        Just b -> Just (c, b) -- found one
        _ -> findSuitableIndividualForChooseRule abr as

applyChooseRuleForOneABox :: ABoxRecord -> ([ABoxRecord], Bool)
applyChooseRuleForOneABox abr =
  let cassertions = conceptAssertionList abr
      relation_map = relationMapping abr
      maybeApplicableAssertion = findSuitableIndividualForChooseRule abr cassertions
   in case maybeApplicableAssertion of
        Nothing -> ([abr], False)
        Just (concept, individual) ->
          let cb = CAssert concept individual
              ncb = CAssert (negateConcept concept) individual
              newABR1 = ABR relation_map (cb : cassertions) (neqSet abr)
              newABR2 = ABR relation_map (ncb : cassertions) (neqSet abr)
           in ([newABR1, newABR2], True)

applyChooseRule :: [ABoxRecord] -> ([ABoxRecord], Bool)
applyChooseRule abrs = case abrs of
  [] -> ([], False)
  _ ->
    let (listOfNewAbrs, appliedResults) = unzip (Prelude.map applyChooseRuleForOneABox abrs)
     in (concat listOfNewAbrs, or appliedResults)

applyRules :: [ABoxRecord] -> Int -> ([ABoxRecord], Rule, Int)
applyRules abrs counter
  | andRuleApplicable = (abrsAfterAndRule, AND, counter)
  | forallRuleApplicable = (abrsAfterForallRule, FORALL, counter)
  | orRuleApplicable = (abrsAfterOrRule, OR, counter)
  | chooseRuleApplicable = (abrsAfterChooseRule, CHOOSE, counter)
  | atMostRuleApplicable = (abrsAfterAtMostRule, AT_MOST, counter)
  | atLeastRuleApplicable = (abrsAfterAtLeastRule, AT_LEAST, newCounterAfterAtLeastRule)
  | existRuleApplicable = (abrsAfterExistRule, EXIST, newCounterAfterExistRule)
  | otherwise = (abrs, NONE, counter)
  where
    (abrsAfterAndRule, andRuleApplicable) = applyAndRule abrs
    (abrsAfterOrRule, orRuleApplicable) = applyOrRule abrs
    (abrsAfterForallRule, forallRuleApplicable) = applyForallRule abrs
    (abrsAfterChooseRule, chooseRuleApplicable) = applyChooseRule abrs
    (abrsAfterExistRule, existRuleApplicable, newCounterAfterExistRule) = applyExistRule abrs counter
    (abrsAfterAtMostRule, atMostRuleApplicable) = applyAtMostRule abrs
    (abrsAfterAtLeastRule, atLeastRuleApplicable, newCounterAfterAtLeastRule) = applyAtLeastRule abrs counter

noConflictConceptAssertions :: HashSet Assertion -> [Assertion] -> Bool
noConflictConceptAssertions c_assertion_set c_assertions =
  case c_assertions of
    [] -> True
    (a : as) ->
      let CAssert concept individual = a
          negated_assertion = CAssert (negateConcept concept) individual
       in not (HashSet.member negated_assertion c_assertion_set) && noConflictConceptAssertions (HashSet.insert a c_assertion_set) as

noNumberContradictions :: ABoxRecord -> [Assertion] -> Bool
noNumberContradictions abr running_list =
  case running_list of
    [] -> True
    (a : as) -> case a of
      (CAssert (AtMost n r c) individual) ->
        case HashMap.lookup r (relationMapping abr) of
          Nothing -> noNumberContradictions abr as
          Just individual_map -> case HashMap.lookup individual individual_map of
            Nothing -> noNumberContradictions abr as
            Just individual_set ->
              let in_cassertions_individuals = HashSet.filter (\b -> (CAssert c b) `elem` (conceptAssertionList abr)) individual_set
                  in_set_neqs = (Prelude.filter (`HashSet.member` neqSet abr) . Prelude.map (uncurry Neq) . genIndividualCombinations . HashSet.toList) in_cassertions_individuals
                  (individual_list1, individual_list2) = (unzip . Prelude.map (\(Neq i1 i2) -> (i1, i2))) in_set_neqs
                  qualified_individuals = HashSet.fromList (individual_list1 ++ individual_list2)
                  special_case_when_n_is_0 = n == 0 && HashSet.size in_cassertions_individuals > 0
               in not special_case_when_n_is_0 && (HashSet.size individual_set <= n || HashSet.size in_cassertions_individuals <= n || HashSet.size qualified_individuals <= n) && noNumberContradictions abr as
      _ -> noNumberContradictions abr as

isOpenABox :: ABoxRecord -> Bool
isOpenABox abr =
  let no_a_neq_a = not (any (\(Neq i1 i2) -> i1 == i2) (neqSet abr))
      no_concept_assertion_conflicts = noConflictConceptAssertions HashSet.empty (conceptAssertionList abr)
      no_number_contradictions = noNumberContradictions abr (conceptAssertionList abr)
   in no_a_neq_a && no_concept_assertion_conflicts && no_number_contradictions

anyOpenABoxes :: [ABoxRecord] -> Bool
anyOpenABoxes = any isOpenABox -- if find any open ABox, return True for being consistent

_tableauAlgorithm :: [ABoxRecord] -> Int -> ([ABoxRecord], Int)
_tableauAlgorithm abrs counter =
  let (newAbrs, appliedRule, newCounter) = applyRules abrs counter
   in if appliedRule == NONE
        then (newAbrs, newCounter)
        else _tableauAlgorithm newAbrs newCounter

_tableauAlgorithmForTest :: Int -> Int -> [ABoxRecord] -> Int -> ([ABoxRecord], Int, Bool)
_tableauAlgorithmForTest max_loop_num loop_count abrs counter =
  let (newAbrs, ar, newCounter) = applyRules abrs counter
      appliedRule = _trace "applied rule " ar
   in if appliedRule /= NONE && loop_count < max_loop_num
        then _tableauAlgorithmForTest max_loop_num (loop_count + 1) newAbrs newCounter
        else (newAbrs, newCounter, loop_count >= max_loop_num)

tableauAlgorithm :: ABox -> Bool
tableauAlgorithm abox =
  let aboxRecord = constructABRFromABox abox
      (finalAbrs, _) = _tableauAlgorithm [aboxRecord] 0
   in anyOpenABoxes finalAbrs

querySubsumption :: [Concept] -> Concept -> Bool
querySubsumption concepts query =
  let with_query_concepts = negateConcept query : concepts
      assertion_set = HashSet.fromList (Prelude.map (\concept -> CAssert concept (Individual "a")) with_query_concepts)
      abox = Abox assertion_set
   in not (tableauAlgorithm abox) -- if the ABox is inconsistent, return true

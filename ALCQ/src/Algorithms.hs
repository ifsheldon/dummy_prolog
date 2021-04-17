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

tableauAlgorithm :: ABox -> Bool
tableauAlgorithm abox =
  let aboxRecord = constructABRFromABox abox
   in False --TODO

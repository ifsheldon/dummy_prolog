module Algorithms
  ( toNNF,
  )
where

import ABox

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

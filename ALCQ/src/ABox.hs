module ABox
  ( Individual (..),
    Relation (..),
    Concept (..),
    Assertion (..),
    ABox (..),
    TBox (..),
    getTop,
    getBottom,
  )
where

import Data.HashSet as HashSet
import Data.Hashable

data Individual = Individual [Char] deriving (Show, Eq)

instance Hashable Individual where
  hashWithSalt salt individual =
    let (Individual name) = individual
     in hashWithSalt salt name

data Relation = Relation [Char] deriving (Show, Eq)

instance Hashable Relation where
  hashWithSalt salt relation = hashWithSalt salt name where (Relation name) = relation

data Concept
  = Primitive [Char]
  | Not Concept
  | And Concept Concept
  | Or Concept Concept
  | Imply Concept Concept
  | Equiv Concept Concept
  | Forall Relation Concept
  | Exist Relation Concept
  | AtLeast Int Relation Concept
  | AtMost Int Relation Concept
  deriving (Show)

_INTERNAL_CONCEPT = Primitive "INTERNAL"

getTop = Or _INTERNAL_CONCEPT (Not _INTERNAL_CONCEPT)

getBottom = And _INTERNAL_CONCEPT (Not _INTERNAL_CONCEPT)

instance Eq Concept where
  c1 == c2 = case (c1, c2) of
    (Not sc1, Not sc2) -> sc1 == sc2
    (And sc11 sc12, And sc21 sc22) -> (sc11 == sc21 && sc12 == sc22) || (sc11 == sc22 && sc12 == sc21)
    (Or sc11 sc12, Or sc21 sc22) -> (sc11 == sc21 && sc12 == sc22) || (sc11 == sc22 && sc12 == sc21)
    (Equiv sc11 sc12, Equiv sc21 sc22) -> (sc11 == sc21 && sc12 == sc22) || (sc11 == sc22 && sc12 == sc21)
    (Imply sc11 sc12, Imply sc21 sc22) -> sc11 == sc21 && sc12 == sc22
    (Primitive name1, Primitive name2) -> name1 == name2
    (Forall r1 sc1, Forall r2 sc2) -> r1 == r2 && sc1 == sc2
    (Exist r1 sc1, Exist r2 sc2) -> r1 == r2 && sc1 == sc2
    (AtLeast n1 r1 sc1, AtLeast n2 r2 sc2) -> n1 == n2 && r1 == r2 && sc1 == sc2
    (AtMost n1 r1 sc1, AtMost n2 r2 sc2) -> n1 == n2 && r1 == r2 && sc1 == sc2
    _ -> False

instance Hashable Concept where
  hashWithSalt salt concept =
    let saltedHashC = hashWithSalt salt
        saltedHashS = hashWithSalt salt
     in case concept of
          And c1 c2 -> saltedHashC c1 + saltedHashC c2
          Or c1 c2 -> saltedHashC c1 + saltedHashC c2
          Not c -> saltedHashS "Not" + saltedHashC c
          Imply _ _ -> saltedHashS (show concept) -- TODO: fix this
          Equiv c1 c2 -> saltedHashS "Equiv" + saltedHashC c1 + saltedHashC c2 -- TODO: fix this
          Primitive name -> saltedHashS name
          Exist r c -> hashWithSalt salt r + saltedHashC c + saltedHashS "Exist"
          Forall r c -> hashWithSalt salt r + saltedHashC c + saltedHashS "Forall"
          AtLeast n r c -> hashWithSalt salt n + hashWithSalt salt r + saltedHashC c + saltedHashS "AtLeast"
          AtMost n r c -> hashWithSalt salt n + hashWithSalt salt r + saltedHashC c + saltedHashS "AtMost"

data Assertion = RAssert Relation Individual Individual | CAssert Concept Individual deriving (Show, Eq)

instance Hashable Assertion where
  hashWithSalt salt assertion = case assertion of
    RAssert r i1 i2 -> hashWithSalt salt r + hashWithSalt salt i1 + hashWithSalt salt i2 * 3
    CAssert c i -> hashWithSalt salt c + hashWithSalt salt i

data ABox = Abox (HashSet Assertion)

data TBox = Tbox (HashSet Concept)

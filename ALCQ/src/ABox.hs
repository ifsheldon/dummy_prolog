module ABox
  ( Individual (..),
    Relation (..),
    Concept (..),
    Assertion (..),
  )
where

import Data.Hashable
import Data.HashSet as HashSet

data Individual = Individual [Char] deriving (Show)

instance Eq Individual where
  i1 == i2 =
    let (Individual name1) = i1
        (Individual name2) = i2
     in name1 == name2

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
  deriving (Show, Eq)

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

data Assertion = RAssert Relation Individual Individual | CAssert Concept Individual deriving (Show, Eq)

instance Hashable Assertion where
  hashWithSalt salt assertion = case assertion of
    RAssert r i1 i2 -> hashWithSalt salt r + hashWithSalt salt i1 + hashWithSalt salt i2 * 3
    CAssert c i -> hashWithSalt salt c + hashWithSalt salt i
    
data ABox = Abox (HashSet Assertion)

data Tbox = Tbox (HashSet Concept)
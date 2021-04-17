module ABox where

import Data.Hashable

data Individual = Individual [Char] [Char] deriving (Show)

instance Eq Individual where
  i1 == i2 =
    let (Individual name1 interpretationName1) = i1
        (Individual name2 interpretationName2) = i2
     in interpretationName1 == interpretationName2

data Relation = Relation [Char] deriving (Show, Eq)

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

data Assertion = RAssertion

module Main where

import ABox
import Algorithms
import Data.HashSet as HashSet

main :: IO ()
main =
  do
    let attendedBy = Relation "attendedBy"
    let smart = Primitive "Smart"
    let studious = Primitive "Studious"
    let a = Individual "a"
    let good_student = And smart studious
    let attendedBySmart = Exist attendedBy smart
    let attendedByStudious = Exist attendedBy studious
    let attendedByGoodStudent = Exist attendedBy good_student
    let abox_concept = (And (And attendedBySmart attendedByStudious) (Not attendedByGoodStudent))
    let abox_assertion = CAssert abox_concept a
    let abox = Abox (HashSet.singleton abox_assertion)
    let abr = constructABRFromABox abox
    print abr
    print "---------------------------------"
    let (finalAbr, _, forcedStop) = _tableauAlgorithmForTest 20 0 [abr] 0
    print ("Forced stop = " ++ show forcedStop)
    print finalAbr
    print "---------------------------------"

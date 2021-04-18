module Main where

import ABox
import Algorithms
import Data.HashSet as HashSet

main :: IO ()
main =
  do
    -- Good student example
    let attendedBy = Relation "attendedBy"
    let smart = Primitive "Smart"
    let studious = Primitive "Studious"
    let individual_a = Individual "a"
    let good_student = And smart studious
    let attendedBySmart = Exist attendedBy smart
    let attendedByStudious = Exist attendedBy studious
    let attendedByGoodStudent = Exist attendedBy good_student
    let abox_concept = (And (And attendedBySmart attendedByStudious) (Not attendedByGoodStudent))
    let abox_assertion = CAssert abox_concept individual_a
    let abox = Abox (HashSet.singleton abox_assertion)
    let abr = constructABRFromABox abox
    print abr
    let (finalAbr, _, forcedStop) = _tableauAlgorithmForTest 20 0 [abr] 0
    let exist_open_abox = checkABoxes finalAbr
    print "---------------------------------"
    print ("Forced stop = " ++ show forcedStop)
    print finalAbr
    print ("Exist one open ABox = " ++ show exist_open_abox)
    print "---------------------------------"
    -- Task 3 Point 1
    let s = Relation "s"
    let r = Relation "r"
    let a = Primitive "A"
    let b = Primitive "B"
    let c = Primitive "C"
    let forall_r_forall_s_a = Forall r (Forall s a)
    let exist_r_forall_s_b = Forall r (Forall s b)
    let forall_r_exist_s_c = Forall r (Exist s c)
    let exist_r_exist_s_a_b_c = Exist r (Exist s (a `And` b `And` c))
    let concept_list1 = [forall_r_forall_s_a, exist_r_forall_s_b, forall_r_exist_s_c]
    let subsumed_result1 = querySubsumption concept_list1 exist_r_exist_s_a_b_c
    print subsumed_result1
    -- Task 3 Point 2
    -- FIXME: see why False, bug here
    let exist_r_forall_s_not_a_or_forall_r_exist_s_b = Exist r (Forall s (Not a)) `Or` Forall r (Exist s b)
    let query2 = Forall r (Exist s (a `And` b)) `Or` Exist r (Forall s (Not b))
    let concept_list2 = [forall_r_forall_s_a, exist_r_forall_s_not_a_or_forall_r_exist_s_b]
    let subsumed_result2 = querySubsumption concept_list2 query2
    print subsumed_result2

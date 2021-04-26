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
    let exist_open_abox = anyOpenABoxes finalAbr
    print "\n---------------------------------"
    print "Good Student Example"
    print ("Forced stop = " ++ show forcedStop)
    print finalAbr
    print ("Exist one open ABox = " ++ show exist_open_abox)
    print "\n---------------------------------"
    -- Task 3 Point 1
    let s = Relation "s"
    let r = Relation "r"
    let a = Primitive "A"
    let b = Primitive "B"
    let c = Primitive "C"
    let forall_r_forall_s_a = Forall r (Forall s a)
    let exist_r_forall_s_b = Exist r (Forall s b)
    let forall_r_exist_s_c = Forall r (Exist s c)
    let exist_r_exist_s_a_b_c = Exist r (Exist s (a `And` b `And` c))
    let concept_list1 = [forall_r_forall_s_a, exist_r_forall_s_b, forall_r_exist_s_c]
    let subsumed_result1 = querySubsumption concept_list1 exist_r_exist_s_a_b_c
    print "\n---------------------------------"
    print "Task 3 a. in Assignment 2"
    print ("Subsumed? " ++ show subsumed_result1)
    print "\n---------------------------------"
    -- Task 3 Point 2
    let exist_r_forall_s_not_a_or_forall_r_exist_s_b = Exist r (Forall s (Not a)) `Or` Forall r (Exist s b)
    let query2 = Forall r (Exist s (a `And` b)) `Or` Exist r (Forall s (Not b))
    let concept_list2 = [forall_r_forall_s_a, exist_r_forall_s_not_a_or_forall_r_exist_s_b]
    let subsumed_result2 = querySubsumption concept_list2 query2
    print "\n---------------------------------"
    print "Task 3 b. in Assignment 2"
    print ("Subsumed? " ++ show subsumed_result2)
    print "\n---------------------------------"

    -- worksheet 3 q2
    let individual_b = Individual "b"
    let individual_c = Individual "c"
    let individual_d = Individual "d"
    let r_a_b = RAssert r individual_a individual_b
    let r_b_d = RAssert r individual_b individual_d
    let r_d_c = RAssert r individual_d individual_c
    let r_a_c = RAssert r individual_a individual_c
    let r_c_d = RAssert r individual_c individual_d
    let cassert_A_d = CAssert a individual_d
    let query_concept = Exist r ((a `And` Exist r a) `Or` (Not a `And` Exist r (Exist r (Not a))))
    let negated_query_concept = Not query_concept
    let query_assertion = CAssert negated_query_concept individual_a
    let abox1 = Abox (HashSet.fromList [r_a_b, r_b_d, r_d_c, r_a_c, r_c_d, cassert_A_d, query_assertion])
    let abr1 = constructABRFromABox abox1
    print abr1
    let (finalAbr1, _, forcedStop1) = _tableauAlgorithmForTest 100 0 [abr1] 0
    let exist_open_abox1 = anyOpenABoxes finalAbr1
    print "\n---------------------------------"
    print "Worksheet 3 Q2"
    print ("Forced stop = " ++ show forcedStop1)
    print finalAbr1
    print ("Exist one open ABox = " ++ show exist_open_abox1)
    print ("a is an instance of the concept w.r.t A: " ++ show (not exist_open_abox1))
    print "\n---------------------------------"

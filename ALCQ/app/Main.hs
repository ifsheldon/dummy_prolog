module Main where

import ABox
import Algorithms
import Data.HashSet as HashSet
import Data.List (subsequences)

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
    let abox_concept = And (And attendedBySmart attendedByStudious) (Not attendedByGoodStudent)
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
    -- Example: at least 3 child, at most 1 female, at most 1 not female
    let hasChild = Relation "hasChild"
    let female = Primitive "Female"
    let not_female = Not female
    let at_least_3_child = AtLeast 3 hasChild getTop
    let at_most_1_female = AtMost 1 hasChild female
    let at_most_1_not_female = AtMost 1 hasChild not_female
    let someone = Individual "someone"
    let query_assertion2 = CAssert (at_least_3_child `And` at_most_1_female `And` at_most_1_not_female) someone
    let abr2 = constructABRFromABox (Abox (HashSet.singleton query_assertion2))
    print abr2
    let (finalAbr2, _, forcedStop2) = _tableauAlgorithmForTest 20 0 [abr2] 0
    let exist_open_abox2 = anyOpenABoxes finalAbr2
    print "\n---------------------------------"
    print "Example: at least 3 child, at most 1 female, at most 1 not female"
    print ("Forced stop = " ++ show forcedStop2)
    print finalAbr2
    print ("Exist one open ABox = " ++ show exist_open_abox2)
    print "\n---------------------------------"
    -- Example: abox = { P(a), AtMost(1,r,P)(a), Exists(r,P)(a), ForAll(r, Exists(r, P))(a), r(a,a) }
    let p = Primitive "P"
    let p_a = CAssert p individual_a
    let at_most_1_r_p_a = CAssert (AtMost 1 r p) individual_a
    let exist_r_p_a = CAssert (Exist r p) individual_a
    let r_a_a = RAssert r individual_a individual_a
    let forall_r_exist_r_p_a = CAssert (Forall r (Exist r p)) individual_a
    let abr3 = constructABRFromABox (Abox (HashSet.fromList [p_a, at_most_1_r_p_a, exist_r_p_a, r_a_a, forall_r_exist_r_p_a]))
    print abr2
    let (finalAbr3, _, forcedStop3) = _tableauAlgorithmForTest 20 0 [abr3] 0
    let exist_open_abox3 = anyOpenABoxes finalAbr3
    print "\n---------------------------------"
    print "Example: abox = { P(a), AtMost(1,r,P)(a), Exists(r,P)(a), ForAll(r, Exists(r, P))(a), r(a,a) }"
    print ("Forced stop = " ++ show forcedStop3)
    print finalAbr3
    print ("Exist one open ABox = " ++ show exist_open_abox3)
    print "\n---------------------------------"

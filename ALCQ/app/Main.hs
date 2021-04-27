module Main where

import ABox
import Algorithms
import Data.HashSet as HashSet

testAssertions assertions =
  do
    let (final_abrs, _, forced_stop) = _tableauAlgorithmForTest 50 0 [constructABRFromABox (Abox $ HashSet.fromList assertions)] 0
    let hasOpenABox = anyOpenABoxes final_abrs
    print assertions
    print ("Forced Stop = " ++ show forced_stop)
    print ("ABox Num = " ++ show (length final_abrs))
    print ("Has Open ABox = " ++ show hasOpenABox)
    print final_abrs

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
    let abox_assertions = [CAssert abox_concept individual_a]
    print "\n---------------------------------"
    print "Good Student Example"
    testAssertions abox_assertions
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
    print "\n---------------------------------"
    print "Example: at least 3 child, at most 1 female, at most 1 not female"
    testAssertions [query_assertion2]
    print "\n---------------------------------"
    -- Example: abox = { P(a), AtMost(1,r,P)(a), Exists(r,P)(a), ForAll(r, Exists(r, P))(a), r(a,a) }
    let p = Primitive "P"
    let p_a = CAssert p individual_a
    let at_most_1_r_p_a = CAssert (AtMost 1 r p) individual_a
    let exist_r_p_a = CAssert (Exist r p) individual_a
    let r_a_a = RAssert r individual_a individual_a
    let forall_r_exist_r_p_a = CAssert (Forall r (Exist r p)) individual_a
    print "\n---------------------------------"
    print "Example: abox = { P(a), AtMost(1,r,P)(a), Exists(r,P)(a), ForAll(r, Exists(r, P))(a), r(a,a) }"
    testAssertions [p_a, at_most_1_r_p_a, exist_r_p_a, r_a_a, forall_r_exist_r_p_a]
    print "\n---------------------------------"
    -- Simple example: Exist r C is equivalent to AtLeast 1 r C
    let exist_r_top = Exist r getTop
    let at_lease_1_r_top = AtLeast 1 r getTop
    let exist_subsumes_at_least = querySubsumption [exist_r_top] at_lease_1_r_top
    let at_least_subsume_exist = querySubsumption [at_lease_1_r_top] exist_r_top
    print "\n---------------------------------"
    print "Example: Exist r C is equivalent to AtLeast 1 r C"
    print ("Exist subsumes AtLeast 1? " ++ show exist_subsumes_at_least)
    print ("AtLeast 1 subsumes Exist? " ++ show at_least_subsume_exist)
    print "\n---------------------------------"
    -- Basic Examples
    let lovedBy = Relation "lovedBy"
    let hatedBy = Relation "hatedBy"
    let beloved = AtLeast 1 lovedBy getTop
    let be_hated = AtLeast 1 hatedBy getTop
    let lovedByAtMost2 = AtMost 2 lovedBy getTop
    let lovedByAtMost3 = AtMost 3 lovedBy getTop
    let lovedByAtLeast1 = AtLeast 1 lovedBy getTop
    let lovedExist = Exist lovedBy getTop
    let lovedByAll = Forall lovedBy getTop
    let hatedByAtLeast2 = AtLeast 2 hatedBy getTop
    let hatedByAtLeast3 = AtLeast 3 hatedBy getTop
    let hatedByAll = Forall hatedBy getTop
    print "\n---------------------------------"
    print ("lovedByAtMost2 subsumes lovedByAtMost3 " ++ show (querySubsumption [lovedByAtMost2] lovedByAtMost3))
    print ("lovedByAtMost3 subsumes lovedByAtMost2 " ++ show (querySubsumption [lovedByAtMost3] lovedByAtMost2))
    print ("hatedByAtLeast2 subsumes hatedByAtLeast3 " ++ show (querySubsumption [hatedByAtLeast2] hatedByAtLeast3))
    print ("hatedByAtLeast3 subsumes hatedByAtLeast2 " ++ show (querySubsumption [hatedByAtLeast3] hatedByAtLeast2))
    print ("lovedByAtMost3 subsumes hatedByAtLeast2 " ++ show (querySubsumption [lovedByAtMost3] hatedByAtLeast2))
    print "\n---------------------------------"
    -- More examples
    let parentWithMax5Children = AtMost 5 hasChild getTop
    let parentWithMax4Children = AtMost 4 hasChild getTop
    let parentWithMax3Children = AtMost 3 hasChild getTop
    let parentWithMax2Children = AtMost 2 hasChild getTop
    let parentWithMax1Children = AtMost 1 hasChild getTop
    let parentWithMax0Children = AtMost 0 hasChild getTop

    let parentWithMin5Children = AtLeast 5 hasChild getTop
    let parentWithMin4Children = AtLeast 4 hasChild getTop
    let parentWithMin3Children = AtLeast 3 hasChild getTop
    let parentWithMin2Children = AtLeast 2 hasChild getTop
    let parentWithMin1Children = AtLeast 1 hasChild getTop
    let parentWithMin0Children = AtLeast 0 hasChild getTop
    let joe = Individual "Joe"
    let ann = Individual "Ann"
    let eva = Individual "Eva"
    let mary = Individual "Mary"
    let andy = Individual "Andy"
    -- Task 4
    let task4_ABox_assertions = [RAssert hasChild joe ann, RAssert hasChild joe eva, RAssert hasChild joe mary, CAssert parentWithMax2Children joe]
    print "\n---------------------------------"
    print "Task 4"
    testAssertions task4_ABox_assertions
    print "\n---------------------------------"

    let abox_assertions_0 = [RAssert hasChild joe ann, RAssert hasChild joe eva, RAssert hasChild joe mary, RAssert hasChild joe andy]
    print "\n---------------------------------"
    print "-------"
    testAssertions abox_assertions_0
    print "-------"
    let abox_assertions_1 = CAssert parentWithMax5Children joe : abox_assertions_0
    testAssertions abox_assertions_1
    print "-------"
    let abox_assertions_2 = CAssert (Not parentWithMax5Children) joe : abox_assertions_0
    testAssertions abox_assertions_2
    print "-------"
    let abox_assertions_3 = CAssert parentWithMax4Children joe : abox_assertions_0
    testAssertions abox_assertions_3
    print "-------"
    let abox_assertions_4 = CAssert parentWithMax3Children joe : abox_assertions_0
    testAssertions abox_assertions_4
    print "-------"
    let abox_assertions_5 = CAssert parentWithMax2Children joe : abox_assertions_0
    testAssertions abox_assertions_5
    print "-------"
    let abox_assertions_6 = [CAssert parentWithMin3Children joe, Neq andy ann, Neq andy eva] ++ abox_assertions_0
    testAssertions abox_assertions_6
    print "-------"
    let abox_assertions_7 = [CAssert parentWithMin3Children joe, Neq andy ann, Neq andy eva, Neq ann eva] ++ abox_assertions_0
    testAssertions abox_assertions_7
    print "-------"
    let abox_assertions_8 = [CAssert (Not parentWithMin3Children) joe, Neq andy ann, Neq andy eva, Neq ann eva] ++ abox_assertions_0
    testAssertions abox_assertions_8
    print "-------"
    print "\n---------------------------------"

module Main where

import ABox
import Algorithms
import Data.Foldable (find)
import Data.HashSet as HashSet

reconstructABox :: ABoxRecord -> ABox
reconstructABox (ABR relation_map cassertions neq_set) =
  (Abox . HashSet.fromList) (relationMapToRAssertions relation_map ++ cassertions ++ HashSet.toList neq_set)

testAssertions assertions =
  do
    let (final_abrs, _, forced_stop) = _tableauAlgorithmForTest 50 0 [constructABRFromABox (Abox $ HashSet.fromList assertions)] 0
    let hasOpenABox = anyOpenABoxes final_abrs
    let maybeOpenABox = case find isOpenABox final_abrs of
          Nothing -> Nothing
          Just abr -> Just (reconstructABox abr)
    print ("Forced Stop = " ++ show forced_stop)
    print ("ABox Num = " ++ show (length final_abrs))
    print ("Has Open ABox = " ++ show hasOpenABox)
    --    print final_abrs
    print ("Open ABox = " ++ show maybeOpenABox)

main :: IO ()
main =
  do
    -- Task 3
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
    print ("(a). Subsumed? " ++ show subsumed_result1)
    print "\n---------------------------------"
    -- Task 3 Point 2
    let exist_r_forall_s_not_a_or_forall_r_exist_s_b = Exist r (Forall s (Not a)) `Or` Forall r (Exist s b)
    let query2 = Forall r (Exist s (a `And` b)) `Or` Exist r (Forall s (Not b))
    let concept_list2 = [forall_r_forall_s_a, exist_r_forall_s_not_a_or_forall_r_exist_s_b]
    let subsumed_result2 = querySubsumption concept_list2 query2
    print "\n---------------------------------"
    print "Task 3 b. in Assignment 2"
    print ("(b). Subsumed? " ++ show subsumed_result2)
    print "\n---------------------------------"
    -- Task 4
    let hasChild = Relation "hasChild"
    let parentWithMax2Children = AtMost 2 hasChild getTop
    let joe = Individual "Joe"
    let ann = Individual "Ann"
    let eva = Individual "Eva"
    let mary = Individual "Mary"
    let andy = Individual "Andy"
    let task4_ABox_assertions = [RAssert hasChild joe ann, RAssert hasChild joe eva, RAssert hasChild joe mary, CAssert parentWithMax2Children joe]
    print "\n---------------------------------"
    print "Task 4"
    testAssertions task4_ABox_assertions
    print "\n---------------------------------"
    -- Good student example
    let individual_a = Individual "a"
    let attendedBy = Relation "attendedBy"
    let smart = Primitive "Smart"
    let studious = Primitive "Studious"
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

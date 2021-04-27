import ABox
import Algorithms
import Data.HashSet as HashSet
import Test.Tasty
import Test.Tasty.HUnit

s = Relation "s"

r = Relation "r"

a = Primitive "A"

b = Primitive "B"

c = Primitive "C"

individual_a = Individual "a"

individual_b = Individual "b"

individual_c = Individual "c"

individual_d = Individual "d"

joe = Individual "Joe"

ann = Individual "Ann"

eva = Individual "Eva"

mary = Individual "Mary"

andy = Individual "Andy"

hasChild = Relation "hasChild"

parentWithMax5Children = AtMost 5 hasChild getTop

parentWithMax4Children = AtMost 4 hasChild getTop

parentWithMax3Children = AtMost 3 hasChild getTop

parentWithMax2Children = AtMost 2 hasChild getTop

parentWithMax1Children = AtMost 1 hasChild getTop

parentWithMax0Children = AtMost 0 hasChild getTop

parentWithMin5Children = AtLeast 5 hasChild getTop

parentWithMin4Children = AtLeast 4 hasChild getTop

parentWithMin3Children = AtLeast 3 hasChild getTop

parentWithMin2Children = AtLeast 2 hasChild getTop

parentWithMin1Children = AtLeast 1 hasChild getTop

parentWithMin0Children = AtLeast 0 hasChild getTop

testAssertions :: [ABox.Assertion] -> (Bool, Bool)
testAssertions assertions = (hasOpenABox, forced_stop)
  where
    (final_abrs, _, forced_stop) = _tableauAlgorithmForTest 50 0 [constructABRFromABox (Abox $ HashSet.fromList assertions)] 0
    hasOpenABox = anyOpenABoxes final_abrs

main :: IO ()
main =
  do
    defaultMain
      ( testGroup
          "Algorithm Tests"
          [ goodStudentExample,
            task3Example,
            worksheet3Q2,
            task4Example,
            existAtLeastExample,
            basicTestCases,
            testCase1,
            testCase2,
            testCase3,
            testCase4,
            testCase5,
            testCase6,
            testCase7,
            testCase8,
            testCase9,
            testCase10,
            testCase11
          ]
      )

goodStudentExample :: TestTree
goodStudentExample = testCase "Good Student Example" (assertEqual "Should output open world" (True, False) (testAssertions abox_assertions))
  where
    attendedBy = Relation "attendedBy"
    smart = Primitive "Smart"
    studious = Primitive "Studious"
    good_student = And smart studious
    attendedBySmart = Exist attendedBy smart
    attendedByStudious = Exist attendedBy studious
    attendedByGoodStudent = Exist attendedBy good_student
    abox_concept = And (And attendedBySmart attendedByStudious) (Not attendedByGoodStudent)
    abox_assertions = [CAssert abox_concept individual_a]

task3Example :: TestTree
task3Example = testCase "Task 3 in Assignment 2" (assertEqual "Two sub-tasks should all output True" (True, True) (subsumed_result1, subsumed_result2))
  where
    forall_r_forall_s_a = Forall r (Forall s a)
    exist_r_forall_s_b = Exist r (Forall s b)
    forall_r_exist_s_c = Forall r (Exist s c)
    exist_r_exist_s_a_b_c = Exist r (Exist s (a `And` b `And` c))
    concept_list1 = [forall_r_forall_s_a, exist_r_forall_s_b, forall_r_exist_s_c]
    subsumed_result1 = querySubsumption concept_list1 exist_r_exist_s_a_b_c
    exist_r_forall_s_not_a_or_forall_r_exist_s_b = Exist r (Forall s (Not a)) `Or` Forall r (Exist s b)
    query2 = Forall r (Exist s (a `And` b)) `Or` Exist r (Forall s (Not b))
    concept_list2 = [forall_r_forall_s_a, exist_r_forall_s_not_a_or_forall_r_exist_s_b]
    subsumed_result2 = querySubsumption concept_list2 query2

worksheet3Q2 :: TestTree
worksheet3Q2 = testCase "Worksheet 3 Q2" (assertEqual "Should output not exist open abox" (False, False) (testAssertions assertions))
  where
    r_a_b = RAssert r individual_a individual_b
    r_b_d = RAssert r individual_b individual_d
    r_d_c = RAssert r individual_d individual_c
    r_a_c = RAssert r individual_a individual_c
    r_c_d = RAssert r individual_c individual_d
    cassert_A_d = CAssert a individual_d
    query_concept = Exist r ((a `And` Exist r a) `Or` (Not a `And` Exist r (Exist r (Not a))))
    negated_query_concept = Not query_concept
    query_assertion = CAssert negated_query_concept individual_a
    assertions = [r_a_b, r_b_d, r_d_c, r_a_c, r_c_d, cassert_A_d, query_assertion]

task4Example :: TestTree
task4Example = testCase "Task 4 Example" (assertEqual "Should output exist open abox" (True, False) (testAssertions assertions))
  where
    assertions = [RAssert hasChild joe ann, RAssert hasChild joe eva, RAssert hasChild joe mary, CAssert parentWithMax2Children joe]

existAtLeastExample :: TestTree
existAtLeastExample = testCase "Test Exist r C <-> AtLeast 1 r C" (assertEqual "Should output Exist r C subsumes AtLeast 1 r C, and AtLeast 1 r C subsumes Exist r C" (True, True) (exist_subsumes_at_least, at_least_subsume_exist))
  where
    exist_r_top = Exist r getTop
    at_lease_1_r_top = AtLeast 1 r getTop
    exist_subsumes_at_least = querySubsumption [exist_r_top] at_lease_1_r_top
    at_least_subsume_exist = querySubsumption [at_lease_1_r_top] exist_r_top

basicTestCases :: TestTree
basicTestCases =
  testCase
    "Basic Cases"
    ( assertEqual
        "Basic cases should not fail"
        (True, False, False, True, False)
        ( querySubsumption [lovedByAtMost2] lovedByAtMost3,
          querySubsumption [lovedByAtMost3] lovedByAtMost2,
          querySubsumption [hatedByAtLeast2] hatedByAtLeast3,
          querySubsumption [hatedByAtLeast3] hatedByAtLeast2,
          querySubsumption [lovedByAtMost3] hatedByAtLeast2
        )
    )
  where
    lovedBy = Relation "lovedBy"
    hatedBy = Relation "hatedBy"
    lovedByAtMost2 = AtMost 2 lovedBy getTop
    lovedByAtMost3 = AtMost 3 lovedBy getTop
    hatedByAtLeast2 = AtLeast 2 hatedBy getTop
    hatedByAtLeast3 = AtLeast 3 hatedBy getTop

-- Example abox = { P(a), AtMost(1,r,P)(a), Exists(r,P)(a), ForAll(r, Exists(r, P))(a), r(a,a) }
testCase1 :: TestTree
testCase1 = testCase "Test Case 1" (assertEqual "Should output exist open abox" (True, False) (testAssertions assertions))
  where
    p = Primitive "P"
    p_a = CAssert p individual_a
    at_most_1_r_p_a = CAssert (AtMost 1 r p) individual_a
    exist_r_p_a = CAssert (Exist r p) individual_a
    r_a_a = RAssert r individual_a individual_a
    forall_r_exist_r_p_a = CAssert (Forall r (Exist r p)) individual_a
    assertions = [p_a, at_most_1_r_p_a, exist_r_p_a, r_a_a, forall_r_exist_r_p_a]

testCase2 :: TestTree
testCase2 = testCase "Test Case 2" (assertEqual "Should output exist open abox" (False, False) (testAssertions assertions))
  where
    female = Primitive "Female"
    not_female = Not female
    at_least_3_child = AtLeast 3 hasChild getTop
    at_most_1_female = AtMost 1 hasChild female
    at_most_1_not_female = AtMost 1 hasChild not_female
    someone = Individual "someone"
    assertions = [CAssert (at_least_3_child `And` at_most_1_female `And` at_most_1_not_female) someone]

assertion_base = [RAssert hasChild joe ann, RAssert hasChild joe eva, RAssert hasChild joe mary, RAssert hasChild joe andy]

testCase3 :: TestTree
testCase3 = testCase "Test Case 3" (assertEqual "Should output exist open abox" (True, False) (testAssertions assertions))
  where
    assertions = assertion_base

testCase4 :: TestTree
testCase4 = testCase "Test Case 4" (assertEqual "Should output exist open abox" (True, False) (testAssertions assertions))
  where
    assertions = CAssert parentWithMax5Children joe : assertion_base

testCase5 :: TestTree
testCase5 = testCase "Test Case 5" (assertEqual "Should output exist open abox" (True, False) (testAssertions assertions))
  where
    assertions = CAssert (Not parentWithMax5Children) joe : assertion_base

testCase6 :: TestTree
testCase6 = testCase "Test Case 6" (assertEqual "Should output exist open abox" (True, False) (testAssertions assertions))
  where
    assertions = CAssert parentWithMax4Children joe : assertion_base

testCase7 :: TestTree
testCase7 = testCase "Test Case 7" (assertEqual "Should output exist open abox" (True, False) (testAssertions assertions))
  where
    assertions = CAssert parentWithMax3Children joe : assertion_base

testCase8 :: TestTree
testCase8 = testCase "Test Case 8" (assertEqual "Should output exist open abox" (True, False) (testAssertions assertions))
  where
    assertions = CAssert parentWithMax2Children joe : assertion_base

testCase9 :: TestTree
testCase9 = testCase "Test Case 9" (assertEqual "Should output exist open abox" (True, False) (testAssertions assertions))
  where
    assertions = [CAssert parentWithMin3Children joe, Neq andy ann, Neq andy eva] ++ assertion_base

testCase10 :: TestTree
testCase10 = testCase "Test Case 10" (assertEqual "Should output exist open abox" (True, False) (testAssertions assertions))
  where
    assertions = [CAssert parentWithMin3Children joe, Neq andy ann, Neq andy eva, Neq ann eva] ++ assertion_base

testCase11 :: TestTree
testCase11 = testCase "Test Case 11" (assertEqual "Should output exist open abox" (False, False) (testAssertions assertions))
  where
    assertions = [CAssert (Not parentWithMin3Children) joe, Neq andy ann, Neq andy eva, Neq ann eva] ++ assertion_base

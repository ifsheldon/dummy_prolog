module Main where

import Algorithms
import Data.HashMap.Strict as HashMap
import Lib
import SigmaSignature
import Literals

testMGU l1 l2 = do
  let (subl1, subl2, subs) = findMGU (l1, l2, Nothing)
  print subl1
  print subl2
  print subs

main = do
  let v0 = Variable "v0"
  let v1 = Variable "v1"
  let v2 = Variable "v2"
  let p = Relation "P" 3
  let q = Relation "Q" 3
  let formula = IMPLY (forall v0 (exist v1 (forall v2 (AtomicFormula p [VarTerm v0, VarTerm v1, VarTerm v2])))) (forall v1 (exist v2 (AtomicFormula q [VarTerm v1, VarTerm v2, VarTerm v0, VarTerm v2, VarTerm v0])))
  let formula1 = IMPLY (forall v0 (exist v1 (forall v2 (AtomicFormula p [VarTerm v0, VarTerm v1, VarTerm v2])))) (forall v1 (exist v2 (AtomicFormula q [VarTerm v1, VarTerm v2, VarTerm v0, VarTerm v2, VarTerm v0])))

  let b = Relation "B" 1
  let s = Relation "S" 1
  let x = Variable "x"
  let y = Variable "y"
  let vx = VarTerm x
  let vy = VarTerm y

  let p = Relation "P" 2
  let q = Relation "Q" 2
  let r = Relation "R" 2
  let w1q8 = (NOT (forall x (exist y (IMPLY (AND (AtomicFormula p [vx, vy]) (AtomicFormula q [vx, vy])) (AtomicFormula r [vx, vy])))))

  let barber1 = (forall x (forall y (IMPLY (AND (AtomicFormula b [vx]) (NOT (AtomicFormula s [vy, vy]))) (AtomicFormula s [vx, vy]))))
  let formula = w1q8
  print ("Original Formula: " ++ show formula)
  let preprocessedFormula = stripArrows formula
  print ("After eliminating arrows: " ++ show preprocessedFormula)
  let (standardizeFormula, _varRecord) = _standardize (preprocessedFormula, [], emptyVarRecord)
  print ("After standardization " ++ show standardizeFormula)
  let eliminatedFormula = eliminateExistentialInFormula standardizeFormula
  print ("After eliminating existentials: " ++ show eliminatedFormula)
  let noUniversalFormula = dropUniversals eliminatedFormula
  print ("After dropping universals: " ++ show noUniversalFormula)
  let distributedFormula = distributeANDOR noUniversalFormula
  print distributedFormula
  let processedFormula = naiveRemoveDuplicate distributedFormula
  print processedFormula
  let clauses = fromCNFFormulaToClauses processedFormula
  print clauses

  print "###################################"
  let a = ConstTerm A
  let b = ConstTerm B
  let z = Variable "z"
  let g = Function "g" 1
  let h = Function "h" 1
  let f = Function "f" 2
  let p = Relation "P" 2
  let tx = VarTerm x
  let ty = VarTerm y
  let tz = VarTerm z
  print "q1"
  let pax = AtomicFormula p [a, tx]
  let pyy = AtomicFormula p [ty, ty]
  let literal_pax = Literal pax
  let literal_pyy = Literal pyy
  testMGU literal_pax literal_pyy
  print "q2"
  let lpgxz = Literal (AtomicFormula p [FuncTerm g [tx], tz])
  let lpgyz = Literal (AtomicFormula p [FuncTerm g [ty], FuncTerm g [tz]])
  testMGU lpgxz lpgyz
  print "q3"
  let lpgxy = Literal (AtomicFormula p [FuncTerm g [tx], ty])
  let lpyhx = Literal (AtomicFormula p [ty, FuncTerm h [tx]])
  testMGU lpgxy lpyhx
  print "q4"
  let lpxgx = Literal (AtomicFormula p [tx, FuncTerm g [tx]])
  let lpgyy = Literal (AtomicFormula p [FuncTerm g [ty], ty])
  testMGU lpxgx lpgyy
  print "q5"
  let lpxgy = Literal (AtomicFormula p [tx, FuncTerm g [ty]])
  let lgypx = Literal (AtomicFormula p [FuncTerm g [ty], tx])
  testMGU lpxgy lgypx
  print "q6"
  let lpyfxy = Literal (AtomicFormula p [ty, FuncTerm f [tx,ty]])
  let lbfay = Literal (AtomicFormula p [b, FuncTerm f [a, ty]])
  testMGU lpyfxy lbfay
  let lpgzfaz = Literal (AtomicFormula p [FuncTerm g [tz], FuncTerm f [a, tz]])
  testMGU lpyfxy lpgzfaz
-- print "\n Testing distribute AND OR----------"
-- let formulaA = AtomicFormula p [ConstTerm A]
-- let formulaB = AtomicFormula p [ConstTerm B]
-- let formulaC = AtomicFormula p [ConstTerm C]
-- let aAndBOrC = (formulaA `AND` formulaB) `OR` formulaC
-- print ("(A and B) or C: "++ show aAndBOrC)
-- print ("After distribution: "++ show (distributeANDOR aAndBOrC))
-- print (formula == (NOT formula1))
-- print ((AND formulaA formulaB)==(AND formulaB formulaA))

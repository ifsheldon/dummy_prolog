module Main where

import Algorithms
import Data.HashMap.Strict as HashMap
import Lib
import SigmaSignature
import Literals

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

-- print "\n Testing distribute AND OR----------"
-- let formulaA = AtomicFormula p [ConstTerm A]
-- let formulaB = AtomicFormula p [ConstTerm B]
-- let formulaC = AtomicFormula p [ConstTerm C]
-- let aAndBOrC = (formulaA `AND` formulaB) `OR` formulaC
-- print ("(A and B) or C: "++ show aAndBOrC)
-- print ("After distribution: "++ show (distributeANDOR aAndBOrC))
-- print (formula == (NOT formula1))
-- print ((AND formulaA formulaB)==(AND formulaB formulaA))

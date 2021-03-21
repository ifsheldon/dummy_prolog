module Main where

import Lib
import SigmaSignature
import Algorithms
import Data.HashMap.Strict as HashMap

main = do
    let v0 = Variable "v0"
    let v1 = Variable "v1"
    let v2 = Variable "v2"
    let p = Relation "P" 3
    let q = Relation "Q" 3
    let formula = IMPLY (QFormula FORALL v0 (QFormula EXIST v1 (QFormula FORALL v2 (AtomicFormula p [VarTerm v0, VarTerm v1, VarTerm v2]) ))) (QFormula FORALL v1 (QFormula EXIST v2 (AtomicFormula q [VarTerm v1, VarTerm v2, VarTerm v0, VarTerm v2, VarTerm v0])))
    print ("Original Formula: "++show formula) 
    let preprocessedFormula = stripArrows formula
    print ("After eliminating arrows: " ++ show preprocessedFormula)
    let (standardizeFormula, _varRecord) = _standardize (preprocessedFormula,[] ,emptyVarRecord)
    print ("After standardization " ++ show standardizeFormula)
    let eliminatedFormula = eliminateExistentialInFormula standardizeFormula
    print ("After eliminating existentials: "++ show eliminatedFormula)
    let noUniversalFormula = dropUniversals eliminatedFormula
    print ("After dropping universals: "++ show noUniversalFormula)
    print "\n Testing distribute AND OR----------"
    let formulaA = AtomicFormula p [ConstTerm A]
    let formulaB = AtomicFormula p [ConstTerm B]
    let formulaC = AtomicFormula p [ConstTerm C]
    let aAndBOrC = (formulaA `AND` formulaB) `OR` formulaC
    print ("(A and B) or C: "++ show aAndBOrC)
    print ("After distribution: "++ show (distributeANDOR aAndBOrC))
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
    let formula = IMPLY (QFormula FORALL v0 (QFormula EXIST v1 (QFormula FORALL v2 (AtomicFormula p [VarTerm v0, VarTerm v1, VarTerm v2]) ))) (QFormula FORALL v1 (QFormula EXIST v2 (AtomicFormula q [VarTerm v1, VarTerm v2, VarTerm v0, VarTerm v0])))
    let preprocessedFormula = stripArrows formula
    let (standardizeFormula, _varRecord) = standardize (preprocessedFormula,[] ,emptyVarRecord)
    -- let formula = IMPLY (QFormula FORALL x (AtomicFormula r1 [VarTerm x])) (QFormula EXIST x (AtomicFormula r2 [VarTerm x]))
    -- let nf = negateFormula (stripArrows formula)
    -- print (nf)
    print standardizeFormula
    print _varRecord
    print (eliminateExistentialInFormula standardizeFormula)
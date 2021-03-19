module Main where

import Lib
import SigmaSignature
import Algorithms

main = do
    let x = Variable "x"
    let r1 = Relation "A" 1
    let r2 = Relation "B" 1
    let formula = IMPLY (QFormula FORALL x (AtomicFormula r1 [VarTerm x])) (QFormula EXIST x (AtomicFormula r2 [VarTerm x]))
    let nf = negateFormula (stripArrows formula)
    print (nf)
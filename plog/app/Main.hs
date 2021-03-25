module Main where

import Algorithms
import Data.HashMap.Strict as HashMap
import SigmaSignature
import Literals

main = do
  let x = Variable "x"
  let y = Variable "y"
  let vx = VarTerm x
  let vy = VarTerm y
  let isBarber = Relation "isBarber" 1
  let shaves = Relation "shaves" 2
  let bx = AtomicFormula isBarber [vx]
  let syy = AtomicFormula shaves [vy, vy]
  let sxy = AtomicFormula shaves [vx, vy]
  let formulaA = forall x (forall y ((bx `AND` (NOT syy)) `IMPLY` sxy))
  let formulaB = NOT (exist x (exist y ((bx `AND` syy) `AND` sxy)))
  let query = NOT (exist x bx)
  let negatedQuery = NOT query
  let clausesA = getClausesFromFormula formulaA
  let clausesB = getClausesFromFormula formulaB
  let negQueryClauses = getClausesFromFormula negatedQuery
  print "Original Formulas: -----------------------"
  print formulaA
  print formulaB
  print query
  print "Resulted Clauses: ------------------------"
  print clausesA
  print clausesB
  print negQueryClauses
  print "Resolution Result: ----------------------"
  let clauses = concat [clausesA, clausesB, negQueryClauses]
  let resolveResult = resolveClauses clauses
  print resolveResult

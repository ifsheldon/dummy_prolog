module Main where

import Algorithms
import Data.HashMap.Strict as HashMap
import Data.HashSet as HashSet
import Literals
import SigmaSignature
import Theories

main = do
  let x = Variable "x"
  let y = Variable "y"
  let z = Variable "z"
  let vx = VarTerm x
  let vy = VarTerm y
  let vz = VarTerm z
  print "Testing using the example in Worksheet 2 Q4 : Barbershop ----------------------"
  let isBarber = Relation "isBarber" 1
  let shaves = Relation "shaves" 2
  let barberSignature = Signature {constants = HashSet.empty, functions = HashSet.empty, relations = HashSet.fromList [isBarber, shaves]}
  let barberSignatureValid = validateSignature barberSignature
  print ("Barber signature is valid: " ++ show barberSignatureValid)
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
  print "Theory consistency check (if returned `Resolvable Nothing`, the theory is in consistent)"
  let theory_clauses = concat [clausesA, clausesB]
  let resolveTheoryResult = resolveClauses theory_clauses
  print resolveTheoryResult
  print "Resolution Result: ----------------------"
  let clauses = concat [clausesA, clausesB, negQueryClauses]
  let resolveResult = resolveClauses clauses
  print resolveResult
  --Alternatively, use theory and queryWithTheory to perform resolution
  let barberTheory = FormulaTheory [formulaA, formulaB]
  let isBarberTheoryValid = validateFormulaTheory barberSignature barberTheory
  print ("barber theory is valid w.r.t barber signature: " ++ show isBarberTheoryValid)
  let queryResult = queryWithTheory barberTheory query
  print queryResult -- RESOLVABLE Nothing means a contradiction is found

  -- descendant
  print "Testing using the example in Worksheet 2 Q5 : Descendant -------------------------"
  let child = Relation "Child" 2
  let descendant = Relation "Descendant" 2
  let anna = ConstTerm (Constant "Anna")
  let peter = ConstTerm (Constant "Peter")
  let hans = ConstTerm (Constant "Hans")
  let child_peter_anna = AtomicFormula child [peter, anna]
  let child_anna_hans = AtomicFormula child [anna, hans]
  let child_x_y = AtomicFormula child [vx, vy]
  let child_x_z = AtomicFormula child [vx, vz]
  let descendant_z_y = AtomicFormula descendant [vz, vy]
  let descendant_x_y = AtomicFormula descendant [vx, vy]
  let descendantDef = forall x (forall y ((child_x_y `OR` (exist z (child_x_z `AND` descendant_z_y))) `IMPLY` descendant_x_y))
  let descendantQuery = AtomicFormula descendant [peter, hans]

  print "Original Formulas: -----------------------"
  print child_anna_hans
  print child_peter_anna
  print descendantDef
  print descendantQuery

  let descendantTheory = FormulaTheory [descendantDef, child_peter_anna, child_anna_hans]
  let descendantQueryResult = queryWithTheory descendantTheory descendantQuery
  print descendantQueryResult

module Theories
  ( Theory(..),
    fromFormulaTheoryToClauseTheory,
    validateFormulaTheory,
    queryWithTheory,
  )
where

import SigmaSignature
import Literals
import Algorithms

data Theory = FormulaTheory [Formula] | ClauseTheory [Clause]

fromFormulaTheoryToClauseTheory :: Theory -> Theory
fromFormulaTheoryToClauseTheory formulaTheory = 
  case formulaTheory of 
    ClauseTheory _ -> formulaTheory
    FormulaTheory formulas -> ClauseTheory $ concatMap getClausesFromFormula formulas

validateFormulaTheory :: Signature -> Theory -> Bool 
validateFormulaTheory signature theory = 
  case theory of 
    FormulaTheory formulas -> all (validateFormula signature) formulas

queryWithTheory :: Theory -> Formula -> ResolveResult
queryWithTheory theory query = 
  let clausesInTheory = case theory of 
                            ClauseTheory clauses -> clauses
                            FormulaTheory formulas -> concatMap getClausesFromFormula formulas
      negatedQuery = NOT query
      queryClauses = getClausesFromFormula negatedQuery
      allClauses = clausesInTheory ++ queryClauses
  in
    resolveClauses allClauses 

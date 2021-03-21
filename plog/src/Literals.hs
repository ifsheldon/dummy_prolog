module Literals(
    Clause(..),
    Literal(..),
    fromCNFFormulaToClauses
) where
import SigmaSignature
data Literal = Literal Formula
data Clause = Clause [Literal]

cutFormulaByAND :: Formula -> [Formula]
cutFormulaByAND formula = 
    case formula of 
        AND f1 f2 -> cutFormulaByAND f1 ++ cutFormulaByAND f2
        _ -> [formula]

cutFormulaByOR :: Formula -> [Formula]
cutFormulaByOR formula = 
    case formula of 
        OR f1 f2 -> cutFormulaByOR f1 ++ cutFormulaByOR f2
        _ -> [formula]

genClauseFromPreprocessedFormula :: Formula -> Clause
genClauseFromPreprocessedFormula = Clause . map Literal . cutFormulaByOR

fromCNFFormulaToClauses :: Formula -> [Clause]
fromCNFFormulaToClauses = map genClauseFromPreprocessedFormula . cutFormulaByAND
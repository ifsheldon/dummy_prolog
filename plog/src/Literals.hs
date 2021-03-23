module Literals
  ( Clause (..),
    Literal (..),
    fromCNFFormulaToClauses,
  )
where

import qualified Data.HashSet as HashSet
import Data.Hashable
import SigmaSignature

data Literal = Literal Formula deriving (Eq, Show)

instance Hashable Literal where
  hashWithSalt salt literal = hashWithSalt salt (show formula) where (Literal formula) = literal

data Clause = Clause [Literal] deriving (Eq, Show)

instance Hashable Clause where
  hashWithSalt salt clause = sum (map (hashWithSalt salt) literals) where (Clause literals) = clause

cutFormulaByAND :: Formula -> [Formula]
cutFormulaByAND formula =
  case formula of
    AND f1 f2 -> cutFormulaByAND f1 ++ cutFormulaByAND f2
    _ -> [formula]

cutFormulaByOR :: Formula -> [Formula] -- get a set of Atomic formulas or their negations
cutFormulaByOR formula =
  case formula of
    OR f1 f2 -> cutFormulaByOR f1 ++ cutFormulaByOR f2
    _ -> [formula]

genClauseFromPreprocessedFormula :: Formula -> Clause
genClauseFromPreprocessedFormula = Clause . map Literal . cutFormulaByOR

removeDuplicates :: [Clause] -> [Clause]
removeDuplicates clauses =
  let listsOfLiterals = map (\(Clause literals) -> literals) clauses
      listsOfDistinctLiterals = map (HashSet.toList . HashSet.fromList) listsOfLiterals
      newClauses = (HashSet.toList . HashSet.fromList . map Clause) listsOfDistinctLiterals
   in newClauses

fromCNFFormulaToClauses :: Formula -> [Clause]
fromCNFFormulaToClauses = removeDuplicates . map genClauseFromPreprocessedFormula . cutFormulaByAND

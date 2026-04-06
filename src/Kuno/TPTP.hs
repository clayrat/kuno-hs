module Kuno.TPTP
  ( TPTPFormula(..)
  , TPTPDb(..)
  , conjectureFormula
  , hasConjecture
  , nonConjectureFormulas
  , problematize
  , dbContainsContradiction
  , dbContainsVerum
  , dbContainsQuantifier
  , dbContainsEquation
  ) where

import Data.List (find)
import Data.Maybe (isJust)

import Kuno.Expression

-- | A TPTP annotated formula (fof or cnf)
data TPTPFormula = TPTPFormula
  { tptpName    :: String
  , tptpRole    :: String
  , tptpFormula :: Formula
  } deriving (Show)

-- | A TPTP problem database
data TPTPDb = TPTPDb
  { tptpFormulas :: [TPTPFormula]
  , tptpPath     :: Maybe FilePath
  } deriving (Show)

conjectureFormula :: TPTPDb -> Maybe TPTPFormula
conjectureFormula = find ((== "conjecture") . tptpRole) . tptpFormulas

hasConjecture :: TPTPDb -> Bool
hasConjecture = isJust . conjectureFormula

nonConjectureFormulas :: TPTPDb -> [TPTPFormula]
nonConjectureFormulas db =
  filter (\f -> tptpRole f /= "conjecture") (tptpFormulas db)

-- | Convert a TPTP problem to a single formula by forming
-- (premise₁ ∧ … ∧ premiseₙ) → conjecture (Section 3 of Alama 2014).
-- This "problematization" is the standard way to reduce a multi-formula
-- TPTP problem to a single dialogue thesis.
problematize :: TPTPDb -> Maybe Formula
problematize db = do
  c <- conjectureFormula db
  let cFormula = equivalenceToConjunction (tptpFormula c)
      premises = map tptpFormula (nonConjectureFormulas db)
  return $ case premises of
    [] -> cFormula
    _  -> Binary Impl (foldl1 (Binary And) premises) cFormula

dbContainsContradiction :: TPTPDb -> Bool
dbContainsContradiction = any (containsContradiction . tptpFormula) . tptpFormulas

dbContainsVerum :: TPTPDb -> Bool
dbContainsVerum = any (containsVerum . tptpFormula) . tptpFormulas

dbContainsQuantifier :: TPTPDb -> Bool
dbContainsQuantifier = any (containsQuantifier . tptpFormula) . tptpFormulas

dbContainsEquation :: TPTPDb -> Bool
dbContainsEquation = any (containsEquation . tptpFormula) . tptpFormulas

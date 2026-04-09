-- | Multi-premise TPTP problems parsed from inline strings.
--
-- Tests the full pipeline: TPTP parsing -> problematization ->
-- dialogue search (the "Right db" path of 'intuitionisticallyValid').
--
-- Whereas FamousFormulas.hs tests bare formulas (the "Left formula" path),
-- this suite exercises the code path used by the CLI: a TPTP database
-- with annotated axioms, hypotheses, and a conjecture.

module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit

import Kuno.Parse
import Kuno.DialogueSearch

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

depth :: Int
depth = 40

isTheoremTPTP :: String -> SearchResult
isTheoremTPTP tptpString =
  case parseTPTP tptpString of
    Left err  -> error $ "Parse error: " ++ err
    Right db  -> intuitionisticallyValid (Right db) depth

assertValidTPTP :: String -> String -> TestTree
assertValidTPTP name tptp = testCase name $
  isTheoremTPTP tptp @?= Proved

------------------------------------------------------------------------
-- Three Wise Men puzzle
--
-- The king has 3 white and 2 black hats.  He places one hat on each of
-- three wise men A, B, C.  Each sees the others' hats but not his own.
--
-- A says "I don't know my hat color."
-- B says "I don't know my hat color either."
-- C says "I know!  Mine is white."
--
-- Formalization: the ignorance of A and B, combined with the constraint
-- that at most 2 black hats exist, entails that C must wear white.
------------------------------------------------------------------------

threeWiseMen :: String
threeWiseMen = unlines
  [ "fof(notallblack, axiom, ~((b(A) & b(B)) & b(C)))."
  , "fof(aignorant, axiom, ~(b(B) & b(C)))."
  , "fof(bignorant, axiom, ~(b(A) & b(C)))."
  , "fof(dichotomy, axiom, ![X]: (w(X) | b(X)))."
  , "fof(conclusion, conjecture, w(C))."
  ]

------------------------------------------------------------------------
-- Modus Ponens with premises
--
-- From (p => q) and p, derive q.  The simplest multi-premise problem.
------------------------------------------------------------------------

modusPonens :: String
modusPonens = unlines
  [ "fof(premise1, axiom, (p => q))."
  , "fof(premise2, hypothesis, p)."
  , "fof(conclusion, conjecture, q)."
  ]

------------------------------------------------------------------------
-- Constructive dilemma
--
-- From (p => q), (r => s), and (p | r), conclude (q | s).
-- Requires case analysis on the disjunction.
------------------------------------------------------------------------

constructiveDilemma :: String
constructiveDilemma = unlines
  [ "fof(ax1, axiom, (p => q))."
  , "fof(ax2, axiom, (r => s))."
  , "fof(ax3, axiom, (p | r))."
  , "fof(conclusion, conjecture, (q | s))."
  ]

------------------------------------------------------------------------
-- Test groups
------------------------------------------------------------------------

tptpTheorems :: TestTree
tptpTheorems = testGroup "Multi-premise theorems"
  [ assertValidTPTP "modus ponens (2 premises)" modusPonens
  , assertValidTPTP "constructive dilemma (3 premises)" constructiveDilemma
  , assertValidTPTP "Three Wise Men (4 premises, FOL)" threeWiseMen
  ]

------------------------------------------------------------------------
-- Runner
------------------------------------------------------------------------

main :: IO ()
main = defaultMain $ testGroup "TPTP Problems"
  [ tptpTheorems
  ]

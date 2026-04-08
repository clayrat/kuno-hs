-- | Generic dialogue game infrastructure.
--
-- A dialogue game starts with a formula φ asserted by the Proponent (P),
-- against the Opponent (O) who disputes it. Players alternate moves, each
-- being an attack on or defense of a previous assertion.
--
-- This module provides the game state representation and generic operations
-- (adding moves, querying continuations, win conditions). Logic-specific
-- rules (particle rules, structural validators, rulesets) live in
-- separate modules under @Kuno.Logic@.
--
-- Reference: Jesse Alama, "Kuno for proof search", arXiv:1405.1864v1
module Kuno.Dialogue
  ( Ruleset(..)
  , Dialogue(..)
  , dialogueLength
  , emptyDialogue
  , addMove
  , nthMove
  , nthStatement
  , lastMove
  , continuations
  , nextProponentMoves
  , nextOpponentMoves
  , proponentWins
  , opponentWins
  , truncateDialogue
  , dialogueTermsIn
  , dialogueFreeVariables
  , moveIsRepetition
  , mostRecentOpenAttackOn
  , isAtomicStatement
  , showDialogue
  , showStatement
  , showMove
  ) where

import Data.Foldable (toList)
import Data.Sequence (Seq, (|>), ViewR(..))
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import Kuno.Expression
import Kuno.Move

-- | A ruleset governs which moves are legal in a dialogue
data Ruleset = Ruleset
  { rsExpander    :: Dialogue -> [Move]
  , rsValidator   :: Dialogue -> Bool
  , rsDescription :: String
  }

instance Show Ruleset where
  show = rsDescription

-- | A dialogue game state.
--
-- The Lisp @dialogue@ class stores only three slots: @plays@ (a list of
-- moves), @initial-formula@, and @ruleset@.  Every query — the set of
-- terms, free variables, whether a move has already been played, which
-- statements Opponent has asserted — is recomputed from @plays@ on each
-- call.
--
-- This Haskell representation adds four incrementally maintained caches
-- that are updated in 'addMove' (and rebuilt in 'truncateDialogue'):
--
--   * @dPlaySet@ — @Set Move@: enables O(log n) move-membership tests
--     for the No-Repeats constraint ('moveIsRepetition'), replacing a
--     linear scan of the play list.
--
--   * @dTerms@ — @Set Term@: all terms that have appeared in the
--     dialogue so far.  Used by the FOL expanders ('dFolAttacks') to
--     enumerate candidate witness terms for quantifier instantiation
--     without re-traversing every move's formula.
--
--   * @dFreeVars@ — @Set Term@: free variables across all moves.  Also
--     consumed by the FOL expanders for the same purpose.
--
--   * @dOppAssertions@ — @Set Statement@: statements asserted by
--     Opponent.  Used by the D/E structural rule that restricts
--     Proponent to atomic formulas that Opponent has asserted earlier
--     ('opponentAssertedAtomEarlier' in "Kuno.Logic.Intuitionistic").
data Dialogue = Dialogue
  { dPlays          :: Seq Move
  , dPlaySet        :: Set.Set Move
  , dTerms          :: Set.Set Term
  , dFreeVars       :: Set.Set Term
  , dOppAssertions  :: Set.Set Statement
  , dInitialFormula :: Formula
  , dRuleset_       :: Ruleset
  }

instance Show Dialogue where
  show d = "Dialogue{" ++ show (dialogueLength d) ++ " moves, "
           ++ showFormula (dInitialFormula d) ++ "}"

dialogueLength :: Dialogue -> Int
dialogueLength d = 1 + Seq.length (dPlays d)

emptyDialogue :: Formula -> Ruleset -> Dialogue
emptyDialogue = Dialogue Seq.empty Set.empty Set.empty Set.empty Set.empty

addMove :: Dialogue -> Move -> Dialogue
addMove d m = d
  { dPlays          = dPlays d |> m
  , dPlaySet        = Set.insert m (dPlaySet d)
  , dTerms          = dTerms d `Set.union` Set.fromList (moveTermsIn m)
  , dFreeVars       = dFreeVars d `Set.union` Set.fromList (moveFreeVariables m)
  , dOppAssertions  = if isOpponentMove m
                      then Set.insert (moveStatement m) (dOppAssertions d)
                      else dOppAssertions d
  }

nthMove :: Dialogue -> Int -> Maybe Move
nthMove d n
  | n <= 0 = Nothing
  | n > Seq.length (dPlays d) = Nothing
  | otherwise = Just (Seq.index (dPlays d) (n - 1))

nthStatement :: Dialogue -> Int -> Statement
nthStatement d 0 = FormulaS (dInitialFormula d)
nthStatement d n = case nthMove d n of
  Just m  -> moveStatement m
  Nothing -> FormulaS (dInitialFormula d)

lastMove :: Dialogue -> Maybe Move
lastMove d = case Seq.viewr (dPlays d) of
  EmptyR -> Nothing
  _ :> m -> Just m

truncateDialogue :: Dialogue -> Int -> Dialogue
truncateDialogue d n =
  let plays' = Seq.take n (dPlays d)
      playsList = toList plays'
  in d { dPlays          = plays'
       , dPlaySet        = Set.fromList playsList
       , dTerms          = Set.fromList (concatMap moveTermsIn playsList)
       , dFreeVars       = Set.fromList (concatMap moveFreeVariables playsList)
       , dOppAssertions  = Set.fromList (map moveStatement (filter isOpponentMove playsList))
       }

dialogueTermsIn :: Dialogue -> [Term]
dialogueTermsIn = Set.toList . dTerms

dialogueFreeVariables :: Dialogue -> [Term]
dialogueFreeVariables = Set.toList . dFreeVars

-- Dialogue analysis

-- openAttackIndices :: Dialogue -> [Int]
-- openAttackIndices d = case dPlays d of
--   [] -> []
--   plays ->
--     [ i | (m, i) <- zip plays [1..]
--         , isAttack m
--         , not $ any (\other -> isDefense other && moveReference other == i)
--                     (drop i plays)
--     ]

-- | Find the most recent open attack on the given player
mostRecentOpenAttackOn :: Player -> Dialogue -> Maybe Int
mostRecentOpenAttackOn player d = go (dialogueLength d)
  where
    attacker = otherPlayer player
    plays = dPlays d
    go i
      | i < 1 = Nothing
      | otherwise =
          case nthMove d i of
            Just m | movePlayer m == attacker && isAttack m ->
              let tail_ = Seq.drop i plays
              in if not $ any (\other -> movePlayer other == player
                                     && isDefense other
                                     && moveReference other == i) tail_
                 then Just i
                 else go (i - 1)
            _ -> go (i - 1)

isAtomicStatement :: Statement -> Bool
isAtomicStatement (FormulaS f) = isAtomic f
isAtomicStatement _ = False

moveIsRepetition :: Dialogue -> Move -> Bool
moveIsRepetition d m = m `Set.member` dPlaySet d

-- Continuations and win conditions

continuations :: Dialogue -> [Move]
continuations d =
  let rs = dRuleset_ d
      validate m = rsValidator rs (addMove d m)
      moves = rsExpander rs d
  in nubOrd (filter validate moves)

nextProponentMoves :: Dialogue -> [Move]
nextProponentMoves = filter isProponentMove . continuations

nextOpponentMoves :: Dialogue -> [Move]
nextOpponentMoves = filter isOpponentMove . continuations

proponentWins :: Dialogue -> Bool
proponentWins d = case lastMove d of
  Just m -> isProponentMove m && null (nextOpponentMoves d)
  Nothing -> False

opponentWins :: Dialogue -> Bool
opponentWins d = case lastMove d of
  Just m -> isOpponentMove m && null (nextProponentMoves d)
  Nothing -> False

-- Pretty-printing

showStatement :: Statement -> String
showStatement (FormulaS f) = showFormula f
showStatement (AttackS AttackLeftConjunct) = "L?"
showStatement (AttackS AttackRightConjunct) = "R?"
showStatement (AttackS WhichDisjunct) = "?∨"
showStatement (AttackS (WhichInstance (Just t))) = "?" ++ showTerm t
showStatement (AttackS (WhichInstance Nothing)) = "?"
showStatement (TermS t) = showTerm t

showMove :: Move -> String
showMove m =
  let player = case movePlayer m of { Proponent -> "P"; Opponent -> "O" }
      kind = if moveIsAttack m then "atk" else "def"
      ref = show (moveReference m)
  in player ++ " [" ++ ref ++ "] " ++ kind ++ " " ++ showStatement (moveStatement m)

-- | Pretty-print a dialogue as a numbered table.
--
-- @
--   0  P       thesis  (p => (q => p))
--   1  O [0]   atk     p
--   2  P [1]   def     (q => p)
--   3  O [2]   atk     q
--   4  P [3]   def     p
-- @
showDialogue :: Dialogue -> String
showDialogue d =
  let header = showLine (0 :: Int) "P" "" "thesis" (showFormula (dInitialFormula d))
      moves = toList (dPlays d)
      body = zipWith showMoveLine [1 :: Int ..] moves
  in unlines (header : body)
  where
    showMoveLine i m =
      let player = case movePlayer m of { Proponent -> "P"; Opponent -> "O" }
          ref = "[" ++ show (moveReference m) ++ "]"
          kind = if moveIsAttack m then "atk" else "def"
      in showLine i player ref kind (showStatement (moveStatement m))
    showLine i player ref kind stmt =
      let iStr = show i
          pad n s = s ++ replicate (max 0 (n - length s)) ' '
      in pad 4 iStr ++ pad 3 player ++ pad 6 ref ++ pad 8 kind ++ stmt

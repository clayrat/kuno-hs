-- | Generic proof-search infrastructure for dialogue-based theorem provers.
--
-- This module defines the 'Logic' abstraction (a record packaging a logic's
-- search strategy) and the depth-limited minimax algorithm that is shared
-- across all logics.
module Kuno.Logic
  ( SearchResult(..)
  , Logic(..)
  , proponentHasWinningStrategy
  , everyDisallowingCutoffs
  , someNonCutoff
  , tptpToDialogue
  ) where

import Kuno.Expression
import Kuno.Move
import Kuno.Dialogue
import Kuno.TPTP

-- | Result of a proof search
data SearchResult
  = Proved Dialogue -- ^ Proponent has a winning strategy
  | Refuted         -- ^ No winning strategy exists
  | Cutoff          -- ^ Depth limit reached

instance Eq SearchResult where
  Proved _ == Proved _ = True
  Refuted  == Refuted  = True
  Cutoff   == Cutoff   = True
  _        == _        = False

instance Show SearchResult where
  show (Proved _) = "Proved"
  show Refuted    = "Refuted"
  show Cutoff     = "Cutoff"

-- | A logic packages the search strategies for bare formulas and TPTP
-- databases.  Each logic provides its own particle rules, structural rules,
-- and search heuristics internally; the 'Logic' record exposes only the
-- high-level search entry points.
data Logic = Logic
  { logicName          :: String
  , logicSearchFormula :: Formula -> Int -> SearchResult
  , logicSearchDb      :: TPTPDb  -> Int -> SearchResult
  }

-- | Depth-limited minimax search: does Proponent have a winning strategy?
-- P wins iff for every O move there exists a P response leading to a
-- winning position (Theorem 1 of Alama 2014). The search expands forward
-- from the current state, alternating O-then-P moves, decrementing the
-- depth cutoff by 2 per round. Returns 'Cutoff' when the depth limit is
-- reached without a conclusive result.
proponentHasWinningStrategy :: Dialogue -> Int -> SearchResult
proponentHasWinningStrategy d cutoff
  | cutoff < 0 = Cutoff
  | cutoff == 0 =
      if null (nextOpponentMoves d) then Proved d else Cutoff
  | otherwise =
      let oppMoves = nextOpponentMoves d
      in if null oppMoves
         then Proved d
         else everyDisallowingCutoffs
                (\oppMove ->
                   let dOpp = addMove d oppMove
                       propMoves = nextProponentMoves dOpp
                   in if null propMoves
                      then Refuted
                      else someNonCutoff
                             (\propMove ->
                                let dProp = addMove dOpp propMove
                                in proponentHasWinningStrategy dProp (cutoff - 2))
                             propMoves)
                oppMoves

-- | Check that a predicate holds for all elements, propagating Cutoff.
-- On success, returns the 'Proved' from the last element (the deepest dialogue).
everyDisallowingCutoffs :: (a -> SearchResult) -> [a] -> SearchResult
everyDisallowingCutoffs _ [] = Proved (error "everyDisallowingCutoffs: empty")
everyDisallowingCutoffs f (x:xs) =
  case f x of
    Refuted    -> Refuted
    Cutoff     -> case everyDisallowingCutoffs f xs of
                    Refuted -> Refuted
                    _       -> Cutoff
    Proved d   -> case xs of
                    [] -> Proved d
                    _  -> everyDisallowingCutoffs f xs

-- | Check that a predicate holds for at least one element, propagating Cutoff.
-- Returns the first 'Proved' found.
someNonCutoff :: (a -> SearchResult) -> [a] -> SearchResult
someNonCutoff _ [] = Refuted
someNonCutoff f (x:xs) =
  case f x of
    Proved d -> Proved d
    Cutoff   -> case someNonCutoff f xs of
                  Proved d -> Proved d
                  _        -> Cutoff
    Refuted  -> someNonCutoff f xs

-- | Convert a TPTP database to an initial dialogue state
tptpToDialogue :: TPTPDb -> Ruleset -> Maybe Dialogue
tptpToDialogue db ruleset = do
  c <- conjectureFormula db
  let cFormula = equivalenceToConjunction (tptpFormula c)
      premises = map tptpFormula (nonConjectureFormulas db)
  case premises of
    [] | isAtomic cFormula -> Nothing
       | otherwise -> Just $ emptyDialogue cFormula ruleset
    [premise] ->
      let initial = Binary Impl premise cFormula
          d0 = emptyDialogue initial ruleset
          d1 = addMove d0 (Move (FormulaS premise) 0 True Opponent)
          d2 = addMove d1 (Move (FormulaS cFormula) 1 False Proponent)
      in Just d2
    _ ->
      let conjunction = foldl1 (Binary And) premises
          initial = Binary Impl conjunction cFormula
          d0 = emptyDialogue initial ruleset
      in Just $ buildPremiseMoves d0 conjunction premises cFormula

-- | Build the initial moves that decompose the conjunction of premises
buildPremiseMoves :: Dialogue -> Formula -> [Formula] -> Formula -> Dialogue
buildPremiseMoves d0 conjunction premises cFormula =
  let -- Opponent attacks the implication with the conjunction
      d1 = addMove d0 (Move (FormulaS conjunction) 0 True Opponent)
      (dFinal, _) = foldMoves d1 1 conjunction premises
      -- Proponent defends with the conjecture
      dResult = addMove dFinal (Move (FormulaS cFormula) 1 False Proponent)
  in dResult
  where
    foldMoves d i conj ps = case ps of
      [] -> (d, i)
      [_] -> (d, i)
      (_:rest@(_:_)) ->
        let lhs = case conj of
                    Binary And l _ -> l
                    _ -> conj
            rhs = case conj of
                    Binary And _ r -> r
                    _ -> conj
            -- Proponent attacks left conjunct
            d2 = addMove d (Move (AttackS AttackLeftConjunct) i True Proponent)
            i2 = i + 1
            -- Opponent defends with left
            d3 = addMove d2 (Move (FormulaS lhs) i2 False Opponent)
            i3 = i2 + 1
            -- Proponent attacks right conjunct
            d4 = addMove d3 (Move (AttackS AttackRightConjunct) (i2 - 1) True Proponent)
            i4 = i3 + 1
            -- Opponent defends with right
            d5 = addMove d4 (Move (FormulaS rhs) i4 False Opponent)
            i5 = i4 + 1
        in foldMoves d5 i5 rhs rest

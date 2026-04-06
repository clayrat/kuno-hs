-- | Intuitionistic logic rules for dialogue games.
--
-- This module contains all particle rules, structural rules, expanders,
-- validators, and rulesets specific to intuitionistic logic (IL), as well
-- as the search strategies for propositional and first-order IL.
--
-- The rules implement Felscher's D and E structural rulesets as described
-- in Alama (2014), "Kuno for proof search", arXiv:1405.1864v1.
module Kuno.Logic.Intuitionistic
  ( -- * Logic value
    intuitionisticLogic
    -- * Standard rulesets
  , dRuleset
  , eRuleset
  , eRulesetNoRepetitions
  , eRulesetPreferDefenses
    -- * FOL expanders and validators
  , eFolExpander
  , eFolExpanderNoRepetitions
  , eFolExpanderNoRepetitionsPreferDefenses
  , eFolValidator
  ) where

import Data.Foldable (toList)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import Kuno.Expression
import Kuno.Move
import Kuno.Dialogue
import Kuno.Logic
import Kuno.TPTP

------------------------------------------------------------------------
-- Logic value
------------------------------------------------------------------------

-- | Intuitionistic logic: propositional and first-order, using Felscher's
-- D/E structural rules with No-Repeats and Prefer-Defense heuristics.
intuitionisticLogic :: Logic
intuitionisticLogic = Logic
  { logicName          = "Intuitionistic"
  , logicSearchFormula = searchIntuitionistic
  , logicSearchDb      = searchIntuitionisticDb
  }

searchIntuitionistic :: Formula -> Int -> SearchResult
searchIntuitionistic formula depth
  | isAtomic formula = Refuted
  | containsQuantifier formula = searchFOL formula depth
  | otherwise = searchPropositional formula depth

searchIntuitionisticDb :: TPTPDb -> Int -> SearchResult
searchIntuitionisticDb db depth
  | dbContainsQuantifier db = searchFOLDb db depth
  | otherwise = searchPropositionalDb db depth

------------------------------------------------------------------------
-- IL helpers
------------------------------------------------------------------------

opponentAssertedAtomEarlier :: Set.Set Statement -> Move -> Bool
opponentAssertedAtomEarlier oAssertions m =
  case moveStatement m of
    FormulaS f | isAtomic f ->
      FormulaS f `Set.member` oAssertions
    _ -> False

opponentAttacks :: Dialogue -> [Move]
opponentAttacks d = filter (\m -> isOpponentMove m && isAttack m) (toList (dPlays d))

duplicateOpponentAttack :: Dialogue -> Move -> Bool
duplicateOpponentAttack d m =
  isOpponentMove m && isAttack m
  && any (\other -> moveReference other == moveReference m) (opponentAttacks d)

------------------------------------------------------------------------
-- Particle rules
------------------------------------------------------------------------

-- -- Move generation: possible propositional attacks
--
-- possiblePropositionalAttacks :: Formula -> [SymbolicAttack]
-- possiblePropositionalAttacks (Conjunction _ _) = [AttackLeftConjunct, AttackRightConjunct]
-- possiblePropositionalAttacks (Disjunction _ _) = [WhichDisjunct]
-- possiblePropositionalAttacks (Implication _ _) = []  -- attack on implication: assert antecedent
-- possiblePropositionalAttacks (Negation _) = []       -- attack on negation: assert the inside
-- possiblePropositionalAttacks _ = []
--
-- -- D-ruleset possible attacks
-- dPossibleAttacks :: Dialogue -> [Move]
-- dPossibleAttacks d
--   | null (dPlays d) =
--       let f = dInitialFormula d
--       in concatMap (attacksOn 0 Opponent f) [f]
--   | otherwise =
--       let lm = last (dPlays d)
--           otherPlayer = if isOpponentMove lm then Proponent else Opponent
--           len = dialogueLength d
--           start = if isOpponentMove lm then 1 else 2
--           plays = dPlays d
--       in concatMap (\(move, i) ->
--             let stmt = moveStatement move
--             in case stmt of
--                  FormulaS f | isComposite f ->
--                    attacksOn i otherPlayer f f
--                  _ -> []
--           ) [(plays !! (i-1), i) | i <- [start, start+2 .. len-1], i <= length plays]
--          ++
--          -- If the dialogue is empty, attack the initial formula
--          if null plays then [] else
--          let initialAtks = attacksOn 0 otherPlayer (dInitialFormula d) (dInitialFormula d)
--          in if start == 1 then initialAtks else []
--   where
--     filterProponentAtoms moves =
--       let lm = lastMove d
--       in case lm of
--            Just m | isOpponentMove m ->
--              filter (\mv -> not (isAtomicStatement (moveStatement mv))
--                          || opponentAssertedAtomEarlier d mv) moves
--            _ -> moves
--
--     attacksOn ref player formula _origFormula =
--       case formula of
--         Implication ante _ ->
--           [Move { moveStatement = FormulaS ante
--                 , moveReference = ref
--                 , moveIsAttack = True
--                 , movePlayer = player }]
--         Negation inner ->
--           [Move { moveStatement = FormulaS inner
--                 , moveReference = ref
--                 , moveIsAttack = True
--                 , movePlayer = player }]
--         Disjunction _ _ ->
--           [Move { moveStatement = AttackS WhichDisjunct
--                 , moveReference = ref
--                 , moveIsAttack = True
--                 , movePlayer = player }]
--         Conjunction _ _ ->
--           [Move { moveStatement = AttackS AttackLeftConjunct
--                 , moveReference = ref
--                 , moveIsAttack = True
--                 , movePlayer = player }
--           ,Move { moveStatement = AttackS AttackRightConjunct
--                 , moveReference = ref
--                 , moveIsAttack = True
--                 , movePlayer = player }]
--         _ -> []

-- More faithful port of d-possible-attacks
dPossibleAttacks' :: Dialogue -> [Move]
dPossibleAttacks' d = case lastMove d of
  Nothing ->
      map (\atk -> Move { moveStatement = atk
                         , moveReference = 0
                         , moveIsAttack = True
                         , movePlayer = Opponent })
          (propAttacks (dInitialFormula d))
  Just lm ->
      let otherClass = otherPlayer (movePlayer lm)
          start = if isOpponentMove lm then 1 else 2
          len = dialogueLength d
          plays = dPlays d
          responses = concatMap (\i ->
            let move = Seq.index plays (i - 1)
                stmt = moveStatement move
            in case stmt of
                 FormulaS f | not (isAtomic f) ->
                   case f of
                     Binary Impl ante _ ->
                       [Move (FormulaS ante) i True otherClass]
                     Negation inner ->
                       [Move (FormulaS inner) i True otherClass]
                     Binary Or _ _ ->
                       [Move (AttackS WhichDisjunct) i True otherClass]
                     Binary And _ _ ->
                       [Move (AttackS AttackLeftConjunct) i True otherClass
                       ,Move (AttackS AttackRightConjunct) i True otherClass]
                     _ -> []
                 _ -> []
            ) [start, start + 2 .. len - 1]
      in case lm of
           _ | isOpponentMove lm ->
               let oAsserts = dOppAssertions d
               in filter (\mv -> not (isAtomicStatement (moveStatement mv))
                              || opponentAssertedAtomEarlier oAsserts mv) responses
           _ -> responses
  where
    -- Particle rules for attacks (Table 1 of Alama 2014):
    --   φ → ψ : attacker asserts φ (the antecedent)
    --   ¬φ    : attacker asserts φ (no defense is possible)
    --   φ ∨ ψ : attacker asks "which?" (defender chooses a disjunct)
    --   φ ∧ ψ : attacker picks a conjunct (defender must produce it)
    propAttacks (Binary Impl ante _) = [FormulaS ante]
    propAttacks (Negation inner) = [FormulaS inner]
    propAttacks (Binary Or _ _) = [AttackS WhichDisjunct]
    propAttacks (Binary And _ _) = [AttackS AttackLeftConjunct, AttackS AttackRightConjunct]
    propAttacks _ = []

-- -- D-ruleset possible defenses
-- dPossibleDefenses :: Dialogue -> [Move]
-- dPossibleDefenses d
--   | null (dPlays d) = []
--   | otherwise =
--       let lm = last (dPlays d)
--           otherClass = if isOpponentMove lm then Proponent else Opponent
--           mostRecent = if isOpponentMove lm
--                        then mostRecentOpenAttackOnProponent d
--                        else mostRecentOpenAttackOnOpponent d
--       in case mostRecent of
--            Nothing -> []
--            Just attackIdx ->
--              case nthMove d attackIdx of
--                Nothing -> []
--                Just attack ->
--                  let attackRef = moveReference attack
--                      attackStmt = moveStatement attack
--                      attackedStmt = nthStatement d attackRef
--                  in let defenses = computeDefenses attackedStmt attackStmt
--                         moves = map (\def -> Move { moveStatement = def
--                                                    , moveReference = attackIdx
--                                                    , moveIsAttack = False
--                                                    , movePlayer = otherClass })
--                                     defenses
--                         -- Filter duplicate opponent attacks
--                         filtered1 = if isProponentMove lm
--                                     then filter (not . duplicateOpponentAttack d) moves
--                                     else moves
--                         -- Atom restriction on Proponent
--                         filtered2 = if isOpponentMove lm
--                                     then filter (\mv -> not (isAtomicStatement (moveStatement mv))
--                                                      || opponentAssertedAtomEarlier d mv) filtered1
--                                     else filtered1
--                     in filtered2
--
-- computeDefenses :: Statement -> Statement -> [Statement]
-- computeDefenses (FormulaS attacked) _ =
--   case attacked of
--     Implication _ cons -> [FormulaS cons]
--     Disjunction l r -> [FormulaS l, FormulaS r]
--     Negation _ -> []
--     Conjunction l _ | True -> -- need to check attack type, simplified
--       [FormulaS l]  -- placeholder
--     _ -> []
-- computeDefenses _ _ = []

-- | Particle rules for defenses (Table 1 of Alama 2014):
--   φ → ψ : defender asserts ψ (the consequent)
--   φ ∨ ψ : defender chooses φ or ψ
--   ¬φ    : no defense possible (attack continues the game with φ)
--   φ ∧ ψ : defender produces the requested conjunct
computeDefenses' :: Statement -> Statement -> [Statement]
computeDefenses' (FormulaS attacked) attackStmt =
  case attacked of
    Binary Impl _ cons -> [FormulaS cons]
    Binary Or l r -> [FormulaS l, FormulaS r]
    Negation _ -> []
    Binary And l r ->
      case attackStmt of
        AttackS AttackLeftConjunct -> [FormulaS l]
        AttackS AttackRightConjunct -> [FormulaS r]
        _ -> []
    _ -> []
computeDefenses' _ _ = []

-- Full defense with proper attack checking
dPossibleDefenses' :: Dialogue -> [Move]
dPossibleDefenses' d = case lastMove d of
  Nothing -> []
  Just lm ->
      let otherClass = otherPlayer (movePlayer lm)
          mostRecent = mostRecentOpenAttackOn otherClass d
      in case mostRecent of
           Nothing -> []
           Just attackIdx ->
             case nthMove d attackIdx of
               Nothing -> []
               Just attack ->
                 let attackRef = moveReference attack
                     attackStmt = moveStatement attack
                     attackedStmt = nthStatement d attackRef
                     defenses = computeDefenses' attackedStmt attackStmt
                     moves = map (\def -> Move def attackIdx False otherClass) defenses
                     filtered1 = if isProponentMove lm
                                 then filter (not . duplicateOpponentAttack d) moves
                                 else moves
                     filtered2 = if isOpponentMove lm
                                 then let oAsserts = dOppAssertions d
                                      in filter (\mv -> not (isAtomicStatement (moveStatement mv))
                                                     || opponentAssertedAtomEarlier oAsserts mv) filtered1
                                 else filtered1
                 in filtered2

------------------------------------------------------------------------
-- Propositional expanders
------------------------------------------------------------------------

-- E-ruleset: Opponent must respond immediately
ePropositionalExpander :: Dialogue -> [Move]
ePropositionalExpander d =
  let lm = lastMove d
      i = dialogueLength d - 1
      dPoss = dPossibleDefenses' d ++ dPossibleAttacks' d
  in case lm of
       Just m | isProponentMove m ->
         filter (\mv -> moveReference mv == i) dPoss
       _ -> dPoss

-- | Prefer-Defense heuristic (Section 4 of Alama 2014): if P can defend,
-- he does so (choosing arbitrarily among available defenses). This avoids
-- premature attacks that can make the search space explode.
-- Note: this heuristic is sound for propositional logic, but leads to
-- incompleteness for FOL — see eFolExpanderNoRepetitionsPreferDefenses.
ePropositionalExpanderPreferDefenses :: Dialogue -> [Move]
ePropositionalExpanderPreferDefenses d =
  let lm = lastMove d
      ePoss = ePropositionalExpander d
  in case lm of
       Just m | isOpponentMove m ->
         let defs = filter isDefense ePoss
             nonDefs = filter (not . isDefense) ePoss
         in defs ++ nonDefs
       _ -> ePoss

-- | No-Repeats constraint (Section 4 of Alama 2014): neither player may
-- repeat a move. Without this, O can repeat moves ad infinitum when the
-- formula is not intuitionistically valid, preventing termination.
-- Note: completeness of No-Repeats for IL is an open question (it is
-- known to preserve completeness for classical logic).
ePropositionalExpanderNoRepetitions :: Dialogue -> [Move]
ePropositionalExpanderNoRepetitions d =
  filter (\mv -> not (moveIsRepetition d mv)) (ePropositionalExpander d)

------------------------------------------------------------------------
-- Structural validators
------------------------------------------------------------------------

-- The D structural rules (Section 2 of Alama 2014):
--   1. P may assert an atomic formula only if O has asserted it earlier.
--      (Enforced in the expanders via opponentAssertedAtomEarlier.)
--   2. Only the most recent open attack may be defended.
--   3. P's assertions may be attacked at most once.
--   4. Play alternates between P and O.
movesAlternate :: Dialogue -> Bool
movesAlternate d =
  all (\(m, i) -> if odd i then isOpponentMove m else isProponentMove m)
      (zip (toList (dPlays d)) [1 :: Int ..])

everyDefenseRespondsToMostRecentOpenAttack :: Dialogue -> Bool
everyDefenseRespondsToMostRecentOpenAttack d =
  let plays = toList (dPlays d)
  in all (\m ->
       if isDefense m
       then let i = moveReference m
                range = take i plays
            in not $ any (\other -> moveReference other == i) range
       else True
     ) plays

proponentAssertionsAttackedAtMostOnce :: Dialogue -> Bool
proponentAssertionsAttackedAtMostOnce d =
  let plays = toList (dPlays d)
  in all (\(m, i) ->
       if isOpponentMove m && isAttack m
       then let j = moveReference m
            in not $ any (\other -> isOpponentMove other
                                 && isAttack other
                                 && moveReference other == j)
                         (take i plays)
       else True
     ) (zip plays [0 :: Int ..])

dPropositionalValidator :: Dialogue -> Bool
dPropositionalValidator d =
  isComposite (dInitialFormula d)
  && movesAlternate d
  && everyDefenseRespondsToMostRecentOpenAttack d
  && proponentAssertionsAttackedAtMostOnce d

-- | The E rule: O must immediately respond to P's moves.
-- By Felscher's theorem (Theorem 2 of Alama 2014), adding the E rule
-- does not change which formulas have winning strategies. This makes
-- E favorable for proof search: O is more constrained, so the search
-- tree is smaller.
ePropositionalValidator :: Dialogue -> Bool
ePropositionalValidator d =
  dPropositionalValidator d
  && all (\(m, i) ->
       if isOpponentMove m then moveReference m == i else True
     ) (zip (toList (dPlays d)) [0 :: Int ..])

------------------------------------------------------------------------
-- FOL expanders
------------------------------------------------------------------------

-- | FOL attacks for a given player.
-- Proponent freely attacks Universal; Opponent freely attacks Existential.
dFolAttacks :: Player -> Dialogue -> Int -> [Move]
dFolAttacks player d termDepth_ =
  case lastMove d of
    Just m | movePlayer m == otherPlayer player ->
      let len = dialogueLength d
          plays = dPlays d
          allTerms = dialogueTermsIn d
          allFreeVars = dialogueFreeVariables d
          fresh = freshVariable allTerms [dInitialFormula d]
          allFiltered = filter (\t -> termDepth t <= termDepth_)
                          (fresh : (filter (not . isVariableTerm) allTerms ++ allFreeVars))
          start = if player == Proponent then 1 else 2
          freeChoice = if player == Proponent then isUniversal else isExistential
          freshOnly  = if player == Proponent then isExistential else isUniversal
      in concatMap (\i ->
           case moveStatement (Seq.index plays (i - 1)) of
             FormulaS f | isComposite f ->
               if freeChoice f
               then map (\t -> Move (AttackS (WhichInstance (Just t))) i True player) allFiltered
               else if freshOnly f
               then [Move (AttackS (WhichInstance (Just fresh))) i True player]
               else []
             _ -> []
           ) [start, start + 2 .. len - 1]
    _ -> []

dFolDefenseForGeneralization :: Dialogue -> Statement -> Int -> Player -> [Move]
dFolDefenseForGeneralization d attackStmt attackIdx player =
  case attackStmt of
    AttackS (WhichInstance (Just inst)) ->
      let attackRef = moveReference <$> nthMove d attackIdx
      in case attackRef of
           Just ref ->
             let attackedStmt = nthStatement d ref
             in case attackedStmt of
                  FormulaS (UniversalQ (b:_) matrix) ->
                    [Move (FormulaS (instantiate matrix inst b)) attackIdx False player]
                  FormulaS (ExistentialQ (b:_) matrix) ->
                    let fresh = freshVariable (dialogueTermsIn d) [dInitialFormula d]
                    in [Move (FormulaS (instantiate matrix fresh b)) attackIdx False player]
                  _ -> []
           Nothing -> []
    _ -> []

-- | FOL defenses for a given player
dFolDefenses :: Player -> Dialogue -> [Move]
dFolDefenses player d =
  case lastMove d of
    Just m | movePlayer m == otherPlayer player ->
      case mostRecentOpenAttackOn player d of
        Just attackIdx ->
          case nthMove d attackIdx of
            Just attack ->
              let stmt = moveStatement attack
              in case stmt of
                   AttackS (WhichInstance _) ->
                     let defs = dFolDefenseForGeneralization d stmt attackIdx player
                     in case player of
                          Opponent  -> filter (not . duplicateOpponentAttack d) defs
                          Proponent -> let oAsserts = dOppAssertions d
                                        in filter (\mv -> not (isAtomicStatement (moveStatement mv))
                                                       || opponentAssertedAtomEarlier oAsserts mv) defs
                   _ -> []
            Nothing -> []
        Nothing -> []
    _ -> []

dFolExpander :: Dialogue -> Int -> [Move]
dFolExpander d td =
  dPossibleDefenses' d ++ dPossibleAttacks' d
  ++ dFolAttacks Proponent d td ++ dFolAttacks Opponent d td
  ++ dFolDefenses Opponent d ++ dFolDefenses Proponent d

eFolExpander :: Dialogue -> Int -> [Move]
eFolExpander d td =
  let lm = lastMove d
      i = dialogueLength d - 1
      dPoss = dFolExpander d td
  in case lm of
       Just m | isProponentMove m ->
         filter (\mv -> moveReference mv == i) dPoss
       _ -> dPoss

eFolExpanderNoRepetitions :: Dialogue -> Int -> [Move]
eFolExpanderNoRepetitions d td =
  filter (not . moveIsRepetition d) (eFolExpander d td)

-- | FOL expander with no repetitions and prefer-defense heuristic.
-- The paper (Section 4) notes that rigidly applying Prefer-Defense in FOL
-- leads to incompleteness: for the valid formula
--   (∃y∀x(p(x) ∧ q(y))) → (∀x∃y(p(x) ∧ q(y)))
-- P must sometimes attack before defending. This expander therefore relaxes
-- the heuristic: if a defense exists, P commits to exactly one (the first),
-- but if no defense is available, all moves (attacks) are returned.
eFolExpanderNoRepetitionsPreferDefenses :: Dialogue -> Int -> [Move]
eFolExpanderNoRepetitionsPreferDefenses d td =
  let lm = lastMove d
      ePoss = eFolExpanderNoRepetitions d td
  in case lm of
       Just m | isOpponentMove m ->
         case filter isDefense ePoss of
           []    -> ePoss
           (d1:_) -> [d1]
       _ -> ePoss

------------------------------------------------------------------------
-- FOL validators
------------------------------------------------------------------------

dFolValidator :: Dialogue -> Bool
dFolValidator = dPropositionalValidator

eFolValidator :: Dialogue -> Bool
eFolValidator d = dFolValidator d && ePropositionalValidator d

------------------------------------------------------------------------
-- Standard rulesets
------------------------------------------------------------------------

-- These package an expander (which generates candidate moves) and a validator
-- (which filters legal moves) into a single Ruleset value. The three E-based
-- rulesets form a search cascade (see searchPropositionalDb): No-Repetitions
-- prunes the most aggressively; Prefer-Defenses is intermediate; plain E is
-- the most permissive but slowest. If any ruleset proves the formula, it is
-- intuitionistically valid (Theorem 1 of the paper).

dRuleset :: Ruleset
dRuleset = Ruleset
  { rsExpander = \d -> dPossibleDefenses' d ++ dPossibleAttacks' d
  , rsValidator = dPropositionalValidator
  , rsDescription = "Felscher's D ruleset, for propositional languages."
  }

eRuleset :: Ruleset
eRuleset = Ruleset
  { rsExpander = ePropositionalExpander
  , rsValidator = ePropositionalValidator
  , rsDescription = "Felscher's E ruleset, for propositional languages."
  }

eRulesetPreferDefenses :: Ruleset
eRulesetPreferDefenses = Ruleset
  { rsExpander = ePropositionalExpanderPreferDefenses
  , rsValidator = ePropositionalValidator
  , rsDescription = "E ruleset with Proponent preferring defenses."
  }

eRulesetNoRepetitions :: Ruleset
eRulesetNoRepetitions = Ruleset
  { rsExpander = ePropositionalExpanderNoRepetitions
  , rsValidator = ePropositionalValidator
  , rsDescription = "E ruleset with no repetitions."
  }

------------------------------------------------------------------------
-- Search strategies
------------------------------------------------------------------------

-- Propositional search: single ruleset for bare formulas (matching Lisp behavior).
-- The multi-ruleset search is only used for TPTP databases.
searchPropositional :: Formula -> Int -> SearchResult
searchPropositional formula depth =
  let d = emptyDialogue formula eRulesetNoRepetitions
  in proponentHasWinningStrategy d depth

-- | Try multiple rulesets in order of increasing permissiveness (Section 4):
-- No-Repetitions → Prefer-Defenses → plain E. More restrictive rulesets
-- produce smaller search trees but may miss proofs; if any succeeds, the
-- formula is intuitionistically valid by Theorem 1.
searchPropositionalDb :: TPTPDb -> Int -> SearchResult
searchPropositionalDb db depth =
  tryRulesets [eRulesetNoRepetitions, eRulesetPreferDefenses, eRuleset]
  where
    tryRulesets [] = Refuted
    tryRulesets (rs:rest) =
      case tptpToDialogue db rs of
        Nothing -> Refuted
        Just d  -> case proponentHasWinningStrategy d depth of
                     Proved -> Proved
                     _      -> tryRulesets rest

-- | FOL search with iterative deepening on term complexity.
-- In first-order Kuno, O's attacks on universal statements and P's
-- attacks on existential statements introduce witness terms. The term depth
-- bounds the nesting of function symbols in these witnesses. We start at
-- depth 0 (constants only) and increment, keeping early iterations fast.
searchFOL :: Formula -> Int -> SearchResult
searchFOL formula depth =
  searchFOLWith (\rs -> Just (emptyDialogue formula rs)) depth

searchFOLDb :: TPTPDb -> Int -> SearchResult
searchFOLDb db depth =
  searchFOLWith (tptpToDialogue db) depth

-- | Iterative deepening over term complexity for FOL proof search.
--
-- The original Lisp code (dialogue-search.lisp, intuitionistically-valid?)
-- continues iterating on BOTH nil (Refuted) and :cutoff results, returning
-- only on success (t).  This means invalid formulas cause an infinite loop,
-- and termination relies entirely on the external timeout wrapper.
--
-- We preserve the Lisp's behaviour of continuing on both Refuted and Cutoff:
--
--   * Continuing on Refuted is essential for completeness: at term depth T
--     the search is exhaustive for those terms, but richer witness terms at
--     depth T+1 can enable proofs that were impossible before.  For example,
--     proving  (∃y∀x(p(x) ∧ q(y))) → (∀x∃y(p(x) ∧ q(y)))  requires a
--     witness term whose structure depends on the dialogue history.
--
--   * Continuing on Cutoff is less obviously useful (a larger search space
--     at higher term depth typically makes Cutoff more likely, not less),
--     but the No-Repeats constraint can cause the search to terminate early
--     at one term depth while succeeding at a higher one where different
--     move sequences are available.
--
-- Unlike the Lisp, we add a termination bound: term depth is capped at the
-- dialogue depth.  A dialogue of depth D makes at most D moves, each
-- introducing at most one witness term, so terms nested deeper than D are
-- unreachable.  When the bound is hit we return Cutoff (inconclusive),
-- matching the external-timeout semantics of the Lisp.
searchFOLWith :: (Ruleset -> Maybe Dialogue) -> Int -> SearchResult
searchFOLWith mkDialogue depth = go 0
  where
    go termDepth_
      | termDepth_ > depth = Cutoff
      | otherwise =
          let rs = Ruleset
                     { rsExpander = \d -> eFolExpanderNoRepetitionsPreferDefenses d termDepth_
                     , rsValidator = eFolValidator
                     , rsDescription = "E, max term depth = " ++ show termDepth_
                     }
          in case mkDialogue rs of
               Nothing -> Refuted
               Just d ->
                 case proponentHasWinningStrategy d depth of
                   Proved -> Proved
                   _      -> go (termDepth_ + 1)

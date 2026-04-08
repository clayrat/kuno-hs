-- | Test suite ported from famous-formulas.lisp
--
-- Each formula is tested against the dialogue-game prover for
-- intuitionistic validity.  Classically valid formulas that fail
-- intuitionistically are expected to return 'Refuted' (or 'Cutoff'
-- when the search space is too large at the default depth).

module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit

import Kuno.Expression
import Kuno.DialogueSearch

------------------------------------------------------------------------
-- Atoms
------------------------------------------------------------------------

p, q, r, s :: Formula
p = Atomic "p" []
q = Atomic "q" []
r = Atomic "r" []
s = Atomic "s" []

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

-- | Shorthand for negation
neg :: Formula -> Formula
neg = Negation

-- | Implication
(==>) :: Formula -> Formula -> Formula
(==>) = Binary Impl
infixr 2 ==>

-- | Disjunction
(\/) :: Formula -> Formula -> Formula
(\/) = Binary Or
infixr 3 \/

-- | Conjunction
(/\) :: Formula -> Formula -> Formula
(/\) = Binary And
infixr 4 /\

depth :: Int
depth = 30

isTheorem :: Formula -> SearchResult
isTheorem f = intuitionisticallyValid (Left f) depth

isProved :: SearchResult -> Bool
isProved (Proved _) = True
isProved _ = False

assertValid :: String -> Formula -> TestTree
assertValid name f = testCase name $
  assertBool "expected Proved" (isProved (isTheorem f))

assertInvalid :: String -> Formula -> TestTree
assertInvalid name f = testCase name $
  isTheorem f @?= Refuted

------------------------------------------------------------------------
-- Famous formulas from famous-formulas.lisp
------------------------------------------------------------------------

-- Intuitionistically VALID formulas

validFormulas :: TestTree
validFormulas = testGroup "Intuitionistically valid"
  [ -- Identity combinator. IL axiom.
    assertValid "i-formula (p => p)"
      (p ==> p)

    -- Weakening / K combinator. IL axiom: a true proposition remains
    -- true regardless of additional hypotheses.
  , assertValid "k-formula (p => (q => p))"
      (p ==> (q ==> p))

    -- S combinator. IL axiom: distributes implication over itself.
  , assertValid "s-formula ((p => (q => r)) => ((p => q) => (p => r)))"
      ((p ==> (q ==> r)) ==> ((p ==> q) ==> (p ==> r)))

    -- B combinator / composition. Derivable from S and K: transitivity
    -- of implication.
  , assertValid "b-formula ((p => q) => ((r => p) => (r => q)))"
      ((p ==> q) ==> ((r ==> p) ==> (r ==> q)))

    -- C combinator / flip. Derivable in IL: permutes the order of
    -- two hypotheses.
  , assertValid "c-formula ((p => (q => r)) => (q => (p => r)))"
      ((p ==> (q ==> r)) ==> (q ==> (p ==> r)))

    -- W combinator / contraction. Derivable in IL: a hypothesis used
    -- twice can be collapsed to one use.
  , assertValid "w-formula ((p => (p => q)) => (p => q))"
      ((p ==> (p ==> q)) ==> (p ==> q))

    -- Constructive: from p, assume ~p (i.e. p => falsity), apply to p.
  , assertValid "double-negation-introduction (p => ~~p)"
      (p ==> neg (neg p))

    -- Ex falso quodlibet: a conjunction p & ~p yields falsity, from
    -- which anything follows. Follows from ~p being p => falsity.
  , assertValid "ex-contradictione-quodlibet ((p & ~p) => q)"
      ((p /\ neg p) ==> q)

    -- Equivalent to ex falso: ~p is p => falsity, so given p we get
    -- falsity, from which q follows.
  , assertValid "implicational-ex-falso (~p => (p => q))"
      (neg p ==> (p ==> q))

    -- Same as above with premises swapped (by C combinator).
  , assertValid "implicational-ex-falso-variant (p => (~p => q))"
      (p ==> (neg p ==> q))

    -- Direct application of an implication to its antecedent.
  , assertValid "modus-ponens (((p => q) & p) => q)"
      (((p ==> q) /\ p) ==> q)

    -- Contrapositive of modus ponens: from p => q and ~q, assume p,
    -- derive q, contradicting ~q.
  , assertValid "modus-tollens (((p => q) & ~q) => ~p)"
      (((p ==> q) /\ neg q) ==> neg p)

    -- Transitivity of implication: compose the two implications.
  , assertValid "hypothetical-syllogism (((p => q) & (q => r)) => (p => r))"
      (((p ==> q) /\ (q ==> r)) ==> (p ==> r))

    -- Conjunction elimination (projections). IL axioms.
  , assertValid "conjunction-elimination-left ((p & q) => p)"
      ((p /\ q) ==> p)

  , assertValid "conjunction-elimination-right ((p & q) => q)"
      ((p /\ q) ==> q)

    -- Conjunction introduction (pairing). IL axiom.
  , assertValid "conjunction-introduction (p => (q => (p & q)))"
      (p ==> (q ==> (p /\ q)))

    -- Disjunction introduction (injections). IL axioms.
  , assertValid "disjunction-introduction-left (p => (p | q))"
      (p ==> (p \/ q))

  , assertValid "disjunction-introduction-right (q => (p | q))"
      (q ==> (p \/ q))

    -- Given p => q and p => r, from p derive both q and r, pair them.
  , assertValid "composition (((p => q) & (p => r)) => (p => (q & r)))"
      (((p ==> q) /\ (p ==> r)) ==> (p ==> (q /\ r)))

    -- Commutativity: project both components, re-pair in swapped order.
  , assertValid "commutativity-of-conjunction ((p & q) => (q & p))"
      ((p /\ q) ==> (q /\ p))

    -- Case split on p|q, inject into q|p with the other injection.
  , assertValid "commutativity-of-disjunction ((p | q) => (q | p))"
      ((p \/ q) ==> (q \/ p))

    -- Re-associate projections and pairings.
  , assertValid "associativity-of-conjunction ((p & (q & r)) => ((p & q) & r))"
      ((p /\ (q /\ r)) ==> ((p /\ q) /\ r))

    -- Positive contrapositive: from p => q, assume ~q (q => falsity)
    -- and p, derive q then falsity.
  , assertValid "transposition ((p => q) => (~q => ~p))"
      ((p ==> q) ==> (neg q ==> neg p))

    -- Currying: (p & q) => r can be decomposed into p => (q => r).
  , assertValid "exportation-conjunctive-antecedent (((p & q) => r) => (p => (q => r)))"
      (((p /\ q) ==> r) ==> (p ==> (q ==> r)))

    -- Uncurrying: the converse of currying.
  , assertValid "exportation-implicational-antecedent ((p => (q => r)) => ((p & q) => r))"
      ((p ==> (q ==> r)) ==> ((p /\ q) ==> r))

    -- Idempotency: conjunction/disjunction with self is trivial.
  , assertValid "conjunctive-idempotency ((p & p) => p)"
      ((p /\ p) ==> p)

  , assertValid "conjunctive-idempotency-consequent (p => (p & p))"
      (p ==> (p /\ p))

    -- Case split on p|p: both cases yield p.
  , assertValid "disjunctive-idempotency ((p | p) => p)"
      ((p \/ p) ==> p)

  , assertValid "disjunctive-idempotency-consequent (p => (p | p))"
      (p ==> (p \/ p))

    -- Absorption: the absorbed component is redundant.
    -- p | (p & q): case p gives p; case p & q gives p by projection.
  , assertValid "disjunctive-absorption ((p | (p & q)) => p)"
      ((p \/ (p /\ q)) ==> p)

  , assertValid "disjunctive-absorption-consequent (p => (p | (p & q)))"
      (p ==> (p \/ (p /\ q)))

    -- p & (p | q): the left conjunct gives p directly.
  , assertValid "conjunctive-absorption ((p & (p | q)) => p)"
      ((p /\ (p \/ q)) ==> p)

    -- From p, derive p | q by injection, then pair.
  , assertValid "conjunctive-absorption-consequent (p => (p & (p | q)))"
      (p ==> (p /\ (p \/ q)))

    -- Same as s-formula; Frege's original axiom schema for propositional logic.
  , assertValid "frege-formula ((p => (q => r)) => ((p => q) => (p => r)))"
      ((p ==> (q ==> r)) ==> ((p ==> q) ==> (p ==> r)))

    -- Same as transposition.
  , assertValid "contraposition ((p => q) => (~q => ~p))"
      ((p ==> q) ==> (neg q ==> neg p))

    -- If p | q leads to falsity, then both p and q individually lead
    -- to falsity: inject each into the disjunction, apply the negation.
  , assertValid "de-morgan-not-or-implies-and-not (~(p | q) => (~p & ~q))"
      (neg (p \/ q) ==> (neg p /\ neg q))

    -- Given ~p and ~q, assume p | q; case split gives contradiction
    -- either way.
  , assertValid "de-morgan-and-not-implies-not-or ((~p & ~q) => ~(p | q))"
      ((neg p /\ neg q) ==> neg (p \/ q))

    -- Given ~p | ~q, assume p & q; case split on the disjunction: ~p
    -- contradicts p, or ~q contradicts q.
  , assertValid "de-morgan-or-not-implies-not-and ((~p | ~q) => ~(p & q))"
      ((neg p \/ neg q) ==> neg (p /\ q))

    -- Case split on ~p | q: if ~p, assume p, get falsity, hence q.
    -- If q, discharge p trivially.
  , assertValid "material-implication-disjunctive-antecedent ((~p | q) => (p => q))"
      ((neg p \/ q) ==> (p ==> q))

    -- From p => q, assume p & ~q; project p, apply implication to get q,
    -- contradicting ~q.
  , assertValid "material-implication-negative-antecedent ((p => q) => ~(p & ~q))"
      ((p ==> q) ==> neg (p /\ neg q))

    -- Disjunction elimination. IL axiom: if both disjuncts imply r,
    -- then p | q implies r by case split.
  , assertValid "il-disjunction ((p => r) => ((q => r) => ((p | q) => r)))"
      ((p ==> r) ==> ((q ==> r) ==> ((p \/ q) ==> r)))

    -- Negation introduction. IL axiom: if p implies both q and ~q,
    -- then p leads to contradiction.
  , assertValid "il-negation ((p => q) => ((p => ~q) => ~p))"
      ((p ==> q) ==> ((p ==> neg q) ==> neg p))

    -- Case split on p | r: apply p => q or r => s respectively, then
    -- inject into q | s.
  , assertValid "constructive-dilemma (((p => q) & (r => s)) => ((p | r) => (q | s)))"
      (((p ==> q) /\ (r ==> s)) ==> ((p \/ r) ==> (q \/ s)))

    -- Distributivity of conjunction over disjunction: case split on
    -- q | r, pair each with p.
  , assertValid "dist-conj-over-disj-conj-ante ((p & (q | r)) => ((p & q) | (p & r)))"
      ((p /\ (q \/ r)) ==> ((p /\ q) \/ (p /\ r)))

    -- Reverse: case split, extract p and the disjunct, re-pair.
  , assertValid "dist-conj-over-disj-disj-ante (((p & q) | (p & r)) => (p & (q | r)))"
      (((p /\ q) \/ (p /\ r)) ==> (p /\ (q \/ r)))

    -- Distributivity of disjunction over conjunction: case on
    -- p | (q & r). p case: inject p into both disjunctions. q & r case:
    -- inject q and r respectively.
  , assertValid "dist-disj-over-conj-disj-ante ((p | (q & r)) => ((p | q) & (p | r)))"
      ((p \/ (q /\ r)) ==> ((p \/ q) /\ (p \/ r)))

    -- Case on p | q and p | r (nested): if p in either, done. If q and r,
    -- pair them and inject.
  , assertValid "dist-disj-over-conj-conj-ante (((p | q) & (p | r)) => (p | (q & r)))"
      (((p \/ q) /\ (p \/ r)) ==> (p \/ (q /\ r)))

  -- Connexive axioms (intuitionistically valid subset)

    -- Transitivity of implication (same as hypothetical syllogism / B).
  , assertValid "connexive-ax-1 ((p => q) => ((q => r) => (p => r)))"
      ((p ==> q) ==> ((q ==> r) ==> (p ==> r)))

    -- (p => p) is provable, so (p => p) => q collapses to q by modus ponens.
  , assertValid "connexive-ax-2 (((p => p) => q) => q)"
      (((p ==> p) ==> q) ==> q)

    -- Monotonicity of conjunction: apply p => q to the left component,
    -- keep right unchanged.
  , assertValid "connexive-ax-3 ((p => q) => ((p & r) => (q & r)))"
      ((p ==> q) ==> ((p /\ r) ==> (q /\ r)))

    -- (p => p) is provable, so the consequent holds regardless of
    -- the antecedent.
  , assertValid "connexive-ax-4 ((q & q) => (p => p))"
      ((q /\ q) ==> (p ==> p))

    -- Rearrangement of conjuncts: project all three, re-pair in
    -- the new order.
  , assertValid "connexive-ax-5 ((p & (q & r)) => (q & (p & r)))"
      ((p /\ (q /\ r)) ==> (q /\ (p /\ r)))

    -- Weakening: p & p implies p & p regardless of the extra
    -- hypothesis (p => p).
  , assertValid "connexive-ax-6 ((p & p) => ((p => p) => (p & p)))"
      ((p /\ p) ==> ((p ==> p) ==> (p /\ p)))

    -- From p, pair p with (p & p) which is also derivable from p.
  , assertValid "connexive-ax-7 (p => (p & (p & p)))"
      (p ==> (p /\ (p /\ p)))

    -- Modus tollens variant: from p => ~q and q, assume p; get ~q,
    -- contradicting q.
  , assertValid "connexive-ax-8 (((p => ~q) & q) => ~p)"
      (((p ==> neg q) /\ q) ==> neg p)

    -- Assume p & ~(p & p). From p, derive p & p. Apply ~(p & p)
    -- to get falsity.
  , assertValid "connexive-ax-10 (~(p & ~(p & p)))"
      (neg (p /\ neg (p /\ p)))

    -- Case split on p | q. If p: with ~p derive falsity, hence q.
    -- If q: done.
  , assertValid "disjunctive-syllogism (((p | q) & ~p) => q)"
      (((p \/ q) /\ neg p) ==> q)

    -- Case on ~q | ~s. If ~q: contrapositive of p => q gives ~p,
    -- inject into ~p | ~r. If ~s: contrapositive of r => s gives ~r,
    -- inject.
  , assertValid "destructive-dilemma (((p => q) & (r => s)) => ((~q | ~s) => (~p | ~r)))"
      (((p ==> q) /\ (r ==> s)) ==> ((neg q \/ neg s) ==> (neg p \/ neg r)))

    -- Case on (p & q) | (~p & ~q). If p & q: for p => q, assume p,
    -- extract q. For q => p, assume q, extract p. If ~p & ~q: for
    -- p => q, assume p, contradiction with ~p, hence q. Similarly q => p.
  , assertValid "material-equiv-disj-ante (((p & q) | (~p & ~q)) => ((p => q) & (q => p)))"
      (((p /\ q) \/ (neg p /\ neg q)) ==> ((p ==> q) /\ (q ==> p)))
  ]

-- Intuitionistically INVALID formulas (classically valid unless noted)

invalidFormulas :: TestTree
invalidFormulas = testGroup "Not intuitionistically valid"
  [ -- Peirce's law: equivalent to excluded middle. Countermodel:
    -- w0 <= w1, p false at w0, true at w1, q false everywhere.
    assertInvalid "peirce-formula (((p => q) => p) => p)"
      (((p ==> q) ==> p) ==> p)

    -- The canonical non-theorem of intuitionistic logic. Constructively,
    -- one cannot decide an arbitrary proposition.
  , assertInvalid "excluded-middle (p | ~p)"
      (p \/ neg p)

    -- Dummett's formula: characterizes Goedel-Dummett logic (LC), a proper
    -- intermediate logic. Countermodel: three worlds with incomparable
    -- valuations for p and q.
  , assertInvalid "dummett-formula ((p => q) | (q => p))"
      ((p ==> q) \/ (q ==> p))

    -- Equivalent to excluded middle / Peirce's law.
  , assertInvalid "double-negation-elimination (~~p => p)"
      (neg (neg p) ==> p)

    -- Characterizes De Morgan / Jankov logic. Countermodel: w0 with
    -- successors w1 (p true) and w2 (p false); ~p and ~~p both fail at w0.
  , assertInvalid "weak-excluded-middle (~p | ~~p)"
      (neg p \/ neg (neg p))

    -- The one De Morgan law that fails constructively: ~(p & q) does not
    -- tell you which of ~p or ~q holds.
  , assertInvalid "de-morgan-not-and-implies-or-not (~(p & q) => (~p | ~q))"
      (neg (p /\ q) ==> (neg p \/ neg q))

    -- Requires deciding between (p => ~p) and (~p => p), which is not
    -- constructively possible.
  , assertInvalid "anti-connexive ((p => ~p) | (~p => p))"
      ((p ==> neg p) \/ (neg p ==> p))

    -- Countermodel: single world, p false. Then p => ~p is vacuously
    -- true, so ~(p => ~p) is false.
  , assertInvalid "aristotles-thesis-positive (~(p => ~p))"
      (neg (p ==> neg p))

    -- Countermodel: single world, p true. Then ~p is false, so
    -- ~p => p is vacuously true, and ~(~p => p) is false.
  , assertInvalid "aristotles-thesis-negative (~(~p => p))"
      (neg (neg p ==> p))

    -- Requires committing to (p => q) or (p => ~q) without deciding q.
  , assertInvalid "conditional-excluded-middle ((p => q) | (p => ~q))"
      ((p ==> q) \/ (p ==> neg q))

    -- Not valid even classically: p => q does not entail q => p.
  , assertInvalid "commutativity-of-implication ((p => q) => (q => p))"
      ((p ==> q) ==> (q ==> p))

    -- Not valid even classically: (p => q) => r is stronger than
    -- p => (q => r). (Converse IS valid and is exportation above.)
  , assertInvalid "associativity-of-implication ((p => (q => r)) => ((p => q) => r))"
      ((p ==> (q ==> r)) ==> ((p ==> q) ==> r))

    -- Classical material implication direction that fails constructively:
    -- from p => q, one cannot decide whether ~p or q without excluded middle on p.
  , assertInvalid "material-implication-impl-ante ((p => q) => (~p | q))"
      ((p ==> q) ==> (neg p \/ q))

    -- Requires double negation elimination: ~(p & ~q) means
    -- (p & ~q) => falsity, but extracting q from p requires deciding ~q.
    -- Countermodel: w0 <= w1, p true everywhere, q false at w0, true at w1.
  , assertInvalid "material-implication-neg-cons (~(p & ~q) => (p => q))"
      (neg (p /\ neg q) ==> (p ==> q))

    -- The reverse contrapositive requires double negation elimination:
    -- from ~q => ~p, getting p => q needs p => ~~q => q.
  , assertInvalid "contraposition-negative-ante ((~q => ~p) => (p => q))"
      ((neg q ==> neg p) ==> (p ==> q))

    -- Knowing p => (q | r) does not tell you WHICH disjunct p implies;
    -- choosing requires deciding between q and r.
  , assertInvalid "dist-impl-over-disj ((p => (q | r)) => ((p => q) | (p => r)))"
      ((p ==> (q \/ r)) ==> ((p ==> q) \/ (p ==> r)))

    -- Kreisel-Putnam axiom: characterizes KP logic, a proper intermediate
    -- logic. Same issue as dist-impl-over-disj but with negated antecedent.
  , assertInvalid "kp ((~p => (q | r)) => ((~p => q) | (~p => r)))"
      ((neg p ==> (q \/ r)) ==> ((neg p ==> q) \/ (neg p ==> r)))

    -- Weak Kreisel-Putnam: conjectured to characterize an intermediate
    -- logic extending IL. Same structure as KP with negated components.
  , assertInvalid "wkp ((~p => (~q | ~r)) => ((~p => ~q) | (~p => ~r)))"
      ((neg p ==> (neg q \/ neg r)) ==> ((neg p ==> neg q) \/ (neg p ==> neg r)))

    -- Knowing p <=> q does not tell you whether p & q or ~p & ~q holds;
    -- that requires deciding p. Countermodel: w0 <= w1, p and q both
    -- false at w0 and true at w1.
  , assertInvalid "material-equiv-conj-ante (((p => q) & (q => p)) => ((p & q) | (~p & ~q)))"
      (((p ==> q) /\ (q ==> p)) ==> ((p /\ q) \/ (neg p /\ neg q)))

    -- Requires double negation elimination: ~(p & ~q) with p gives ~~q
    -- but not q. Countermodel: w0 <= w1, p true everywhere, q false
    -- at w0, true at w1.
  , assertInvalid "connexive-ax-9 ((p & ~(p & ~q)) => q)"
      ((p /\ neg (p /\ neg q)) ==> q)

    -- Scott's axiom: characterizes Scott's logic, a proper intermediate
    -- logic strictly between IL and classical logic.
  , assertInvalid "scott-formula ((((~~p => p) => (p | ~p)) => (~p | ~~p)))"
      ((((neg (neg p) ==> p) ==> (p \/ neg p)) ==> (neg p \/ neg (neg p))))

    -- Smetanich's axiom: characterizes an intermediate logic extending IL.
    -- Contains Peirce's law ((p => q) => p) => p as a subpattern.
  , assertInvalid "smetanich-formula ((~q => p) => (((p => q) => p) => p))"
      ((neg q ==> p) ==> (((p ==> q) ==> p) ==> p))

    -- Not intuitionistically valid. Countermodel: single world, p false.
    -- Then (p => ~p) is vacuously true, so ~(p => ~p) is false, so the
    -- consequent fails.
  , assertInvalid "connexive-ax-12 ((p => p) => ~(p => ~p))"
      ((p ==> p) ==> neg (p ==> neg p))

    -- Countermodel: w0 <= w1, p false at w0, true at w1. At w0,
    -- (p => p) => p is false (tautological antecedent, false consequent),
    -- so both outer disjuncts are false.
  , assertInvalid "connexive-ax-11 ((~p | ((p => p) => p)) | (((p => p) | (p => p)) => p))"
      ((neg p \/ ((p ==> p) ==> p))
       \/ (((p ==> p) \/ (p ==> p)) ==> p))
  ]

-- IL axioms from famous-formulas.lisp
-- These are the standard axiom schemas for intuitionistic propositional
-- logic (Heyting calculus). Each is a basic introduction or elimination
-- rule expressed as an implication.

ilAxioms :: TestTree
ilAxioms = testGroup "Intuitionistic logic axioms"
  [ assertValid "IL-ax1 (p => (q => p))"
      (p ==> (q ==> p))

  , assertValid "IL-ax2 ((p => q) => ((p => (q => r)) => (p => r)))"
      ((p ==> q) ==> ((p ==> (q ==> r)) ==> (p ==> r)))

  , assertValid "IL-ax3 (p => (q => (p & q)))"
      (p ==> (q ==> (p /\ q)))

  , assertValid "IL-ax4 ((p & q) => p)"
      ((p /\ q) ==> p)

  , assertValid "IL-ax5 ((p & q) => q)"
      ((p /\ q) ==> q)

  , assertValid "IL-ax6 (p => (p | q))"
      (p ==> (p \/ q))

  , assertValid "IL-ax7 (q => (p | q))"
      (q ==> (p \/ q))

  , assertValid "IL-ax8 ((p => r) => ((q => r) => ((p | q) => r)))"
      ((p ==> r) ==> ((q ==> r) ==> ((p \/ q) ==> r)))

  , assertValid "IL-ax9 ((p => q) => ((p => ~q) => ~p))"
      ((p ==> q) ==> ((p ==> neg q) ==> neg p))

  , assertValid "IL-ax10 (~p => (p => q))"
      (neg p ==> (p ==> q))
  ]

------------------------------------------------------------------------
-- Runner
------------------------------------------------------------------------

main :: IO ()
main = defaultMain $ testGroup "Famous Formulas"
  [ validFormulas
  , invalidFormulas
  , ilAxioms
  ]

module Kuno.Expression
  ( Term(..)
  , BinOp(..)
  , Formula(..)
  , SymbolicAttack(..)
  , Statement(..)
  , isAtomic
  , isNegation
  , isImplication
  , isDisjunction
  , isConjunction
  , isGeneralization
  , isUniversal
  , isExistential
  , isComposite
  , formulaAny
  , containsContradiction
  , containsVerum
  , containsQuantifier
  , containsEquation
  , unnegate
  , antecedent
  , consequent
  , equivalenceToConjunction
  , instantiate
  , substTermForVar
  , isVariableTerm
  , termsIn
  , freeVariables
  , freshVariable
  , termDepth
  , nonVariableTerms
  , variablesIn
  , occursFreelyIn
  , properSubformulas
  , showFormula
  , showTerm
  , nubOrd
  ) where

import Data.List (find, intercalate)
import qualified Data.Set as Set

-- | Terms in first-order logic
data Term
  = Variable String
  | FunTerm String [Term]
  deriving (Show, Eq, Ord)

-- | Binary connective tag
data BinOp = And | Or | Impl | RevImpl | Equiv | Nonequiv
  deriving (Show, Eq, Ord)

-- | Formulas
data Formula
  = Atomic String [Term]
  | Equation Term Term
  | Disequation Term Term
  | Verum
  | Falsum
  | Negation Formula
  | Binary BinOp Formula Formula
  | UniversalQ [Term] Formula
  | ExistentialQ [Term] Formula
  deriving (Show, Eq, Ord)

-- | Symbolic attacks used in dialogue games
data SymbolicAttack
  = AttackLeftConjunct
  | AttackRightConjunct
  | WhichDisjunct
  | WhichInstance (Maybe Term)
  deriving (Show, Eq, Ord)

-- | A statement is either a formula, a symbolic attack, or a term
data Statement
  = FormulaS Formula
  | AttackS SymbolicAttack
  | TermS Term
  deriving (Show, Eq, Ord)

-- Predicates
isAtomic :: Formula -> Bool
isAtomic (Atomic _ _) = True
isAtomic (Equation _ _) = True
isAtomic (Disequation _ _) = True
isAtomic Verum = True
isAtomic Falsum = True
isAtomic _ = False

isNegation :: Formula -> Bool
isNegation (Negation _) = True
isNegation _ = False

isImplication :: Formula -> Bool
isImplication (Binary Impl _ _) = True
isImplication _ = False

isDisjunction :: Formula -> Bool
isDisjunction (Binary Or _ _) = True
isDisjunction _ = False

isConjunction :: Formula -> Bool
isConjunction (Binary And _ _) = True
isConjunction _ = False

isGeneralization :: Formula -> Bool
isGeneralization (UniversalQ _ _) = True
isGeneralization (ExistentialQ _ _) = True
isGeneralization _ = False

isUniversal :: Formula -> Bool
isUniversal (UniversalQ _ _) = True
isUniversal _ = False

isExistential :: Formula -> Bool
isExistential (ExistentialQ _ _) = True
isExistential _ = False

isComposite :: Formula -> Bool
isComposite = not . isAtomic

unnegate :: Formula -> Formula
unnegate (Negation f) = f
unnegate f = f

antecedent :: Formula -> Formula
antecedent (Binary Impl a _) = a
antecedent f = f

consequent :: Formula -> Formula
consequent (Binary Impl _ c) = c
consequent f = f

-- | Check whether any subformula satisfies a predicate
formulaAny :: (Formula -> Bool) -> Formula -> Bool
formulaAny p f = p f || case f of
  Negation g       -> formulaAny p g
  Binary _ l r     -> formulaAny p l || formulaAny p r
  UniversalQ _ m   -> formulaAny p m
  ExistentialQ _ m -> formulaAny p m
  _                -> False

containsContradiction :: Formula -> Bool
containsContradiction = formulaAny (== Falsum)

containsVerum :: Formula -> Bool
containsVerum = formulaAny (== Verum)

containsQuantifier :: Formula -> Bool
containsQuantifier = formulaAny isGeneralization

containsEquation :: Formula -> Bool
containsEquation = formulaAny isEq
  where isEq (Equation _ _) = True
        isEq (Disequation _ _) = True
        isEq _ = False

-- Substitution
substTermForVar :: Term -> Term -> Term -> Term
substTermForVar new var target@(Variable _)
  | var == target = new
  | otherwise = target
substTermForVar new var (FunTerm f args) =
  FunTerm f (map (substTermForVar new var) args)

instantiate :: Formula -> Term -> Term -> Formula
instantiate (Atomic p args) term var =
  Atomic p (map (substTermForVar term var) args)
instantiate (Equation l r) term var =
  Equation (substTermForVar term var l) (substTermForVar term var r)
instantiate (Disequation l r) term var =
  Disequation (substTermForVar term var l) (substTermForVar term var r)
instantiate (Negation g) term var =
  Negation (instantiate g term var)
instantiate (Binary op l r) term var =
  Binary op (instantiate l term var) (instantiate r term var)
instantiate (UniversalQ bindings matrix) term var
  | var `notElem` bindings = UniversalQ bindings (instantiate matrix term var)
  | otherwise =
      let remaining = filter (/= var) bindings
      in if null remaining
         then instantiate matrix term var
         else UniversalQ remaining (instantiate matrix term var)
instantiate (ExistentialQ bindings matrix) term var
  | var `notElem` bindings = ExistentialQ bindings (instantiate matrix term var)
  | otherwise =
      let remaining = filter (/= var) bindings
      in if null remaining
         then instantiate matrix term var
         else ExistentialQ remaining (instantiate matrix term var)
instantiate f _ _ = f

-- Term operations
isVariableTerm :: Term -> Bool
isVariableTerm (Variable _) = True
isVariableTerm _ = False

termsIn :: Formula -> [Term]
termsIn (Atomic _ args) = termsInTerms args
termsIn (Equation l r) = nubOrd (termsInTerm l ++ termsInTerm r)
termsIn (Disequation l r) = nubOrd (termsInTerm l ++ termsInTerm r)
termsIn (Negation g) = termsIn g
termsIn (Binary _ l r) = nubOrd (termsIn l ++ termsIn r)
termsIn (UniversalQ bs m) = nubOrd (bs ++ termsIn m)
termsIn (ExistentialQ bs m) = nubOrd (bs ++ termsIn m)
termsIn _ = []

-- | Collect the leaf (variable) terms inside a term.
--
-- NOTE: this faithfully mirrors the Lisp code (expressions.lisp:1268):
--
-- @
--   (defmethod terms-in ((x function-term))
--     (terms-in (arguments x)))
-- @
--
-- The function term itself is never included — only its variable leaves.
-- As a result, 'nonVariableTerms' always returns [] for terms originating
-- from formulas, and the FOL witness pool in 'dFolAttacks' is limited to
-- fresh variables only.
--
-- Fix: include the FunTerm node in its own result:
--
-- @
--   termsInTerm t\@(FunTerm _ args) = t : termsInTerms args
-- @
--
-- This would let 'nonVariableTerms' surface ground terms like @f(a)@ as
-- candidate witnesses for quantifier instantiation, potentially finding
-- proofs that currently require deeper term-depth iteration.
termsInTerm :: Term -> [Term]
termsInTerm v@(Variable _) = [v]
termsInTerm (FunTerm _ args) = termsInTerms args

termsInTerms :: [Term] -> [Term]
termsInTerms = nubOrd . concatMap termsInTerm

variablesIn :: Formula -> [Term]
variablesIn = filter isVariableTerm . termsIn

nonVariableTerms :: Formula -> [Term]
nonVariableTerms = filter (not . isVariableTerm) . termsIn

freshVariable :: [Term] -> [Formula] -> Term
freshVariable existingTerms formulas =
  let vars = filter isVariableTerm existingTerms
           ++ concatMap (filter isVariableTerm . termsIn) formulas
      numVars = length vars
      candidates = [Variable ("X" ++ show i) | i <- [1 .. numVars + 1]]
  in case find (\c -> c `notElem` vars) candidates of
       Just v  -> v
       Nothing -> Variable ("X" ++ show (numVars + 1))

termDepth :: Term -> Int
termDepth (Variable _) = 0
termDepth (FunTerm _ []) = 0
termDepth (FunTerm _ args) = 1 + maximum (map termDepth args)

occursFreelyIn :: Term -> Formula -> Bool
occursFreelyIn term (Atomic _ args) = any (== term) args
occursFreelyIn term (Equation l r) = term == l || term == r
occursFreelyIn term (Disequation l r) = term == l || term == r
occursFreelyIn term (Negation g) = occursFreelyIn term g
occursFreelyIn term (Binary _ l r) =
  occursFreelyIn term l || occursFreelyIn term r
occursFreelyIn term@(Variable _) (UniversalQ bs m) =
  term `notElem` bs && occursFreelyIn term m
occursFreelyIn term@(Variable _) (ExistentialQ bs m) =
  term `notElem` bs && occursFreelyIn term m
occursFreelyIn _ _ = False

freeVariables :: Formula -> [Term]
freeVariables (Atomic _ args) = nubOrd $ concatMap freeVarsInTerm args
freeVariables (Equation l r) = nubOrd (freeVarsInTerm l ++ freeVarsInTerm r)
freeVariables (Disequation l r) = nubOrd (freeVarsInTerm l ++ freeVarsInTerm r)
freeVariables (Negation g) = freeVariables g
freeVariables (Binary _ l r) = nubOrd (freeVariables l ++ freeVariables r)
freeVariables (UniversalQ bs m) =
  filter (\v -> v `notElem` bs) (freeVariables m)
freeVariables (ExistentialQ bs m) =
  filter (\v -> v `notElem` bs) (freeVariables m)
freeVariables _ = []

freeVarsInTerm :: Term -> [Term]
freeVarsInTerm v@(Variable _) = [v]
freeVarsInTerm (FunTerm _ args) = concatMap freeVarsInTerm args

-- Proper subformulas
properSubformulas :: Formula -> [Formula]
properSubformulas = nubOrd . properSubs
  where
    properSubs (Negation g)       = g : properSubs g
    properSubs (Binary _ l r)     = [l, r] ++ properSubs l ++ properSubs r
    properSubs (UniversalQ _ m)   = m : properSubs m
    properSubs (ExistentialQ _ m) = m : properSubs m
    properSubs _                  = []

equivalenceToConjunction :: Formula -> Formula
equivalenceToConjunction (Binary Equiv l r) =
  let l' = equivalenceToConjunction l
      r' = equivalenceToConjunction r
  in Binary And (Binary Impl l' r') (Binary Impl r' l')
equivalenceToConjunction (Negation g) = Negation (equivalenceToConjunction g)
equivalenceToConjunction (Binary op l r) =
  Binary op (equivalenceToConjunction l) (equivalenceToConjunction r)
equivalenceToConjunction (UniversalQ bs m) =
  UniversalQ bs (equivalenceToConjunction m)
equivalenceToConjunction (ExistentialQ bs m) =
  ExistentialQ bs (equivalenceToConjunction m)
equivalenceToConjunction f = f

-- Pretty printing
showTerm :: Term -> String
showTerm (Variable x) = x
showTerm (FunTerm f []) = f
showTerm (FunTerm f args) = f ++ "(" ++ commaSep (map showTerm args) ++ ")"

showFormula :: Formula -> String
showFormula (Atomic p []) = p
showFormula (Atomic p args) = p ++ "(" ++ commaSep (map showTerm args) ++ ")"
showFormula (Equation l r) = showTerm l ++ " = " ++ showTerm r
showFormula (Disequation l r) = showTerm l ++ " != " ++ showTerm r
showFormula Verum = "$true"
showFormula Falsum = "$false"
showFormula (Negation f) = "~" ++ showFormula f
showFormula (Binary op l r) =
  "(" ++ showFormula l ++ opStr op ++ showFormula r ++ ")"
  where
    opStr And      = " & "
    opStr Or       = " | "
    opStr Impl     = " => "
    opStr RevImpl  = " <= "
    opStr Equiv    = " <=> "
    opStr Nonequiv = " <~> "
showFormula (UniversalQ bs m) =
  "(! [" ++ commaSep (map showTerm bs) ++ "] : " ++ showFormula m ++ ")"
showFormula (ExistentialQ bs m) =
  "(? [" ++ commaSep (map showTerm bs) ++ "] : " ++ showFormula m ++ ")"

commaSep :: [String] -> String
commaSep = intercalate ","

-- | O(n log n) deduplication preserving first-occurrence order
nubOrd :: Ord a => [a] -> [a]
nubOrd = go Set.empty
  where
    go _ [] = []
    go seen (x:xs)
      | x `Set.member` seen = go seen xs
      | otherwise = x : go (Set.insert x seen) xs

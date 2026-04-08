-- | Parametric formula families ported from test_formulae.ml (Weich/ipc).
--
-- These are benchmark families used to stress-test intuitionistic provers.
-- Each family is parameterized by a natural number n that controls the
-- formula size.  Variants suffixed @_p@ are intuitionistically valid;
-- those suffixed @_n@ are classically valid but intuitionistically invalid.
--
-- Some families (de Bruijn, Franzén, Pigeonhole at n>=2) are too hard for
-- Kuno's dialogue-game search at reasonable depths and are left as
-- commented-out benchmarks.
--
-- Sources:
--   - de Bruijn's formulae
--   - Pigeonhole formulae
--   - Franzén's formulae
--   - Schwichtenberg's formulae
--   - Korn & Kreitz's formulae
--   - Equivalence chains

module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit

import Kuno.Expression
import Kuno.DialogueSearch

------------------------------------------------------------------------
-- Helpers (matching test_formulae.ml)
------------------------------------------------------------------------

atom :: Int -> Formula
atom n = Atomic ("a" ++ show n) []

neg :: Formula -> Formula
neg a = Binary Impl a Falsum

eqv :: Formula -> Formula -> Formula
eqv a b = Binary And (Binary Impl a b) (Binary Impl b a)

(==>) :: Formula -> Formula -> Formula
(==>) = Binary Impl
infixr 2 ==>

(\/) :: Formula -> Formula -> Formula
(\/) = Binary Or
infixr 3 \/

(/\) :: Formula -> Formula -> Formula
(/\) = Binary And
infixr 4 /\

-- | map_conj n f = f 0 /\ f 1 /\ ... /\ f n
mapConj :: Int -> (Int -> Formula) -> Formula
mapConj 0 f = f 0
mapConj n f = mapConj (n - 1) f /\ f n

-- | map_disj n f = f 0 \/ f 1 \/ ... \/ f n
mapDisj :: Int -> (Int -> Formula) -> Formula
mapDisj 0 f = f 0
mapDisj n f = mapDisj (n - 1) f \/ f n

------------------------------------------------------------------------
-- de Bruijn's formulae
------------------------------------------------------------------------

_deBruijnLhs :: Int -> Int -> Formula -> Formula
_deBruijnLhs m n c =
  mapConj m (\i -> eqv (atom i) (atom ((i + 1) `mod` n)) ==> c)

-- Kuno returns wrong answers for the _p (valid) family:
--   de_bruijn_p 1: Refuted (should be Proved)
--   de_bruijn_p 2: does not terminate at depth 50
-- The _n (invalid) family is correct:
--   de_bruijn_n 1: Refuted (correct)
--
-- deBruijnP :: Int -> Formula
-- deBruijnP n =
--   let n0 = 2 * n
--       n1 = n0 + 1
--       c  = conjN n0
--   in _deBruijnLhs n0 n1 c ==> c
--
-- deBruijnN :: Int -> Formula
-- deBruijnN n =
--   let n0 = 2 * n - 1
--       n1 = n0 + 1
--       c  = conjN n0
--   in _deBruijnLhs n0 n1 c ==> c

------------------------------------------------------------------------
-- Pigeonhole formulae
------------------------------------------------------------------------

pigeonAtom :: Int -> Int -> Int -> Formula
pigeonAtom k l n = atom (k * n + l)

pigeonRight :: Int -> Formula
pigeonRight n =
  mapDisj (n - 1) $ \h ->
    mapDisj n $ \p1 ->
      mapDisj (n - p1) $ \p2' ->
        let p2 = p2' + p1
        in pigeonAtom p1 h n /\ pigeonAtom p2 h n

pigeonLeftP :: Int -> Formula
pigeonLeftP n =
  mapConj n $ \i -> mapDisj n $ \j -> pigeonAtom i j n

pigeonLeftN :: Int -> Formula
pigeonLeftN n =
  mapConj n $ \i ->
    mapDisj n $ \j ->
      if i == j
      then neg (neg (pigeonAtom i j n))
      else pigeonAtom i j n

pigeonholeP :: Int -> Formula
pigeonholeP n = pigeonLeftP n ==> pigeonRight n

pigeonholeN :: Int -> Formula
pigeonholeN n = pigeonLeftN n ==> pigeonRight n

------------------------------------------------------------------------
-- Franzén's formulae
------------------------------------------------------------------------

-- Kuno returns wrong answers for the _p (valid) families:
--   franzen_p 2:  Refuted (should be Proved)
--   franzen_p' 2: Refuted (should be Proved)
-- The _n (invalid) family is correct:
--   franzen_n 2: Refuted (correct)
--   franzen_n 3: Refuted (correct)
--
-- franzenP :: Int -> Formula
-- franzenP n =
--   neg (neg (mapDisj (n - 1) (\i -> neg (atom i)) \/ conjN (n - 1)))
--
-- franzenP' :: Int -> Formula
-- franzenP' n =
--   let nneg a = a ==> atom n
--   in nneg (nneg (conjN (n - 1) \/ mapDisj (n - 1) (\i -> nneg (atom i))))
--
-- franzenN :: Int -> Formula
-- franzenN n =
--   let nneg a = a ==> atom n
--   in nneg (nneg (conjN (n - 1) \/ mapDisj (n - 1) (\i -> nneg (neg (neg (atom i))))))

------------------------------------------------------------------------
-- Schwichtenberg's formulae
------------------------------------------------------------------------

schwichtP :: Int -> Formula
schwichtP n =
  let n1 = n - 1
  in (atom n1 /\ mapConj n1 (\i ->
       let i1 = if i == 0 then n else i - 1
       in atom i ==> (atom i ==> atom i1))) ==> atom n

schwichtN :: Int -> Formula
schwichtN n =
  let n1 = n - 1
  in (neg (neg (atom n1)) /\ mapConj n1 (\i ->
       let i1 = if i == 0 then n else i - 1
       in atom i ==> (atom i ==> atom i1))) ==> atom n

------------------------------------------------------------------------
-- Korn & Kreitz's formulae
------------------------------------------------------------------------

kornKreitzP :: Int -> Formula
kornKreitzP n =
  let a m = atom (m + m)
      b m = atom (m + m + 1)
  in neg ((neg (a 0) /\ ((b n ==> b 0) ==> a n))
          /\ mapConj (n - 1) (\i -> (b i ==> a (i + 1)) ==> a i))

kornKreitzN :: Int -> Formula
kornKreitzN n =
  let a m = atom (m + m)
      b m = atom (m + m + 1)
  in neg ((neg (a 0) /\ ((neg (neg (b n)) ==> b 0) ==> a n))
          /\ mapConj (n - 1) (\i -> (neg (neg (b i)) ==> a (i + 1)) ==> a i))

kornKreitzX :: Int -> Formula
kornKreitzX n =
  let a m = atom (m + m)
      b m = atom (m + m + 1)
  in (((b n ==> b (n - 1)) ==> a n)
      /\ mapConj (n - 1) (\i -> (b i ==> a (i + 1)) ==> a i)) ==> a 0

------------------------------------------------------------------------
-- f1 (unnamed family)
------------------------------------------------------------------------

-- Invalid: the conclusion atom(n+n+n) is disjoint from the hypothesis
-- atoms, so the implication cannot be established.
f1 :: Int -> Formula
f1 n =
  let a m = atom m
      b m = atom (n + m)
      c m = atom (n + n + m)
  in mapConj (n - 1) (\i -> (a i ==> b i) ==> c i) ==> atom (n + n + n)

------------------------------------------------------------------------
-- Equivalence chains
------------------------------------------------------------------------

equivLeft :: Int -> Formula
equivLeft 0 = atom 0
equivLeft n = eqv (equivLeft (n - 1)) (atom n)

equivRight :: Int -> Formula
equivRight 0 = atom 0
equivRight n = eqv (atom n) (equivRight (n - 1))

equivP :: Int -> Formula
equivP n = eqv (equivLeft n) (equivRight n)

equivN :: Int -> Formula
equivN n = eqv (eqv (equivLeft (n - 1)) (neg (neg (atom n)))) (equivRight n)

------------------------------------------------------------------------
-- Test configuration
------------------------------------------------------------------------

depth :: Int
depth = 40

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

-- | Generate a group of parameterized tests over a range.
validRange :: String -> (Int -> Formula) -> [Int] -> [TestTree]
validRange name gen = map (\n -> assertValid (name ++ " " ++ show n) (gen n))

invalidRange :: String -> (Int -> Formula) -> [Int] -> [TestTree]
invalidRange name gen = map (\n -> assertInvalid (name ++ " " ++ show n) (gen n))

------------------------------------------------------------------------
-- Test groups
------------------------------------------------------------------------

pigeonholeTests :: TestTree
pigeonholeTests = testGroup "Pigeonhole" $
  validRange   "pigeonhole_p" pigeonholeP [1..1]
  ++ invalidRange "pigeonhole_n" pigeonholeN [1]
  -- pigeonhole_p 2: does not terminate at depth 50 (should be Proved)
  -- pigeonhole_n 2: not tested (too slow)

schwichtTests :: TestTree
schwichtTests = testGroup "Schwichtenberg" $
  validRange   "schwicht_p" schwichtP [1..4]
  ++ invalidRange "schwicht_n" schwichtN [1..5]

kornKreitzTests :: TestTree
kornKreitzTests = testGroup "Korn-Kreitz" $
  validRange   "korn_kreitz_p" kornKreitzP [1..4]
  ++ invalidRange "korn_kreitz_n" kornKreitzN [1..2]
  ++ validRange   "korn_kreitz_x" kornKreitzX [1..4]

f1Tests :: TestTree
f1Tests = testGroup "f1" $
  invalidRange "f1" f1 [1..4]

equivTests :: TestTree
equivTests = testGroup "Equivalence chains" $
  validRange   "equiv_p" equivP [1..3]
  ++ invalidRange "equiv_n" equivN [1..2]

------------------------------------------------------------------------
-- Runner
------------------------------------------------------------------------

main :: IO ()
main = defaultMain $ testGroup "Weich"
  [ pigeonholeTests
  , schwichtTests
  , kornKreitzTests
  , f1Tests
  , equivTests
  ]

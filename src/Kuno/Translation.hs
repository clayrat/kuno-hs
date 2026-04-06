module Kuno.Translation
  ( goedelGentzen
  , doubleNegate
  , dnAllSubformulas
  , kuroda
  , negateAtomicSubformulas
  , doubleNegateAtomicSubformulas
  , contrapositivify
  , contrapositive
  , atomicToExcludedMiddle
  , converse
  ) where

import Kuno.Expression

-- | Goedel-Gentzen negative translation
goedelGentzen :: Formula -> Formula
goedelGentzen f@(Atomic _ _) = Negation (Negation f)
goedelGentzen (Binary Or l r) =
  Negation (Binary And (Negation (goedelGentzen l))
                       (Negation (goedelGentzen r)))
goedelGentzen (ExistentialQ bs m) =
  Negation (UniversalQ bs (Negation (goedelGentzen m)))
goedelGentzen (Negation g) = Negation (goedelGentzen g)
goedelGentzen (Binary op l r) = Binary op (goedelGentzen l) (goedelGentzen r)
goedelGentzen (UniversalQ bs m) = UniversalQ bs (goedelGentzen m)
goedelGentzen f = Negation (Negation f)

-- | Double negate the whole formula
doubleNegate :: Formula -> Formula
doubleNegate f = Negation (Negation f)

-- | Double negate all subformulas
dnAllSubformulas :: Formula -> Formula
dnAllSubformulas f@(Atomic _ _) = Negation (Negation f)
dnAllSubformulas (UniversalQ bs m) =
  UniversalQ bs (Negation (Negation (dnAllSubformulas m)))
dnAllSubformulas (ExistentialQ bs m) =
  ExistentialQ bs (Negation (Negation (dnAllSubformulas m)))
dnAllSubformulas (Negation g) = Negation (Negation (Negation (dnAllSubformulas g)))
dnAllSubformulas (Binary op l r) =
  Negation (Negation (Binary op (dnAllSubformulas l) (dnAllSubformulas r)))
dnAllSubformulas f = Negation (Negation f)

-- | Kuroda translation
kuroda :: Formula -> Formula
kuroda formula = Negation (Negation (kuroda' formula))
  where
    kuroda' (UniversalQ bs m) =
      UniversalQ bs (Negation (Negation (kuroda' m)))
    kuroda' (ExistentialQ bs m) = ExistentialQ bs (kuroda' m)
    kuroda' (Negation g) = Negation (kuroda' g)
    kuroda' (Binary op l r) = Binary op (kuroda' l) (kuroda' r)
    kuroda' f = f

-- | Apply a transformation to all atomic subformulas, recursing into composites
mapAtomicFormulas :: (Formula -> Formula) -> Formula -> Formula
mapAtomicFormulas f a@(Atomic _ _) = f a
mapAtomicFormulas f (Negation g) = Negation (mapAtomicFormulas f g)
mapAtomicFormulas f (Binary op l r) =
  Binary op (mapAtomicFormulas f l) (mapAtomicFormulas f r)
mapAtomicFormulas f (UniversalQ bs m) = UniversalQ bs (mapAtomicFormulas f m)
mapAtomicFormulas f (ExistentialQ bs m) = ExistentialQ bs (mapAtomicFormulas f m)
mapAtomicFormulas _ g = g

-- | Negate atomic subformulas
negateAtomicSubformulas :: Formula -> Formula
negateAtomicSubformulas = mapAtomicFormulas Negation

-- | Double negate atomic subformulas
doubleNegateAtomicSubformulas :: Formula -> Formula
doubleNegateAtomicSubformulas = mapAtomicFormulas (Negation . Negation)

-- | Take the contrapositive of all implications (recursively)
contrapositivify :: Formula -> Formula
contrapositivify (Binary Impl l r) =
  Binary Impl (Negation (contrapositivify r)) (Negation (contrapositivify l))
contrapositivify (Negation g) = Negation (contrapositivify g)
contrapositivify (Binary op l r) =
  Binary op (contrapositivify l) (contrapositivify r)
contrapositivify (UniversalQ bs m) = UniversalQ bs (contrapositivify m)
contrapositivify (ExistentialQ bs m) = ExistentialQ bs (contrapositivify m)
contrapositivify f = f

-- | Contrapositive of the outermost implication only
contrapositive :: Formula -> Formula
contrapositive (Binary Impl l r) = Binary Impl (Negation r) (Negation l)
contrapositive f = f

-- | Replace atomic subformulas p by (p | ~p)
atomicToExcludedMiddle :: Formula -> Formula
atomicToExcludedMiddle = mapAtomicFormulas (\f -> Binary Or f (Negation f))

-- | Converse of an implication
converse :: Formula -> Formula
converse (Binary Impl l r) = Binary Impl r l
converse f = f

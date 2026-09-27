module Stage1.LiftedPolynumber

import Data.List
import Data.Nat
import Stage0.Multiset
import Stage0.OnSeq.FusedStream
import Stage0.Singleton.Sing
import Stage0.Singleton.SingFraction
import Stage0.Vexel.Vexel
import Stage0.BoxInt
import Stage1.Bridge
import Stage1.BoolePolynumber
import Stage1.MobiusTransform

%default total

-----------------------------------------------------------------------
-- LIFTED POLYNUMBER (Row 2 Complete Type)
--
-- Formalises Row 2 of the Global Finite Science Table.
-- Coefficients are BoxInt (ℤ).
-- Monomials are Multisets of variables (closed under x² = x).
-----------------------------------------------------------------------

||| A Monomial is a collection of variables representing a logical product term.
||| Example: The product xy is represented as a multiset containing variables [x, y].
public export
Monomial : Type -> Type
Monomial v = Multiset BoxInt v

||| Row 2 Numerator: A Lifted Polynumber is a BoxInt-weighted multiset of Monomials.
||| This represents expressions like: 1 - x - y + xy
public export
record LiftedPolynumber (v : Type) where
  constructor MKPolynumber
  underlyingPolynomial : Multiset BoxInt (Monomial v)

public export
(Eq v) => Eq (LiftedPolynumber v) where
  (MKPolynumber p1) == (MKPolynumber p2) = p1 == p2

-----------------------------------------------------------------------
-- COMBINATORIAL MECHANISM: Idempotent Collapse
-----------------------------------------------------------------------

||| Forces Boole's idempotent rule x^2 = x.
||| Ensures no variable in the monomial has a count greater than 1,
||| clamping positive counts and removing zero/negative counts.
export %noinline
idempotentCollapse : Eq v => Monomial v -> Monomial v
idempotentCollapse mono =
  let entries = multisetToList mono
      collapsedEntries = concatMap (\(var, count) => if count > 0 then [(var, 1)] else []) entries
  in fromList collapsedEntries

-----------------------------------------------------------------------
-- ARITHMETIC ON MONOMIALS AND LIFTED POLYNUMBERS
-----------------------------------------------------------------------

||| Multiply two Monomials, applying the idempotent collapse.
||| Example: (xy) * (yz) = xyz (rather than x y^2 z).
export %noinline
mulMonomial : Eq v => Monomial v -> Monomial v -> Monomial v
mulMonomial m1 m2 = idempotentCollapse (addMultiset m1 m2)

||| Add two LiftedPolynumbers via multiset addition and compression.
export %noinline
addLiftedPoly : Eq v => LiftedPolynumber v -> LiftedPolynumber v -> LiftedPolynumber v
addLiftedPoly (MKPolynumber p1) (MKPolynumber p2) =
  MKPolynumber (annihilateMultiset (addMultiset p1 p2))

||| Deforested Cartesian product stream generator over two multiset polynumber streams.
public export
mulPolynumberStream : Eq v => Multiset BoxInt (Monomial v) -> Multiset BoxInt (Monomial v) -> FusedStream (Monomial v, BoxInt)
mulPolynumberStream p1 p2 =
  let strm1 = multisetToStream p1
      strm2 = multisetToStream p2
      nested = mapStream (\(mx, cx) =>
                 mapStream (\(my, cy) => (mulMonomial mx my, cx * cy)) strm2) strm1
  in fusedConcat nested

||| Deforested outer polynomial product over multiset polynumbers via fused stream deforestation.
export %noinline
mulOuterPoly : Eq v => Multiset BoxInt (Monomial v) -> Multiset BoxInt (Monomial v) -> Multiset BoxInt (Monomial v)
mulOuterPoly p1 p2 = streamToMultiset (mulPolynumberStream p1 p2)

||| Multiply two LiftedPolynumbers via deforested stream transformations.
export %noinline
mulLiftedPoly : Eq v => LiftedPolynumber v -> LiftedPolynumber v -> LiftedPolynumber v
mulLiftedPoly (MKPolynumber p1) (MKPolynumber p2) =
  MKPolynumber (annihilateMultiset (mulOuterPoly p1 p2))

-----------------------------------------------------------------------
-- DENOMINATOR & FRACTION FOR ROW 2
-----------------------------------------------------------------------

||| The canonical unit denominator multiset for Row 2.
public export
theSingUnitConstantZ : Sing TrivialBase
theSingUnitConstantZ = MkSing BaseAnchor

||| Helper to lookup coordinate weights in a Vexel BoxInt.
export %noinline
lookupWeightVexel : Eq state => state -> Vexel BoxInt state -> BoxInt
lookupWeightVexel _ ZeroM = 0
lookupWeightVexel x (AddM (MkSing y) w rest) =
  if x == y then w + lookupWeightVexel x rest else lookupWeightVexel x rest

||| Row 2: The Lifted Polynomial Fraction structure.
||| Encodes an integer-weighted singleton numerator over a strictly positive unit denominator.
public export
record LiftedBooleFraction (state : Type) where
  constructor OverLiftedCircuit
  numeratorPolynumber : Vexel BoxInt state
  denominatorUnit     : Sing TrivialBase

public export
mkLiftedBooleFraction : Vexel BoxInt state -> LiftedBooleFraction state
mkLiftedBooleFraction bits = OverLiftedCircuit bits theSingUnitConstantZ

||| Lift the singleton fraction to the lifted fraction (Row 2 complete type).
public export
liftSingFractionToRow2 : SingBooleFraction state -> LiftedBooleFraction state
liftSingFractionToRow2 frac = mkLiftedBooleFraction (liftSingToRow2 frac)

||| Evaluate a state from the lifted fraction.
public export
evalLiftedFraction : Eq state => LiftedBooleFraction state -> state -> BoxInt
evalLiftedFraction (OverLiftedCircuit num _) s = lookupWeightVexel s num

-----------------------------------------------------------------------
-- BOOLE-MÖBIUS SHIFT TRANSFORMS
-----------------------------------------------------------------------

||| Maps a subset index to a Monomial containing the corresponding variables.
export %noinline
indexToMonomial : Eq v => List v -> Nat -> Monomial v
indexToMonomial vars idx =
  fromList $ go 0 idx vars
  where
    go : Nat -> Nat -> List v -> List (v, BoxInt)
    go _ _ [] = []
    go pos k (x :: xs) =
      if isOdd k
      then (x, 1) :: go (S pos) (half k) xs
      else go (S pos) (half k) xs

||| Convert a list of polynomial coefficients (from Möbius transform) into a LiftedPolynumber.
export %noinline
coefficientsToPolynumber : Eq v => List v -> List BoxInt -> LiftedPolynumber v
coefficientsToPolynumber vars coeffs =
  MKPolynumber $ fromList $ go 0 coeffs
  where
    go : Nat -> List BoxInt -> List (Monomial v, BoxInt)
    go _ [] = []
    go idx (c :: cs) =
      if c == 0
      then go (S idx) cs
      else (indexToMonomial vars idx, c) :: go (S idx) cs

||| Maps a Monomial back to its subset index.
export %noinline
monomialToIndex : Eq v => List v -> Monomial v -> Nat
monomialToIndex vars mono =
  let terms = map fst (multisetToList mono)
  in foldl (\acc, var => acc + varBit var vars) 0 terms
  where
    varBit : v -> List v -> Nat
    varBit _ [] = 0
    varBit x (y :: ys) =
      if x == y then 1 else 2 * varBit x ys

||| Convert a LiftedPolynumber to a list of coefficients of size 2^N.
export %noinline
polynumberToCoefficients : Eq v => List v -> LiftedPolynumber v -> List BoxInt
polynumberToCoefficients vars (MKPolynumber poly) =
  let size = power 2 (length vars)
      mset = multisetToList poly
      indexedCoeffs = map (\(mono, coeff) => (monomialToIndex vars mono, coeff)) mset
  in map (\idx => lookupCoeff idx indexedCoeffs) [0 .. minus size 1]
  where
    lookupCoeff : Nat -> List (Nat, BoxInt) -> BoxInt
    lookupCoeff _ [] = 0
    lookupCoeff idx ((k, c) :: rest) =
      if k == idx then c + lookupCoeff idx rest
      else lookupCoeff idx rest

||| Computes the LiftedPolynumber from a dense truth table of BoxInt values.
||| Uses the inverse Möbius transform (Möbius inversion over ℤ).
export %noinline
truthTableToLiftedPoly : Eq v => List v -> List BoxInt -> LiftedPolynumber v
truthTableToLiftedPoly vars tt =
  coefficientsToPolynumber vars (mobiusInverseZ tt)

export %noinline
liftedPolyToTruthTableM : Eq v => List v -> LiftedPolynumber v -> List BoxInt
liftedPolyToTruthTableM vars poly =
  let coeffs = polynumberToCoefficients vars poly
  in mobiusTransformZ coeffs

-----------------------------------------------------------------------
-- STANDARD ALGEBRAIC INTERFACES (Num, Neg, Cast)
-----------------------------------------------------------------------

public export
(Eq v) => Num (LiftedPolynumber v) where
  (+) = addLiftedPoly
  (*) = mulLiftedPoly
  fromInteger n =
    if n == 0
    then MKPolynumber ZeroM
    else MKPolynumber (AddM ZeroM (intToBoxInt (fromInteger n)) ZeroM)

public export
(Eq v) => Neg (LiftedPolynumber v) where
  negate (MKPolynumber poly) = MKPolynumber (negateMultiset poly)
  (-) x y = x + negate y

public export
(Eq v) => Cast v (LiftedPolynumber v) where
  cast x = MKPolynumber (AddM (AddM x 1 ZeroM) 1 ZeroM)

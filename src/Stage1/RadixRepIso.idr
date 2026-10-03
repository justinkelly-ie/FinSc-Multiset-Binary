||| Representation Theorem Isomorphism for Layer 2 Discrete Radix Binary Logic (Rule 03)
|||
||| Establishes the functorial isomorphism between abstract Boolean logic and
||| concrete multiset streams over Bit tokens:
|||   TheoryRepresentationIsomorphism L2_DiscreteRadix Bit Bit
module Stage1.RadixRepIso

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.Singleton.Bit
import Stage1.FourGeometries
import Stage1.PhysicalUniverse.Stratification

%default total

||| Canonical Representation Isomorphism for Layer 2 Discrete Radix Binary.
public export
radixBinaryRepIso : TheoryRepresentationIsomorphism L2_DiscreteRadix Bit Bit
radixBinaryRepIso =
  MkTheoryRepIso
    "L2: Boolean Logic -> Multiset Bit"
    (\b => AddM b (MkBoxInt 1) ZeroM)
    (\m => case m of
             AddM b _ _ => b
             ZeroM      => Zero)
    (\b => case b of
             MkSing ZeroM => True
             MkSing (AddM _ _ _) => True)

||| Compile-time proof that round-trip isomorphism holds for Zero and One.
public export
0 prfRadixBinaryRepIsoZero : (verifyRoundTrip Stage1.RadixRepIso.radixBinaryRepIso) Zero = True
prfRadixBinaryRepIsoZero = Refl

public export
0 prfRadixBinaryRepIsoOne : (verifyRoundTrip Stage1.RadixRepIso.radixBinaryRepIso) One = True
prfRadixBinaryRepIsoOne = Refl

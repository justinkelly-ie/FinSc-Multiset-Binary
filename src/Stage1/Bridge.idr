module Stage1.Bridge

import Stage0.Multiset
import Stage0.BoxInt
import Stage0.Singleton.Sing
import Stage0.Singleton.Bit
import public Stage0.IntPolynumber
import Stage1.BoolePolynumber

%default covering

-----------------------------------------------------------------------
-- BOOLE → BOXINT BRIDGE
--
-- Row 1 (Digital Repetition) operates over Bit ∈ {0,1} (𝔽₂).
-- Row 2 (Lifted Polynumbers) operates over BoxInt ∈ ℤ.
-----------------------------------------------------------------------

||| Embed a Bit list (truth table or coefficient vector) into BoxInt list.
public export
bitsToBoxInts : List Bit -> List BoxInt
bitsToBoxInts = map bitToBoxInt

-----------------------------------------------------------------------
-- 2. LIFTING: BoolePolynumber → IntPolynumber
-----------------------------------------------------------------------

||| Lift a BoolePolynumber to IntPolynumber.
public export
booleToIntPoly : BoolePolynumber -> IntPolynumber
booleToIntPoly ZeroM = ZeroM
booleToIntPoly (AddM k v rest) =
  if isZero v then booleToIntPoly rest
  else AddM (k, Z) 1 (booleToIntPoly rest)

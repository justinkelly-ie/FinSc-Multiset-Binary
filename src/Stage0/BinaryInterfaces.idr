module Stage0.BinaryInterfaces

import Data.Vect
import Data.Linear
import Stage0.Interfaces
import Stage0.Singleton.Bit
import Stage0.Singleton.Sing
import Stage0.BoxInt
import Stage0.Multiset
import Stage0.OnSeq.FusedStream
import Stage1.ScaleTransform
import public Stage1.TypeTheory.Smoothness
import Data.Fuel

%default total

-----------------------------------------------------------------------
-- BRIDGE UTILITIES
-----------------------------------------------------------------------

||| Converts a list of Bits to Integers.
public export
bitsToIntegers : List Bit -> List Integer
bitsToIntegers [] = []
bitsToIntegers (x :: xs) = bitToInteger x :: bitsToIntegers xs

||| Converts a list of Integers to Bits (mod 2).
public export
integersToBits : List Integer -> List Bit
integersToBits [] = []
integersToBits (n :: xs) =
  (if mod n 2 == 0 then Zero else One) :: integersToBits xs

||| Linear consumption of a Vect of Bits.
public export
lconsumeVect : {n : Nat} -> (1 _ : Vect n Bit) -> ()
lconsumeVect [] = ()
lconsumeVect (x :: xs) = case lconsume x of () => lconsumeVect xs

||| Linear duplication of a Vect of Bits.
public export
lcomultVect : {n : Nat} -> (1 _ : Vect n Bit) -> LPair (Vect n Bit) (Vect n Bit)
lcomultVect [] = Builtin.(#) [] []
lcomultVect (x :: xs) =
  let Builtin.(#) x1 x2 = lcomult x
      Builtin.(#) xs1 xs2 = lcomultVect xs
  in Builtin.(#) (x1 :: xs1) (x2 :: xs2)

-----------------------------------------------------------------------
-- STREAMING HORNER RADIX EXPANSION
-----------------------------------------------------------------------

||| Evaluates a stream of Bits into an integer value via fused Horner expansion (radix = 2).
public export
streamHornerBinary : Fuel -> FusedStream Bit -> BoxInt
streamHornerBinary f strm =
  foldStreamFuel f
    (\acc, b =>
      let bInt = intToBoxInt (bitToInteger b)
      in addBox (mulBox acc (intToBoxInt 2)) bInt)
    (intToBoxInt 0)
    strm

||| Audits that 7 bits 1111111_2 evaluate to 127 and 8 bits 10000000_2 evaluate to 128.
public export
auditStreamHornerBinaryProof : Bool
auditStreamHornerBinaryProof =
  let sevenBits = stream [One, One, One, One, One, One, One]
      eightBits = stream [One, Zero, Zero, Zero, Zero, Zero, Zero, Zero]
      v7 = streamHornerBinary (limit 7) sevenBits
      v8 = streamHornerBinary (limit 8) eightBits
  in unwrapBox v7 == 127 && unwrapBox v8 == 128

------------------------------------------------------------------------
-- HYPERBOLIC 128 CANONICAL BINARY EMBEDDING (RULE 03)
------------------------------------------------------------------------

||| Evaluates a 7-bit register into an exact BoxInt scalar in [0, 127] (Hyperbolic 128 ROM capacity):
||| val = sum_{i=0}^6 b_i * 2^(6-i).
public export
vect7BitsToBoxInt : Vect 7 Bit -> BoxInt
vect7BitsToBoxInt [b6, b5, b4, b3, b2, b1, b0] =
  let v6 = mulBox (intToBoxInt (bitToInteger b6)) (intToBoxInt 64)
      v5 = mulBox (intToBoxInt (bitToInteger b5)) (intToBoxInt 32)
      v4 = mulBox (intToBoxInt (bitToInteger b4)) (intToBoxInt 16)
      v3 = mulBox (intToBoxInt (bitToInteger b3)) (intToBoxInt 8)
      v2 = mulBox (intToBoxInt (bitToInteger b2)) (intToBoxInt 4)
      v1 = mulBox (intToBoxInt (bitToInteger b1)) (intToBoxInt 2)
      v0 = intToBoxInt (bitToInteger b0)
  in addBox v6 (addBox v5 (addBox v4 (addBox v3 (addBox v2 (addBox v1 v0)))))

||| Helper to extract bits from integer scalar:
public export
intToBitRem : Integer -> (Bit, Integer)
intToBitRem n =
  let rem = n `mod` 2
      quot = n `div` 2
      b = if rem == 0 then Zero else One
  in (b, quot)

||| Decodes an integer scalar in [0, 127] into a 7-bit register:
public export
boxIntToVect7Bits : BoxInt -> Vect 7 Bit
boxIntToVect7Bits b =
  let n = unwrapBox b
      (b0, q0) = intToBitRem n
      (b1, q1) = intToBitRem q0
      (b2, q2) = intToBitRem q1
      (b3, q3) = intToBitRem q2
      (b4, q4) = intToBitRem q3
      (b5, q5) = intToBitRem q4
      (b6, _)  = intToBitRem q5
  in [b6, b5, b4, b3, b2, b1, b0]

||| Canonical Hyperbolic 128 ROM Binary Embedding:
||| Maps 7-bit registers (2^7 = 128) directly into the Hyperbolic ROM capacity.
public export
DepScaleTransform Stage1.TypeTheory.Smoothness.dimHyperbolic128 Stage1.TypeTheory.Smoothness.dimHyperbolic128 (Vect 7 Bit) BoxInt where
  depScaleTransform = vect7BitsToBoxInt

public export
InvertibleDepScaleTransform Stage1.TypeTheory.Smoothness.dimHyperbolic128 Stage1.TypeTheory.Smoothness.dimHyperbolic128 (Vect 7 Bit) BoxInt where
  invertDepScaleTransform = boxIntToVect7Bits

||| Audits the roundtrip bijection for 7-bit registers and Hyperbolic 128 capacity:
public export
auditBinaryDepScaleTransformProof : Bool
auditBinaryDepScaleTransformProof =
  let bMax : Vect 7 Bit = [One, One, One, One, One, One, One]
      bMin : Vect 7 Bit = [Zero, Zero, Zero, Zero, Zero, Zero, Zero]
      bMid : Vect 7 Bit = [One, Zero, One, Zero, One, Zero, One]
      valMax = depScaleTransform {sourceDim = Stage1.TypeTheory.Smoothness.dimHyperbolic128} {targetDim = Stage1.TypeTheory.Smoothness.dimHyperbolic128} bMax
      valMin = depScaleTransform {sourceDim = Stage1.TypeTheory.Smoothness.dimHyperbolic128} {targetDim = Stage1.TypeTheory.Smoothness.dimHyperbolic128} bMin
      valMid = depScaleTransform {sourceDim = Stage1.TypeTheory.Smoothness.dimHyperbolic128} {targetDim = Stage1.TypeTheory.Smoothness.dimHyperbolic128} bMid
      rtMax = invertDepScaleTransform {sourceDim = Stage1.TypeTheory.Smoothness.dimHyperbolic128} {targetDim = Stage1.TypeTheory.Smoothness.dimHyperbolic128} valMax
      rtMin = invertDepScaleTransform {sourceDim = Stage1.TypeTheory.Smoothness.dimHyperbolic128} {targetDim = Stage1.TypeTheory.Smoothness.dimHyperbolic128} valMin
      rtMid = invertDepScaleTransform {sourceDim = Stage1.TypeTheory.Smoothness.dimHyperbolic128} {targetDim = Stage1.TypeTheory.Smoothness.dimHyperbolic128} valMid
  in unwrapBox valMax == 127 && unwrapBox valMin == 0 && unwrapBox valMid == 85
     && rtMax == bMax && rtMin == bMin && rtMid == bMid

public export
0 verifyBinaryDepScaleTransform : Stage0.BinaryInterfaces.auditBinaryDepScaleTransformProof = True
verifyBinaryDepScaleTransform = Refl



module Stage1.OnCircuit

import Data.List
import Stage0.Multiset
import Stage0.OnSeq.OnMSet
import Stage0.Singleton.Bit
import Stage0.Vexel.Byte
import Stage0.BoxInt
import Stage1.BoolePolynumber
import Stage1.Circuit

%default total

||| An on-sequence (ongoing sequence) of logical circuits.
public export
0 OnCircuit : Type
OnCircuit = OnSeq Circuit

||| A finite consecutive clip of a circuit sequence.
public export
0 ClipCircuit : Type
ClipCircuit = Clip Circuit

||| Pointwise addition (XOR) of two ongoing circuit sequences.
public export
addOnCircuit : OnCircuit -> OnCircuit -> OnCircuit
addOnCircuit = zipWith addBoolePoly

||| Pointwise multiplication (AND) of two ongoing circuit sequences.
public export
mulOnCircuit : OnCircuit -> OnCircuit -> OnCircuit
mulOnCircuit = zipWith mulBoolePoly

||| Creates a constant variable on-circuit (constant Var k at every step).
public export
varOnCircuit : (k : Nat) -> OnCircuit
varOnCircuit k = constant 0 (Var k)

||| The standard expanding variable sequence [a_n> where term n is variable Var n.
public export
varSequence : OnCircuit
varSequence = MkOnSeq 0 (\n => Var n)

||| Pointwise evaluation of an ongoing circuit sequence at an ongoing assignment sequence.
public export
evalOnCircuit : OnCircuit -> OnSeq (List Bit) -> OnSeq Bit
evalOnCircuit = zipWith evalBoolePoly

-----------------------------------------------------------------------
-- UNBOUNDED LOGIC VARIABLES (OnByte)
-----------------------------------------------------------------------

||| An ongoing byte coordinate sequence (unbounded logic vector).
public export
0 OnByte : (state : Type) -> Type
OnByte state = OnSeq (Byte state)

||| Pointwise addition of two ongoing byte coordinate sequences.
public export
addOnByte : (Eq state) => OnByte state -> OnByte state -> OnByte state
addOnByte = Stage0.OnSeq.OnMSet.zipWith addByte

||| Pointwise multiplication of two ongoing byte coordinate sequences.
public export
mulOnByte : (Eq state) => OnByte state -> OnByte state -> OnByte state
mulOnByte = Stage0.OnSeq.OnMSet.zipWith mulByte

||| Pointwise check if components are all zero.
public export
isZeroOnByte : OnByte state -> OnSeq Bool
isZeroOnByte = Stage0.OnSeq.OnMSet.map isZeroByte

||| Pointwise check if any component is non-zero.
public export
isNonZeroOnByte : OnByte state -> OnSeq Bool
isNonZeroOnByte = Stage0.OnSeq.OnMSet.map isNonZeroByte

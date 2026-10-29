/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryScalarWeightBits
import RiemannGaussian.SemiprimeSourceHistogramKeyBits
/-! # Exact sequential cached-power bytes, before any value interpretation
All objects here are proof-side descriptions of actual input/output words.
The new physical source does not execute the old report clock or indexed map.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersSpec
open SemiprimeRationalBits
/-- Exact sign-prefixed numerator ABI, preserving all magnitude padding. -/
def signed (x:RationalWord):List Bool:=x.numerator.negative::x.numerator.magnitude
/-- One row has its TRUE tag and two framed actual fields; its tail is initially EMPTY. -/
def row (x:RationalWord):List Bool:=true::SemiprimeSourceHistogramKeyBits.frame (signed x)
  (SemiprimeSourceHistogramKeyBits.frame x.denominator [])
/-- Complete chronological rational vector uses the existing FALSE terminal. -/
def vector:List RationalWord→List Bool
  | []=>[false]
  | x::xs=>row x++vector xs
/-- Exact next power: old accumulator FIRST, original argument SECOND. -/
def next (width:List Bool) (argument current:RationalWord):RationalWord:=
  (executeOperation .mul current argument width).word
/-- One literal sequential recurrence emits the current word before its successors. -/
def suffix (width:List Bool) (argument current:RationalWord):Nat→List RationalWord
  | 0=>[]
  | n+1=>current::suffix width argument (next width argument current) n
/-- Actual complete power array, with literal ONE at index zero independently of W. -/
def array (width:List Bool) (argument:RationalWord) (q:Nat):List RationalWord:=
  suffix width argument SemiprimeJetBits.oneWord q
/-- Zero and singleton arrays retain the precise native literal seed convention, even W0. -/
theorem array_zero (width:List Bool) (argument:RationalWord):array width argument 0=[]:=rfl
/-- No arithmetic call is needed for the literal index-zero power. -/
theorem array_one (width:List Bool) (argument:RationalWord):array width argument 1=[SemiprimeJetBits.oneWord]:=rfl
/-- The physical recurrence has precisely the authoritative native operand orientation. -/
theorem next_power (width:List Bool) (argument:RationalWord) (n:Nat):
    next width argument (SemiprimeD1RecoveryPowerBits.power width argument n).word=
      (SemiprimeD1RecoveryPowerBits.power width argument (n+1)).word:=rfl
/-- Byte equality of EVERY sequential suffix and its original ordered finite-index powers. -/
theorem from_power (width:List Bool) (argument:RationalWord) (n q:Nat):
    suffix width argument (SemiprimeD1RecoveryPowerBits.power width argument n).word q=
      (List.range' n q).map (fun k=>(SemiprimeD1RecoveryPowerBits.power width argument k).word):=by
  induction q generalizing n with
  | zero=>rfl
  | succ q ih=>simp only [suffix,next_power,List.range'_succ,List.map_cons,ih]
/-- The old cache is exactly its actual index-ordered power bytes; its old clock is irrelevant. -/
theorem native_words (width:List Bool) (argument:RationalWord) (keys:List Nat):
    (SemiprimeD1RecoveryScalarWeightBits.powers width argument keys).words=
      keys.map (fun k=>(SemiprimeD1RecoveryPowerBits.power width argument k).word):=by
  induction keys with
  | nil=>rfl
  | cons k ks ih=>simp only [SemiprimeD1RecoveryScalarWeightBits.powers,List.map_cons,ih]
/-- Complete exact byte identity to the native cache on indices0..q-1, without Valid/Fits premises. -/
theorem array_native (width:List Bool) (argument:RationalWord) (q:Nat):
    array width argument q=(SemiprimeD1RecoveryScalarWeightBits.powers width argument
      (SemiprimeD1RecoveryScalarRun.indices q).value).words:=by
  rw [native_words,SemiprimeD1RecoveryScalarRun.indices_value]
  simpa [array,SemiprimeD1RecoveryPowerBits.power,List.range_eq_range'] using from_power width argument 0 q
/-- Exact row count follows the actual acquired q markers, not a supplied address list. -/
theorem from_length (width:List Bool) (argument current:RationalWord) (q:Nat):
    (suffix width argument current q).length=q:=by
  induction q generalizing current with
  | zero=>rfl
  | succ q ih=>simp only [suffix,List.length_cons,ih]
/-- The exact next operation fits BOTH actual magnitude fields, including zero-width truncation. -/
theorem next_lengths (width:List Bool) (argument current:RationalWord):
    (next width argument current).numerator.magnitude.length=width.length ∧
    (next width argument current).denominator.length=width.length:=
  fitRationalBits_width _ _
/-- Framing cost pays actual signed numerator and denominator bytes. -/
theorem row_length (x:RationalWord):
    (row x).length=2*x.numerator.magnitude.length+2*x.denominator.length+5:=by
  simp only [row,signed,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  omega
/-- Logging one reversed row and reversing only once at the end retains exact chronological order. -/
theorem history_cons (x:RationalWord) (hist:List Bool):
    (row x).reverse++hist=(hist.reverse++row x).reverse:=by simp
end RiemannGaussian.SemiprimeD1StackRecoveryPowersSpec

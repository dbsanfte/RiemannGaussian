/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryDenominator
import RiemannGaussian.SemiprimeSourceHistogramKeyBits
/-! # Exact physical five-field row tape and raw streaming product specification
Functions here describe literal input bytes and outputs in proofs. The finite
source never receives a row object, field getter, product, length or count.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecoveryDenominatorEncoding
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeBitArithmetic
/-- Proof-only five actual source payloads: node,index,sign,magnitude,denominator. -/
abbrev Row:=Fin 5 → List Bool
/-- Exact five physical framed fields, with their actual unread suffix. -/
def fields (r:Row) (tail:List Bool):List Bool:=frame (r 0) (frame (r 1) (frame (r 2) (frame (r 3) (frame (r 4) tail))))
/-- Literal acquired row-tape format, including every row marker and final false sentinel. -/
def tape:List Row → List Bool
  | []=>[false]
  | r::rs=>true::fields r (tape rs)
/-- Mathematical raw accumulator reached by the actual left-to-right stream. -/
def raw (rs:List Row) (acc:List Bool):List Bool:=
  rs.foldl (fun acc r=>(mulBits (r 4) acc).bits) acc
/-- Actual total denominator payload bytes, a proof-side resource projection only. -/
def denominatorMass (rs:List Row):Nat:=(rs.map (fun r=>(r 4).length)).sum
/-- First-denominator orientation gives additive raw padding, not recursive multiplication of lengths. -/
theorem raw_length (rs:List Row) (acc:List Bool):
    (raw rs acc).length ≤acc.length+2*denominatorMass rs:=by
  induction rs generalizing acc with
  | nil=>simp [raw,denominatorMass]
  | cons r rs ih=>
    have h:=ih (mulBits (r 4) acc).bits
    have hm:=mulBits_length (r 4) acc
    simp only [raw,List.foldl_cons] at ⊢ h
    simp only [denominatorMass,List.map_cons,List.sum_cons] at ⊢ h
    omega
/-- Numeric interpretation is proof-only and agrees with the complete denominator product. -/
theorem raw_value (rs:List Row) (acc:List Bool):
    bitValue (raw rs acc)=(rs.map (fun r=>bitValue (r 4))).prod*bitValue acc:=by
  induction rs generalizing acc with
  | nil=>simp [raw]
  | cons r rs ih=>
    simp only [raw,List.foldl_cons] at ⊢ ih
    rw [ih,mulBits_correct]
    simp only [List.map_cons,List.prod_cons]
    ac_rfl
end RiemannGaussian.SemiprimeD1StackRecoveryDenominatorEncoding

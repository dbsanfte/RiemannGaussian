/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorEncoding
/-! # Intrinsic row-count and raw-product caps from actual acquired tape bytes
No count, field size or product length is a program operand. Every estimate is
proved from the actual framed five-field tape and denominator-first execution.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecoveryDenominatorCapacities
open SemiprimeD1StackRecoveryDenominatorEncoding
/-- Actual five physical payload lengths of one acquired row. -/
def fieldMass (r:Row):Nat:=(r 0).length+(r 1).length+(r 2).length+(r 3).length+(r 4).length
/-- Actual complete payload bytes in the acquired row stream. -/
def payloadMass (rs:List Row):Nat:=(rs.map fieldMass).sum
/-- The true denominator bytes are part of the actual complete row payload. -/
theorem denominator_le (r:Row):(r 4).length ≤fieldMass r:=by unfold fieldMass;omega
/-- All five real field delimiters and their copied payload bytes are included. -/
theorem fields_length (r:Row) (tail:List Bool):(fields r tail).length=2*fieldMass r+tail.length+5:=by
  simp only [fields,SemiprimeSourceHistogramKeyBits.frame_length]
  unfold fieldMass
  omega
/-- Exact whole tape length, counting every row marker and final false sentinel. -/
theorem tape_length (rs:List Row):(tape rs).length=2*payloadMass rs+6*rs.length+1:=by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>
    simp only [tape,List.length_cons,fields_length,ih,payloadMass,List.map_cons,List.sum_cons]
    omega
/-- Every row count is paid by actual source bytes. -/
theorem rows_length (rs:List Row):rs.length ≤(tape rs).length:=by have h:=tape_length rs;omega
/-- Every actual payload byte is paid by the acquired source tape. -/
theorem payload_le_tape (rs:List Row):payloadMass rs ≤(tape rs).length:=by have h:=tape_length rs;omega
/-- All true denominator input bytes are included without reading any child cache. -/
theorem denominator_mass_le (rs:List Row):denominatorMass rs ≤payloadMass rs:=by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>
    have h:=denominator_le r
    simp only [denominatorMass,payloadMass,List.map_cons,List.sum_cons] at ⊢ ih
    omega
/-- Each physically selected row's complete fields are paid by the whole source stream. -/
theorem field_mass_le (rs:List Row) (r:Row) (hr:r∈rs):fieldMass r ≤payloadMass rs:=by
  induction rs with
  | nil=>cases hr
  | cons s rs ih=>
    simp only [List.mem_cons] at hr
    simp only [payloadMass,List.map_cons,List.sum_cons]
    rcases hr with rfl|hr
    · omega
    · have h:=ih hr
      unfold payloadMass at h
      omega
/-- Complete denominator bytes are bounded by actual acquired row-tape bytes. -/
theorem denominator_mass_tape (rs:List Row):denominatorMass rs ≤(tape rs).length:=
  (denominator_mass_le rs).trans (payload_le_tape rs)
/-- The entire physically reached raw accumulator has a linear actual-source byte cap. -/
theorem raw_source_length (rs:List Row):(raw rs [true]).length ≤1+2*(tape rs).length:=by
  have h:=raw_length rs [true]
  have hd:=denominator_mass_tape rs
  simp only [List.length_cons,List.length_nil] at h
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryDenominatorCapacities

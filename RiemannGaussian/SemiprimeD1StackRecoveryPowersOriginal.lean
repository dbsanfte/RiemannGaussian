/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersStorage
import RiemannGaussian.SemiprimeD1StackRecoveryPowersValues
/-! # Complete exact native cached-power source and actual Grid-lineage value boundary
The runtime takes ONLY four actual tapes. Original q/argument/template
acquisition remains a caller composition, whose byte/value lineage is explicit.
No per-power Fits, array, result, native report clock or operation stream is input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersOriginal
open SemiprimeD1StackRecoveryPowers SemiprimeD1StackRecoveryPowersEncoding SemiprimeD1StackRecoveryPowersBounds
open SemiprimeD1StackRecoveryPowersSpec (signed array vector)
open SemiprimeRationalBits (RationalWord)
/-- Mathematical framing-tail identity identifies the exact existing rational-vector ABI. -/
theorem frame_tail (xs ys zs:List Bool):
    SemiprimeSourceHistogramKeyBits.frame xs ys++zs=SemiprimeSourceHistogramKeyBits.frame xs (ys++zs):=by
  induction xs with
  | nil=>rfl
  | cons b xs ih=>simp only [SemiprimeSourceHistogramKeyBits.frame,List.cons_append,ih]
/-- Complete output codec is byte-identical to the sealed Grid/affine rational-array codec. -/
theorem vector_grid (xs:List RationalWord):vector xs=SemiprimeD1StackRecoveryGridView.slopeTape xs:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [SemiprimeD1StackRecoveryPowersSpec.vector,SemiprimeD1StackRecoveryPowersSpec.row,List.cons_append,
      frame_tail,List.nil_append,ih,SemiprimeD1StackRecoveryGridView.slopeTape,List.foldr_cons,
      SemiprimeD1StackRecoveryGridView.slopeRow]
    rfl
/-- Exact whole output byte equality holds even q0, W0, zero denominators, padding and negative zero. -/
theorem output_native (argument:RationalWord) (q:Nat) (width:List Bool):
    (done argument q width).data (aux .output)=vector (SemiprimeD1RecoveryScalarWeightBits.powers width argument
      (SemiprimeD1RecoveryScalarRun.indices q).value).words:=by
  change vector (array width argument q)=_
  rw [SemiprimeD1StackRecoveryPowersSpec.array_native]
/-- Four actual originals are retained exactly, including raw padding and unary q bytes. -/
theorem retained_inputs (argument:RationalWord) (q:Nat) (width:List Bool):
    (done argument q width).data (aux .argumentSigned)=signed argument ∧
    (done argument q width).data (aux .argumentDen)=argument.denominator ∧
    (done argument q width).data (aux .q)=List.replicate q true ∧
    (done argument q width).data template=width:=⟨rfl,rfl,rfl,rfl⟩
/-- Every actual caller work tape is empty, including current, remaining, per-row and whole-history buffers. -/
theorem work_clear (argument:RationalWord) (q:Nat) (width:List Bool) (slot:Aux)
    (ha:slot≠.argumentSigned) (hd:slot≠.argumentDen) (hq:slot≠.q) (ho:slot≠.output):
    (done argument q width).data (aux slot)=[]:=by
  cases slot <;> first | rfl | exact (ha rfl).elim | exact (hd rfl).elim | exact (hq rfl).elim | exact (ho rfl).elim
/-- All36 actual arithmetic fields, including every alias/shadow, are empty except the retained W. -/
theorem rational_clear (argument:RationalWord) (q:Nat) (width:List Bool) (slot:R.Stack)
    (hk:slot≠SemiprimeD1StackRationalOperation.aux .template):
    (done argument q width).data (rational slot)=[]:=by
  change (if slot=SemiprimeD1StackRationalOperation.aux .template then width else [])=[]
  exact ite_eq_right hk
/-- Complete actual fixed source, exact original array bytes and own polynomial clock. -/
theorem source_original (argument:RationalWord) (q:Nat) (width:List Bool):
    ∃time ≤ polynomial argument q width,
      SemiprimeD1StackCalls.run program time (initial (signed argument) argument.denominator (List.replicate q true) width)=some (done argument q width) ∧
      (done argument q width).data (aux .output)=vector (SemiprimeD1RecoveryScalarWeightBits.powers width argument
        (SemiprimeD1RecoveryScalarRun.indices q).value).words:=by
  obtain ⟨time,ht,hr⟩:=source_run_bounded argument q width
  exact ⟨time,ht,hr,output_native argument q width⟩
/-- Original actual Grid argument and internally derived Node-width capacities close ALL power legality/value obligations. -/
theorem source_grid_values (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (hu:u ≤ M)
    (hW:SemiprimeD1RecoveryNodeBits.width a M ≤ width.length):
    let argument:=SemiprimeD1StackRecoveryPowersValues.argument a M u t width
    let q:=SemiprimeD1StackRecoveryPowersValues.retained a M u selected
    ∃time ≤ polynomial argument q width,
      SemiprimeD1StackCalls.run program time (initial (signed argument) argument.denominator (List.replicate q true) width)=some (done argument q width) ∧
      ((array width argument q).map RationalWord.value=
        (SemiprimeD1RecoveryWeightRun.powersRun (SemiprimeD1WeightPrecision.argument a selected.val) q).value.toList ∧
        (∀x∈array width argument q,x.Valid) ∧ (∀x∈array width argument q,SemiprimeRationalBits.Width x width.length)):=by
  obtain ⟨time,hbound,hr⟩:=source_run_bounded (SemiprimeD1StackRecoveryPowersValues.argument a M u t width)
    (SemiprimeD1StackRecoveryPowersValues.retained a M u selected) width
  exact ⟨time,hbound,hr,SemiprimeD1StackRecoveryPowersValues.original_values a M u selected t width ht hu hW⟩
end RiemannGaussian.SemiprimeD1StackRecoveryPowersOriginal

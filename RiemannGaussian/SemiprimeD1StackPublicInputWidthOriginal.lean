/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputWidthBounds
import RiemannGaussian.SemiprimeD1StackWordLessExecution
import RiemannGaussian.SemiprimeMacroEntryBitCheck

/-! # Exact original active-digit width and actual low-bit activity test
The bound and its activity bit are derived from the paid original-input source.
They are not guessed from compact target-digit values: internal high-zero
digits and the final partial digit keep their ORIGINAL allowed bit widths.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackPublicInputWidthOriginal
open SemiprimeD1StackPublicInputWidth SemiprimeD1StackPublicInputWidthExecution
open SemiprimeMacroParameters SemiprimeBitArithmetic

/-- Original binary-source width, for ALL physical indices, including inactive ones. -/
theorem width_original (bits index : List Bool) :
    SemiprimeD1StackInputWidthExecution.width (cache bits index)=activeDigitBits bits.length index.length := by
  obtain ⟨hw,hb,hi⟩:=SemiprimeD1StackPublicInputWidthBounds.cache_lengths bits index
  unfold SemiprimeD1StackInputWidthExecution.width
  rw [hw,hb,hi]
  rfl
/-- Canonical original binary N identifies its actual source bit-count. -/
theorem width_public (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    SemiprimeD1StackInputWidthExecution.width (cache bits index)=activeDigitBits (bitLength (bitValue bits)) index.length := by
  rw [width_original,SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc]
/-- The old power-template routine has exactly the actual low-zero/high-one bytes. -/
theorem boundBits_bits (n : ℕ) :
    SemiprimeMacroEntryBitCheck.boundBits n=List.replicate n false++[true] := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    unfold SemiprimeMacroEntryBitCheck.boundBits
    simp only [List.replicate_succ,SemiprimeBitFermatArithmetic.powerTemplateBits,List.cons_append]
    exact congrArg (List.cons false) ih
/-- Exact OLD source-comparison bound word, acquired from N and physical index
only, for every original active/inactive position and every compact N. -/
theorem output_original (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    (done bits index).data output=
      SemiprimeMacroEntryBitCheck.boundBits (activeDigitBits (bitLength (bitValue bits)) index.length) := by
  rw [output_bound]
  unfold SemiprimeD1StackInputWidthExecution.bound
  rw [width_public bits index hc]
  exact (boundBits_bits _).symm
/-- Positive actual acquired width characterizes the ORIGINAL active digit set;
the machine never receives its cardinality or this solved predicate. -/
theorem active_iff (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    0<SemiprimeD1StackInputWidthExecution.width (cache bits index) ↔ index.length<digitCount (bitLength (bitValue bits)) := by
  rw [width_public bits index hc]
  have hL:=bitLength_pos hN
  constructor
  · intro ha
    by_contra hn
    have hi : digitCount (bitLength (bitValue bits))≤ index.length := by omega
    have hm:=Nat.mul_le_mul_right (radixBits (bitLength (bitValue bits))) hi
    have he:bitLength (bitValue bits)≤ index.length*radixBits (bitLength (bitValue bits)) :=
      (digitCount_covers hL).trans hm
    unfold activeDigitBits at ha
    rw [Nat.sub_eq_zero_of_le he,Nat.min_zero] at ha
    exact (Nat.lt_irrefl 0) ha
  · intro hi
    exact (activeDigitBits_bounds hL hi).1
/-- A SINGLE ACTUAL low-bit peek on the produced bound detects exactly original
digit activity, including zero-valued interior digits and exhausted positions. -/
theorem head_active (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ((done bits index).data output).head?=some false ↔ index.length<digitCount (bitLength (bitValue bits)) := by
  rw [output_bound,SemiprimeD1StackInputWidthBounds.bound_head]
  have hi:=active_iff bits index hc hN
  cases hw:SemiprimeD1StackInputWidthExecution.width (cache bits index) with
  | zero=>
    have hn : ¬index.length<digitCount (bitLength (bitValue bits)) := by
      intro ht
      have hp:=hi.mpr ht
      rw [hw] at hp
      exact (Nat.lt_irrefl 0) hp
    simp [hn]
  | succ n=>
    have ha : index.length<digitCount (bitLength (bitValue bits)) := hi.mp (by rw [hw];omega)
    simp [ha]
/-- Any subsequent real comparison against the acquired word has the exact
original source guard. This semantic adapter supplies NO guard bit to runtime. -/
theorem original_guard (bits index word : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (i : Fin (digitCount (bitLength (bitValue bits)))) (hi : index.length=i.val) :
    SemiprimeD1StackWordLessExecution.answer word ((done bits index).data output)=
      (SemiprimeMacroEntryBitPrimitives.lessBits word
        (SemiprimeMacroEntryBitCheck.boundBits ((SemiprimePublicFactorCount.publicConfig (bitValue bits) hN).width i))).accepted := by
  apply Bool.eq_iff_iff.mpr
  rw [SemiprimeD1StackWordLessExecution.answer_true,SemiprimeMacroEntryBitPrimitives.lessBits_correct,output_original bits index hc,hi]
  rfl
/-- Actual original-index input inventory, uniformly before every input position. -/
theorem original_inventory (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (hi : index.length=i.val) :
    bits.length+index.length+2≤70*(bitLength (bitValue bits)+1) := by
  have h:=(SemiprimeD1StackTransformArithmetic.prefix_powers (bitLength (bitValue bits)) _ le_rfl).1
  change transformLength (bitLength (bitValue bits))≤64*bitLength (bitValue bits)+1 at h
  have hit:=i.isLt
  have hshape:=axes_product (bitLength (bitValue bits))
  rw [SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc,hi]
  omega
/-- Whole original-binary bound-acquisition clock in original bitlength. -/
theorem original_time (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (hi : index.length=i.val) :
    SemiprimeD1StackPublicInputWidthBounds.runBound bits index≤100000000000000*(bitLength (bitValue bits)+1)^2 := by
  have h:=Nat.pow_le_pow_left (original_inventory bits index hc i hi) 2
  rw [mul_pow] at h
  norm_num at h
  unfold SemiprimeD1StackPublicInputWidthBounds.runBound
  omega
/-- SAME actual machine, original binary N+physical index only, fixed quadratic
time before all N/positions; no cache, width, target, bound or clock advice. -/
noncomputable def machineOriginal (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (hi : index.length=i.val) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits index))
      (some (SemiprimeD1StackCalls.configuration (done bits index)))
      (100000000000000*(bitLength (bitValue bits)+1)^2) := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0) hN
  let h:=SemiprimeD1StackPublicInputWidthBounds.boundInTime bits index hb
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (original_time bits index hc i hi)⟩
/-- ALL37 data roles and actual return-label cells at EVERY actual prefix,
uniformly in original binary bitlength and every original input position. -/
theorem original_prefix_cells (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (hi : index.length=i.val) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits index)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤10000000000000000*(bitLength (bitValue bits)+1)^2 := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0) hN
  have h:=SemiprimeD1StackPublicInputWidthBounds.machine_prefix_cells bits index hb fuel cfg hr
  have hp:=Nat.pow_le_pow_left (original_inventory bits index hc i hi) 2
  rw [mul_pow] at hp
  norm_num at hp
  omega
end RiemannGaussian.SemiprimeD1StackPublicInputWidthOriginal

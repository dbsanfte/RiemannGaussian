/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1KernelDerivativeBits
import RiemannGaussian.SemiprimeD1RadixOperandBits
import RiemannGaussian.SemiprimeD1RecoveryStripBits
import RiemannGaussian.SemiprimeD1WireKernelOriginal
import RiemannGaussian.SemiprimeSourceCompactWordIds
import RiemannGaussian.SemiprimeBitIndexGeometry

/-! # Original kernel normalizer acquired by physical grid arithmetic
Original a is the only parameter. Grid IDs and the central power of two are
constructed as actual words; physical subtraction and multiplication form the
derivative. Its low-bit strip yields the signed odd denominator. No native
factorial, valuation, integer derivative or large quotient produces the output.
The original finite dimension/control calculation remains a host-lowering item.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1KernelDenominatorBits
open scoped BigOperators
open SemiprimeBitArithmetic SemiprimeBitIndexClipping SemiprimeBitIndexGeometry
open SemiprimeBitFermatArithmetic SemiprimeD1WireKernelOriginal

/-- Physical central grid word and paid allocation of its offset template. -/
def centerRun (a : ℕ) : SemiprimeD1RadixOperandBits.Run :=
  let radix := List.replicate a false
  let shifted := shiftTemplateBits radix [true]
  ⟨shifted.bits,bitCost shifted+3*a+2⟩

/-- Original central index is constructed from literal bits. -/
theorem center_value (a : ℕ) : bitValue (centerRun a).bits=center a := by
  have h := (shiftTemplateBits_exact (List.replicate a false) [true]).1
  have hone : bitValue [true]=1 := rfl
  simpa only [centerRun,List.length_replicate,hone,Nat.mul_one,center] using h

/-- The original central word has exactly its genuine binary width. -/
theorem center_width (a : ℕ) : (centerRun a).bits.length=a+1 := by
  simpa only [centerRun,List.length_replicate,List.length_cons,List.length_nil] using
    (shiftTemplateBits_exact (List.replicate a false) [true]).2.1

/-- Complete physical central-word creation, including the radix template. -/
theorem center_clock (a : ℕ) : (centerRun a).clock=6*a+3 := by
  have h := (shiftTemplateBits_exact (List.replicate a false) [true]).2.2
  simp only [List.length_replicate] at h
  dsimp only [centerRun]
  rw [h]
  omega

/-- Actual signed raw derivative, still entirely in physical word form. -/
def raw (a : ℕ) : SemiprimeD1KernelProductBits.Run :=
  SemiprimeD1KernelDerivativeBits.run (centerRun a).bits
    (SemiprimeSourceCompactWordIds.acquire (size a)).value

/-- Original acquired grid-word widths are derived, not supplied to the producer. -/
theorem grid_width (a : ℕ) : ∀ q∈(SemiprimeSourceCompactWordIds.acquire (size a)).value,
    q.length ≤ a+1 := by
  intro q hq
  apply SemiprimeSourceCompactBits.compact_length_of_lt q
    (SemiprimeSourceCompactWordIds.acquire_compact (size a) q hq)
  exact SemiprimeSourceCompactWordIds.acquire_value_lt (size a) q hq

/-- The physically formed integer is the actual original grid derivative. -/
theorem raw_value (a : ℕ) : (raw a).word.value=
    SemiprimeD1WireKernel.derivativeProduct (size a) (center a) := by
  let f : ℕ → ℤ := fun q => if center a=q then 1 else (center a:ℤ)-(q:ℤ)
  calc
    _ = (((SemiprimeSourceCompactWordIds.acquire (size a)).value.map bitValue).map f).prod := by
      rw [raw,SemiprimeD1KernelDerivativeBits.run_value,center_value]
      rw [List.map_map]
      rfl
    _ = ((List.range (size a)).map f).prod := by rw [SemiprimeSourceCompactWordIds.acquire_values]
    _ = ∏q∈Finset.range (size a),f q := by
      simpa only [List.toFinset_range] using
        (List.prod_toFinset f (List.nodup_range (n:=size a))).symm
    _ = _ := by unfold f SemiprimeD1WireKernel.derivativeProduct;simp only [eq_comm]

/-- Full physical derivative magnitude width is polynomial in original a and2L. -/
theorem raw_width (a : ℕ) : (raw a).word.magnitude.length ≤ 2*size a*(a+2)+1 := by
  have h := SemiprimeD1KernelDerivativeBits.run_width (centerRun a).bits
    (SemiprimeSourceCompactWordIds.acquire (size a)).value (a+1)
    (center_width a).le (grid_width a)
  simpa only [raw,SemiprimeSourceCompactWordIds.acquire_length,Nat.add_assoc] using h

/-- Complete physical derivative work, with no big-integer value or Fit advice. -/
theorem raw_clock (a : ℕ) : (raw a).clock ≤ size a*(56*(a+2)+15)+1+
    SemiprimeD1KernelProductBits.budget (size a) (a+2)+3 := by
  have h := SemiprimeD1KernelDerivativeBits.run_clock (centerRun a).bits
    (SemiprimeSourceCompactWordIds.acquire (size a)).value (a+1)
    (center_width a).le (grid_width a)
  simpa only [raw,SemiprimeSourceCompactWordIds.acquire_length,Nat.add_assoc] using h

/-- Original signed odd denominator and its actual dyadic content word. -/
structure Run where
  /-- Actual signed odd suffix of the computed derivative. -/
  word : SignedWord
  /-- Actual shifted-one word, never a native valuation answer. -/
  content : List Bool
  /-- Original grid construction, center, derivative, strip and all tags. -/
  clock : ℕ

/-- Closed original-grid physical normalizer acquisition. -/
def run (a : ℕ) : Run :=
  let grid := SemiprimeSourceCompactWordIds.acquire (size a)
  let center := centerRun a
  let derivative := SemiprimeD1KernelDerivativeBits.run center.bits grid.value
  let stripped := SemiprimeD1RecoveryStripBits.acquire derivative.word.magnitude
  ⟨⟨derivative.word.negative,stripped.odd⟩,stripped.content,
    grid.work+center.clock+derivative.clock+stripped.clock+10⟩

/-- Original nonzero derivative gives a positive actual magnitude to strip. -/
theorem raw_positive (a : ℕ) : 0 < bitValue (raw a).word.magnitude := by
  rw [←signedWord_natAbs,raw_value]
  exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr
    (SemiprimeD1WireKernelFactors.derivativeProduct_ne_zero (size a) (center a) (center_lt a)))

/-- Actual low-bit stripping extracts exactly the original common content. -/
theorem run_content (a : ℕ) : bitValue (run a).content=
    2^SemiprimeD1WireKernelEntry.content (a+1) := by
  have h := SemiprimeD1RecoveryStripBits.content_value (raw a).word.magnitude (raw_positive a)
  have he := SemiprimeD1WireKernel.derivativeProduct_content (a+1) (center a) (center_lt a)
  change bitValue (SemiprimeD1RecoveryStripBits.acquire (raw a).word.magnitude).content=_
  rw [h]
  unfold SemiprimeD1IntegerRecoveryResidue.content
  rw [←signedWord_natAbs,raw_value]
  change 2^padicValInt 2 (SemiprimeD1WireKernel.derivativeProduct (2^(a+1)) (center a))=_
  rw [he]
  rfl

/-- Physical signed stripping reconstructs the full actual derivative. -/
theorem run_reconstruct (a : ℕ) : (bitValue (run a).content:ℤ)*(run a).word.value=(raw a).word.value := by
  have h := SemiprimeD1RecoveryStripBits.factor (raw a).word.magnitude
  have hInt : (bitValue (raw a).word.magnitude:ℤ)=
      (bitValue (SemiprimeD1RecoveryStripBits.acquire (raw a).word.magnitude).content:ℤ)*
        (bitValue (SemiprimeD1RecoveryStripBits.acquire (raw a).word.magnitude).odd:ℤ) := by
    exact_mod_cast h
  change (bitValue (SemiprimeD1RecoveryStripBits.acquire (raw a).word.magnitude).content:ℤ)*
    (if (raw a).word.negative=true then
      -(bitValue (SemiprimeD1RecoveryStripBits.acquire (raw a).word.magnitude).odd:ℤ)
    else bitValue (SemiprimeD1RecoveryStripBits.acquire (raw a).word.magnitude).odd)=_
  cases hs : (raw a).word.negative <;>
    simp only [SignedWord.value,hs,Bool.false_eq_true,ite_false,ite_true] <;>
    nlinarith only [hInt]

/-- CLOSED original signed normalizer bytes equal the exact original factory,
with no native factorial, valuation, Int quotient or denominator answer input. -/
theorem run_value (a : ℕ) : (run a).word.value=
    SemiprimeD1WireKernelEntry.oddDenominator (a+1) (center a) := by
  have hraw := run_reconstruct a
  rw [run_content,raw_value] at hraw
  have hrec := SemiprimeD1WireKernelEntry.denominator_reconstruct (a+1) (center a) (center_lt a)
  have hp : (2:ℤ)^SemiprimeD1WireKernelEntry.content (a+1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hp
  push_cast at hraw
  have hrec' : SemiprimeD1WireKernel.derivativeProduct (size a) (center a)=
      SemiprimeD1WireKernelEntry.oddDenominator (a+1) (center a)*
        (2:ℤ)^SemiprimeD1WireKernelEntry.content (a+1) := hrec.symm
  exact hraw.trans (hrec'.trans (mul_comm _ _))

/-- Original output oddness follows from the actual producer and original grid. -/
theorem run_odd (a : ℕ) : Odd (run a).word.value := by
  rw [run_value]
  exact SemiprimeD1WireKernelEntry.denominator_odd (a+1) (center a) (center_lt a)

/-- Actual output payload has the derived full original-grid width. -/
theorem run_width (a : ℕ) : (run a).word.magnitude.length ≤ 2*size a*(a+2)+1 := by
  exact (SemiprimeD1RecoveryStripBits.lengths (raw a).word.magnitude).2.trans (raw_width a)

/-- Fixed original-dimension polynomial; original2L is a scalar parameter here,
and no actual denominator magnitude is substituted into a loop bound. -/
def budget (a N : ℕ) : ℕ :=
  N*(30*(a+4)+20)+1+(6*a+3)+
    (N*(56*(a+2)+15)+1+SemiprimeD1KernelProductBits.budget N (a+2)+3)+
    8*(2*N*(a+2)+1)+10+10

/-- All actual physical normalizer work is bounded from original grid dimensions,
including grid ID construction, every exact integer product and low-bit strip. -/
theorem run_clock (a : ℕ) : (run a).clock ≤ budget a (size a) := by
  have hid := SemiprimeSourceCompactWordIds.acquire_clock (size a)
  have hn : 1 ≤ size a := by unfold size;exact Nat.one_le_two_pow
  have hlog : Nat.clog 2 (size a+1) ≤ a+2 := by
    apply Nat.clog_le_of_le_pow
    have he : 2^(a+2)=2*size a := by unfold size;rw [show a+2=(a+1)+1 by omega,pow_succ];ring
    rw [he]
    omega
  have hs : (SemiprimeSourceCompactWordIds.acquire (size a)).work ≤
      size a*(30*(a+4)+20)+1 := by
    have hstep : SemiprimeSourceCompactWordIds.stepBudget (size a) ≤ 30*(a+4)+20 := by
      unfold SemiprimeSourceCompactWordIds.stepBudget
      omega
    exact hid.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hstep) 1)
  have hc := center_clock a
  have hr := raw_clock a
  have hw := raw_width a
  have hstrip := SemiprimeD1RecoveryStripBits.acquire_clock (raw a).word.magnitude
  change (SemiprimeSourceCompactWordIds.acquire (size a)).work+(centerRun a).clock+
    (raw a).clock+(SemiprimeD1RecoveryStripBits.acquire (raw a).word.magnitude).clock+10 ≤ _
  unfold budget
  omega

end RiemannGaussian.SemiprimeD1KernelDenominatorBits

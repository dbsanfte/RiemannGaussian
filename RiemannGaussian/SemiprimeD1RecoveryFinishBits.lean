/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryCanonicalRun
import RiemannGaussian.SemiprimeD1OddInverseBounds
import RiemannGaussian.SemiprimeEncodedRowSelection

/-! # Canonical integer recovery to an actual physical odd-inverse output
The common denominator is stripped by bounded native integer stages. Its actual
odd part and the actual signed numerator are digit-extracted, then the modular
inverse and final multiplication execute on Boolean words. Native extraction
and big-integer division remain explicitly separate from the physical clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryFinishBits
open SemiprimeD1RecoveryScalarRun SemiprimeBitArithmetic
open SemiprimeD1IntegerRecoveryResidue
open SemiprimeD1JetScalarBits

/-- Actual native dyadic cancellation and its retained scalar-stage report. -/
structure Stripped where
  /-- Actual divided signed numerator. -/
  numerator : ℤ
  /-- Actual remaining positive odd denominator. -/
  denominator : ℕ
  /-- Bounded valuation/power/division scalar stages, not primitive bit work. -/
  work : ℕ

/-- Bounded actual valuation and content acquisition; fuel is a bit exponent,
never the possibly enormous numerical denominator itself. -/
def strip (W : ℕ) (N : ℤ) (D : ℕ) : Stripped :=
  let order:=orderFuel W D
  let power:=intPower 2 order.value
  ⟨N/power.value,D/power.value.natAbs,order.work+power.work+5⟩

/-- Original numerical denominator bounds derive the bounded valuation fuel. -/
theorem valuation_le (W D : ℕ) (hD : 0 < D) (hd : D ≤ 2^W) : padicValNat 2 D ≤ W := by
  have hp : 2^padicValNat 2 D ≤ D := Nat.le_of_dvd hD pow_padicValNat_dvd
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp (hp.trans hd)

/-- Actual stripping agrees with the already proved maximal-content cancellation. -/
theorem strip_value (W : ℕ) (N : ℤ) (D : ℕ) (hD : 0 < D) (hd : D ≤ 2^W) :
    (strip W N D).numerator=(stripped N D).numerator ∧
      ((strip W N D).denominator:ℤ)=(stripped N D).denominator := by
  have hv:=orderFuel_value W D (Or.inr (valuation_le W D hD hd))
  simp only [strip,hv,intPower_value,stripped,content,Int.natAbs_pow ]
  norm_cast

/-- Actual signed digit acquisition, with separate native and physical reports. -/
structure SignedReport where
  /-- Actual signed residue digits. -/
  bits : List Bool
  /-- Actual successive native digit extraction stages. -/
  scalarWork : ℕ
  /-- Actual Boolean sign/reduction execution report. -/
  clock : ℕ

/-- A real signed digit source followed by physical modular sign handling. -/
def signed (p W : ℕ) (N : ℤ) : SignedReport :=
  let magnitude:=SemiprimeEncodedRowSelection.digits (W+1) N.natAbs
  if N < 0 then
    let negative:=SemiprimeD1OddInverseBits.negativeOne p
    let out:=mul p negative.bits magnitude.bits
    ⟨out.bits,magnitude.work,negative.clock+out.clock+3⟩
  else
    let out:=reduce p magnitude.bits
    ⟨out.bits,magnitude.work,out.clock⟩

/-- Signed physical output has the actual original integer residue. -/
theorem signed_value (p W : ℕ) (N : ℤ) (hN : N.natAbs ≤ 2^W) :
    (bitValue (signed p W N).bits:ZMod (2^p))=(N:ZMod (2^p)) := by
  have hn : N.natAbs < 2^(W+1) := lt_of_le_of_lt hN (Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) (by omega))
  have he:=SemiprimeEncodedRowSelection.digits_value (W+1) N.natAbs hn
  by_cases hs : N < 0
  · simp only [signed,hs,ite_true,mul_zmod,he]
    change SemiprimeD1OddInverseBits.value p (SemiprimeD1OddInverseBits.negativeOne p).bits * (N.natAbs:ZMod (2^p)) = _
    rw [SemiprimeD1OddInverseBits.negativeOne_zmod]
    have h : (N.natAbs:ℤ) = -N := Int.ofNat_natAbs_of_nonpos (by omega)
    have hc:=congrArg (fun z:ℤ => (z:ZMod (2^p))) h
    simp only [Int.cast_natCast,Int.cast_neg] at hc
    rw [hc]
    ring
  · simp only [signed,hs,ite_false,reduce_value,ZMod.natCast_mod,he]
    have hc:=congrArg (fun z:ℤ => (z:ZMod (2^p))) (Int.ofNat_natAbs_of_nonneg (show 0 ≤ N by omega))
    simpa only [Int.cast_natCast] using hc

/-- Final physical residue and separately retained native scalar stages. -/
structure Report where
  /-- Actual compact output residue digits. -/
  bits : List Bool
  /-- Bounded native valuation/content/division and digit extraction stages. -/
  scalarWork : ℕ
  /-- Actual Boolean inverse/sign/product execution report. -/
  clock : ℕ

/-- Acquire actual canonical integer digits, execute physical odd inversion and
multiply the actual signed residue. No native inverse or residue answer is used. -/
def finish (p W : ℕ) (N : ℤ) (D : ℕ) : Report :=
  let s:=strip W N D
  let denominator:=SemiprimeEncodedRowSelection.digits (W+1) s.denominator
  let inverse:=SemiprimeD1OddInverseBits.inverse p denominator.bits
  let numerator:=signed p W s.numerator
  let out:=mul p numerator.bits inverse.bits
  ⟨out.bits,s.work+denominator.work+numerator.scalarWork+5,
    inverse.clock+numerator.clock+out.clock+5⟩

/-- Actual physical odd-inverse execution equals the original native odd-fraction
residue. All numerical bounds are internal-stage integer caps, not Fits answers. -/
theorem finish_value (p W : ℕ) (N : ℤ) (D : ℕ) (hD : 0 < D)
    (hd : D ≤ 2^W) (hn : N.natAbs ≤ 2^W) :
    (bitValue (finish p W N D).bits:ZMod (2^p))=
      SemiprimeD1CrossingResidue.residue p (stripped N D) := by
  have hs:=strip_value W N D hD hd
  have hden : (strip W N D).denominator ≤ 2^W := (Nat.div_le_self _ _).trans hd
  have hnum : (strip W N D).numerator.natAbs ≤ 2^W := (Int.natAbs_ediv_le_natAbs _ _).trans hn
  have hdt : (strip W N D).denominator < 2^(W+1) := lt_of_le_of_lt hden
    (Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) (by omega))
  have he:=SemiprimeEncodedRowSelection.digits_value (W+1) (strip W N D).denominator hdt
  have ho : Odd (bitValue (SemiprimeEncodedRowSelection.digits (W+1) (strip W N D).denominator).bits) := by
    rw [he]
    have hi:=stripped_odd N D hD
    rw [← hs.2] at hi
    exact_mod_cast hi
  have hi:=SemiprimeD1OddInverseBounds.inverse_eq_native p
    (SemiprimeEncodedRowSelection.digits (W+1) (strip W N D).denominator).bits ho
  simp only [finish,mul_zmod,signed_value p W _ hnum]
  change _ * SemiprimeD1OddInverseBits.value p _ = _
  rw [hi]
  simp only [SemiprimeD1OddInverseBits.value,he]
  simp only [SemiprimeD1CrossingResidue.residue,hs.1,← hs.2,Int.cast_natCast]

/-- Signed output width and compactness are derived from actual physical reduction. -/
theorem signed_good (p W : ℕ) (N : ℤ) :
    (signed p W N).bits.length ≤ p ∧ SemiprimeSourceCompactBits.Compact (signed p W N).bits := by
  simp only [signed]
  split_ifs
  · exact ⟨mul_length _ _ _,mul_compact _ _ _⟩
  · exact ⟨reduce_length _ _,reduce_compact _ _⟩

/-- Actual signed digit extraction work is retained in its own field. -/
theorem signed_scalarWork (p W : ℕ) (N : ℤ) : (signed p W N).scalarWork=4*(W+1)+1 := by
  simp only [signed]
  split_ifs <;> exact SemiprimeEncodedRowSelection.digits_work _ _

/-- Explicit physical sign-handling bound, with no word-width advice. -/
theorem signed_clock (p W : ℕ) (N : ℤ) :
    (signed p W N).clock ≤ 12*p*(p+W+3)+10*p+20 := by
  have hm:=mul_clock p (SemiprimeD1OddInverseBits.negativeOne p).bits
    (SemiprimeEncodedRowSelection.digits (W+1) N.natAbs).bits
  have hr:=reduce_clock p (SemiprimeEncodedRowSelection.digits (W+1) N.natAbs).bits
  simp only [SemiprimeD1OddInverseBits.negativeOne,List.length_replicate,
    SemiprimeEncodedRowSelection.digits_length,Nat.add_assoc] at hm ⊢
  norm_num only at hm
  simp only [signed]
  split_ifs <;> dsimp only
  · simp only [SemiprimeD1OddInverseBits.negativeOne]
    omega
  · omega

/-- Actual output is compact and has at most the requested precision. -/
theorem finish_good (p W : ℕ) (N : ℤ) (D : ℕ) :
    (finish p W N D).bits.length ≤ p ∧ SemiprimeSourceCompactBits.Compact (finish p W N D).bits :=
  ⟨mul_length _ _ _,mul_compact _ _ _⟩

/-- Bounded dyadic acquisition never returns more valuation steps than its fuel. -/
theorem order_value_le (W D : ℕ) : (orderFuel W D).value ≤ W := by
  induction W generalizing D with
  | zero => simp [orderFuel]
  | succ W ih =>
    simp only [orderFuel]
    split_ifs <;> dsimp only
    · omega
    · have h:=ih (D/2); omega
    · omega

/-- Native stripping and both digit-extraction traversals have polynomial stage count. -/
theorem finish_scalarWork (p W : ℕ) (N : ℤ) (D : ℕ) :
    (finish p W N D).scalarWork ≤ 20*(W+1)+30 := by
  have ho:=orderFuel_work W D
  have hv:=order_value_le W D
  simp only [finish,strip,intPower_work,SemiprimeEncodedRowSelection.digits_work,signed_scalarWork]
  omega

/-- A fixed polynomial bounds the actual Boolean inverse/sign/product clock. -/
def finishBudget (p W : ℕ) : ℕ :=
  400*(p+1)^3+12*p*(p+W+3)+10*p+20+12*p*(2*p+2)+9*p+14

/-- Every bit operation in the actual odd-inverse completion is retained. -/
theorem finish_clock (p W : ℕ) (N : ℤ) (D : ℕ) :
    (finish p W N D).clock ≤ finishBudget p W := by
  have hi:=SemiprimeD1OddInverseBounds.inverse_clock p
    (SemiprimeEncodedRowSelection.digits (W+1) (strip W N D).denominator).bits
  have hs:=signed_clock p W (strip W N D).numerator
  have hsl:=(signed_good p W (strip W N D).numerator).1
  have hil:=(SemiprimeD1OddInverseBits.inverse_good p
    (SemiprimeEncodedRowSelection.digits (W+1) (strip W N D).denominator).bits).1
  have hm:=mul_clock p (signed p W (strip W N D).numerator).bits
    (SemiprimeD1OddInverseBits.inverse p
      (SemiprimeEncodedRowSelection.digits (W+1) (strip W N D).denominator).bits).bits
  have hmp : 12*(signed p W (strip W N D).numerator).bits.length*
      ((signed p W (strip W N D).numerator).bits.length+
       (SemiprimeD1OddInverseBits.inverse p
        (SemiprimeEncodedRowSelection.digits (W+1) (strip W N D).denominator).bits).bits.length+2)
      ≤ 12*p*(2*p+2) := by gcongr; omega
  simp only [finish,finishBudget]
  omega

/-- Actual original acquisition, integer accumulator and final physical output. -/
structure OriginalReport where
  /-- Actual final compact parent residue. -/
  bits : List Bool
  /-- The full original scalar weight producer report. -/
  producerWork : ℕ
  /-- All native common-denominator integer accumulation stages. -/
  integerWork : ℕ
  /-- Native stripping and digit acquisition stages. -/
  scalarWork : ℕ
  /-- Physical inverse/sign/product bit report. -/
  clock : ℕ

/-- Acquire the original grid size and evaluate the fixed width polynomial;
no mathematical power or supplied width is used as an unreported input stage. -/
def widthRun (a M P : ℕ) : Run ℕ :=
  let g:=SemiprimeD1RecoveryWeightRun.geometry a 0
  ⟨SemiprimeD1IntegerRecoveryHeight.recoveryPolynomial a M g.size P,g.work+100⟩

/-- Actual width acquisition yields the original-derived recovery exponent. -/
theorem widthRun_value (a M P : ℕ) :
    (widthRun a M P).value=SemiprimeD1IntegerRecoveryHeight.recoveryExponent a M P := by
  simp only [widthRun,SemiprimeD1RecoveryWeightRun.geometry_size,
    SemiprimeD1IntegerRecoveryHeight.recoveryExponent_eq]

/-- Complete original-parameter path; the fuel/encoding width is DERIVED from
original recovery height, never supplied as a desired Fits or residue answer. -/
def run (a M u p P : ℕ) (children : ℕ → Array (List Bool)) : OriginalReport :=
  let r:=SemiprimeD1RecoveryCanonicalRun.run a M u children
  let W:=widthRun a M P
  let out:=finish p W.value r.numerator r.denominator
  ⟨out.bits,r.producerWork,r.integerWork,W.work+out.scalarWork+3,out.clock⟩

/-- Original source and child-word dimensions derive BOTH actual integer caps. -/
theorem original_caps (a M u P : ℕ) (hM : u ≤ M)
    (children : ℕ → Array (List Bool))
    (hc : ∀(t j : ℕ), (((children t)[j]?).getD []).length ≤ P) :
    0 < (SemiprimeD1RecoveryCanonicalRun.run a M u children).denominator ∧
    (SemiprimeD1RecoveryCanonicalRun.run a M u children).denominator ≤
      2^SemiprimeD1IntegerRecoveryHeight.recoveryExponent a M P ∧
    (SemiprimeD1RecoveryCanonicalRun.run a M u children).numerator.natAbs ≤
      2^SemiprimeD1IntegerRecoveryHeight.recoveryExponent a M P := by
  rw [SemiprimeD1RecoveryCanonicalRun.run_denominator,SemiprimeD1RecoveryCanonicalRun.run_numerator]
  simp only [SemiprimeD1IntegerRecovery.run,SemiprimeD1IntegerRecovery.denominatorRun_value,
    SemiprimeD1IntegerRecovery.accumulateRun_value]
  refine ⟨SemiprimeD1IntegerRecovery.denominator_pos _,?_,?_⟩
  · have hd:=SemiprimeD1IntegerRecoveryHeight.denominator_bound a M u hM children
    have hl:=SemiprimeD1IntegerRecoveryHeight.terms_length a M u hM children
    apply hd.trans
    apply Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
    unfold SemiprimeD1IntegerRecoveryHeight.recoveryExponent
    nlinarith only [hl]
  · simpa only [List.drop_zero] using
      SemiprimeD1IntegerRecoveryHeight.original_suffix_bits a M u P hM children hc 0

/-- The actual original producer and PHYSICAL inverse recover precisely the
established native maximal-content residue; no count/weight/Fits answer supplied. -/
theorem run_value (a M u p P : ℕ) (hM : u ≤ M)
    (children : ℕ → Array (List Bool))
    (hc : ∀(t j : ℕ), (((children t)[j]?).getD []).length ≤ P) :
    (bitValue (run a M u p P children).bits:ZMod (2^p))=
      SemiprimeD1IntegerRecoveryResidue.finish p (SemiprimeD1IntegerRecovery.run a M u children) := by
  have h:=original_caps a M u P hM children hc
  have hv:=finish_value p (SemiprimeD1IntegerRecoveryHeight.recoveryExponent a M P)
    (SemiprimeD1RecoveryCanonicalRun.run a M u children).numerator
    (SemiprimeD1RecoveryCanonicalRun.run a M u children).denominator h.1 h.2.1 h.2.2
  simpa only [run,widthRun_value,SemiprimeD1RecoveryCanonicalRun.run_numerator,
    SemiprimeD1RecoveryCanonicalRun.run_denominator,SemiprimeD1IntegerRecoveryResidue.finish] using hv

/-- Actual acquired width formation has a retained fixed scalar-stage charge. -/
theorem widthRun_work (a M P : ℕ) : (widthRun a M P).work=3*a+108 := by
  simp [widthRun,SemiprimeD1RecoveryWeightRun.geometry,intPower_work]

/-- Actual complete original output has derived compactness and target width. -/
theorem run_good (a M u p P : ℕ) (children : ℕ → Array (List Bool)) :
    (run a M u p P children).bits.length ≤ p ∧
      SemiprimeSourceCompactBits.Compact (run a M u p P children).bits := finish_good _ _ _ _

/-- Actual complete original physical inverse/sign/product report. -/
theorem run_clock (a M u p P : ℕ) (children : ℕ → Array (List Bool)) :
    (run a M u p P children).clock ≤
      finishBudget p (SemiprimeD1IntegerRecoveryHeight.recoveryExponent a M P) := by
  simpa only [run,widthRun_value] using finish_clock p (widthRun a M P).value
    (SemiprimeD1RecoveryCanonicalRun.run a M u children).numerator
    (SemiprimeD1RecoveryCanonicalRun.run a M u children).denominator

/-- All native stripping/encoding and original width acquisition stages are retained. -/
theorem run_scalarWork (a M u p P : ℕ) (children : ℕ → Array (List Bool)) :
    (run a M u p P children).scalarWork ≤
      3*a+141+20*(SemiprimeD1IntegerRecoveryHeight.recoveryExponent a M P+1) := by
  have h:=finish_scalarWork p (widthRun a M P).value
    (SemiprimeD1RecoveryCanonicalRun.run a M u children).numerator
    (SemiprimeD1RecoveryCanonicalRun.run a M u children).denominator
  simp only [widthRun_value] at h
  simp only [run,widthRun_work,widthRun_value]
  omega

/-- Mixed retained report for this actual original producer and physical finish.
Native scalar operations are explicitly distinguished from physical bit work. -/
def work (r : OriginalReport) : ℕ := r.producerWork+r.integerWork+r.scalarWork+r.clock

/-- Actual original native-producer plus physical-finish report is a fixed
polynomial in original acquired grid dimensions and child/parent precision.
This theorem does not turn scalar division/GCD into unit primitive-bit steps. -/
theorem run_work (a M u p P : ℕ) (hM : u ≤ M)
    (children : ℕ → Array (List Bool))
    (hc : ∀(t j : ℕ), (((children t)[j]?).getD []).length ≤ P) :
    work (run a M u p P children) ≤
      SemiprimeD1RecoveryRowsRun.budget a M u+(4*P+17)*(SemiprimeD1WireKernelOriginal.size a*(4*M))+7+
      (3*a+141+20*(SemiprimeD1IntegerRecoveryHeight.recoveryExponent a M P+1))+
      finishBudget p (SemiprimeD1IntegerRecoveryHeight.recoveryExponent a M P) := by
  have hp:=SemiprimeD1RecoveryCanonicalRun.run_producer_work a M u children
  have hi:=SemiprimeD1RecoveryCanonicalRun.run_integer_work_bound a M u P hM children hc
  have hs:=run_scalarWork a M u p P children
  have hb:=run_clock a M u p P children
  change (run a M u p P children).producerWork ≤ _ at hp
  change (run a M u p P children).integerWork ≤ _ at hi
  unfold work
  omega

end RiemannGaussian.SemiprimeD1RecoveryFinishBits

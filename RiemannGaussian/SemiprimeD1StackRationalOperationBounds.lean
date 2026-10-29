/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperationExecution
import RiemannGaussian.SemiprimeD1StackWordFitBounds
/-! # Own fixed polynomial in the five actual input byte lengths
The template width is paid by its actual cells. Numeric numerator and
denominator values stay binary; every raw-product padding and quotient width
is bounded before real normalization and both physical fits are charged.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalOperationBounds
open SemiprimeD1StackRationalOperation SemiprimeD1StackRationalOperationEncoding
open SemiprimeD1StackRationalOperationCalls SemiprimeD1StackRationalOperationSetup
open SemiprimeD1StackRationalOperationProduct SemiprimeD1StackRationalOperationAdd
open SemiprimeD1StackRationalOperationRaw SemiprimeD1StackRationalOperationFinish
open SemiprimeD1StackRationalOperationExecution
open SemiprimeBitArithmetic (mulBits addBits)
open SemiprimeBitDivision (subBits)
/-- SAME real multiplier trace and copies/drain, bounded from original physical operand lengths. -/
theorem productTime_le (xs ys:List Bool) (s:Nat) (hs:1 ≤ s) (hx:xs.length ≤ s) (hy:ys.length ≤ s) :
    productTime xs ys ≤ 3000*s^3:=by
  have ht:=SemiprimeD1StackMultiplierExecution.source_time xs ys
  have hm:=SemiprimeBitArithmetic.mulBits_length xs ys
  have hmul:xs.length*(ys.length+2) ≤ s*(s+2):=Nat.mul_le_mul hx (by omega)
  have hprod:(xs.length+1)*(xs.length*(ys.length+2)+ys.length+3) ≤ (s+1)*(s*(s+2)+s+3):=
    Nat.mul_le_mul (by omega) (by omega)
  have hs1:s ≤ s^3:=Nat.le_pow (by decide:0<3)
  have hs2:s^2 ≤ s^3:=Nat.pow_le_pow_right hs (by decide:2 ≤ 3)
  unfold productTime SemiprimeD1StackMultiplierExecution.timeBound at *
  nlinarith
/-- Real signed-add copies, both possible subtractors, actual borrow reads and cleanup are linear in actual cross-product bytes. -/
theorem sumTime_le (sx:Bool) (xs:List Bool) (sy:Bool) (ys:List Bool) (s:Nat)
    (hs:1 ≤ s) (hx:xs.length ≤ s) (hy:ys.length ≤ s) :sumTime sx xs sy ys ≤1000*s:=by
  have ha:=(SemiprimeBitArithmetic.addBits_counts xs ys false).2.2.2.2
  have hl:=(SemiprimeBitDivision.subBits_counts xs ys false).2.2.2.2
  have hr:=(SemiprimeBitDivision.subBits_counts ys xs false).2.2.2.2
  have hm:max xs.length ys.length ≤ s:=max_le hx hy
  have hm':max ys.length xs.length ≤ s:=max_le hy hx
  unfold sumTime prepareTime addTime subtractTime saveTime
  split
  · omega
  · split <;> omega
/-- The actual raw result has linear physical width even when input words carry high zero padding. -/
theorem raw_width (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd:List Bool)
    (s:Nat) (hxn:xn.length ≤ s) (hxd:xd.length ≤ s) (hyn:yn.length ≤ s) (hyd:yd.length ≤ s) :
    (rawWord op sx xn xd sy yn yd).numerator.magnitude.length ≤3*s+1 ∧
    (rawWord op sx xn xd sy yn yd).denominator.length ≤3*s+1:=by
  rw [rawWord_legacy]
  exact (SemiprimeRationalBits.rawOperation_cost_width (operation op) _ _ ⟨hxn,hxd⟩ ⟨hyn,hyd⟩).2
/-- All four actual raw-operation branches have a fixed cubic clock in their input bytes. -/
theorem rawTime_le (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd:List Bool)
    (s:Nat) (hs:1 ≤ s) (hxn:xn.length ≤ s) (hxd:xd.length ≤ s) (hyn:yn.length ≤ s) (hyd:yd.length ≤ s) :
    rawTime op sx xn xd sy yn yd ≤1000000*s^3:=by
  have h0:=productTime_le xn yd s hs hxn hyd
  have h1:=productTime_le yn xd s hs hyn hxd
  have h2:=productTime_le xn yn s hs hxn hyn
  have h3:=productTime_le xd yd s hs hxd hyd
  have hl: (mulBits xn yd).bits.length ≤3*s:=by have h:=SemiprimeBitArithmetic.mulBits_length xn yd;omega
  have hr: (mulBits yn xd).bits.length ≤3*s:=by have h:=SemiprimeBitArithmetic.mulBits_length yn xd;omega
  have ha:=sumTime_le sx (mulBits xn yd).bits sy (mulBits yn xd).bits (3*s) (by omega) hl hr
  have hs1:s ≤ s^3:=Nat.le_pow (by decide:0<3)
  cases op <;> dsimp only [rawTime] <;> omega
/-- Every actual cleanup byte, including the two raw cross-product caches, is linearly paid. -/
theorem cleanupTime_le (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool)
    (s:Nat) (hs:1 ≤ s) (hxn:xn.length ≤ s) (hxd:xd.length ≤ s) (hyn:yn.length ≤ s) (hyd:yd.length ≤ s) :
    cleanupTime (rawResult op sx xn xd sy yn yd template) ≤20*s:=by
  have hl:=SemiprimeBitArithmetic.mulBits_length xn yd
  have hr:=SemiprimeBitArithmetic.mulBits_length yn xd
  cases op <;> simp only [cleanupTime,rawResult,ready,leftReady,binary,List.length_nil,ite_true,ite_false,
    reduceCtorEq] <;> omega
/-- Exact raw normalized quotient lengths remain bounded by their actual original widths, including zero-denominator totalization. -/
theorem normalized_width (negative:Bool) (num den:List Bool) :
    (normalized negative num den).numerator.magnitude.length ≤ num.length ∧
    (normalized negative num den).denominator.length ≤ den.length+1:=by
  unfold normalized SemiprimeD1StackRationalNormalizeSpec.word
  split
  · exact ⟨by simp [SemiprimeRationalBits.zeroWord],by simp [SemiprimeRationalBits.zeroWord]⟩
  · exact ⟨(SemiprimeD1StackRationalNormalizeSpec.numerator_length num den).le,
      (SemiprimeD1StackRationalNormalizeSpec.denominator_length num den).le.trans (by omega)⟩
/-- SAME actual normalizer source and BOTH full WordFit calls have quartic cost in raw bytes plus actual template cells. -/
theorem finishTime_le (num den template:List Bool) (s:Nat) (hs:1 ≤ s)
    (hn:num.length ≤4*s) (hd:den.length ≤4*s) (hw:template.length ≤ s) :
    finishTime num den template ≤1000000000000000*s^4:=by
  have hN:=SemiprimeD1StackRationalNormalizeBounds.runBound_le num den
  have hi:SemiprimeD1StackRationalNormalizeEncoding.inputSize num den ≤10*s:=by
    unfold SemiprimeD1StackRationalNormalizeEncoding.inputSize;omega
  have hp: (SemiprimeD1StackRationalNormalizeEncoding.inputSize num den)^4 ≤ (10*s)^4:=Nat.pow_le_pow_left hi 4
  have hq:=normalized_width false num den
  have hf0:=SemiprimeD1StackWordFitBounds.totalTime_le (normalized false num den).numerator.magnitude template
  have hf1:=SemiprimeD1StackWordFitBounds.totalTime_le (normalized false num den).denominator template
  have hs1:s ≤ s^4:=Nat.le_pow (by decide:0<4)
  unfold SemiprimeD1StackRationalNormalizeBounds.polynomial at hN
  unfold finishTime
  nlinarith only [hN,hp,hq.1,hq.2,hf0,hf1,hn,hd,hw,hs,hs1]
/-- Coefficient/degree are fixed before the five original inputs; template VALUE-width is physically paid. -/
def polynomial (ls ld rs rd template:List Bool) :Nat:=100000000000000000000*(inputSize ls ld rs rd template)^6
/-- Whole literal operation source has its OWN fixed original-byte polynomial clock; no legacy report clock is transported. -/
theorem runBound_le (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    runBound op sx xn xd sy yn yd template ≤ polynomial (sx::xn) xd (sy::yn) yd template:=by
  let s:=inputSize (sx::xn) xd (sy::yn) yd template
  have hs:1 ≤ s:=by dsimp [s,inputSize];omega
  have hxn:xn.length ≤ s:=by dsimp [s,inputSize];omega
  have hxd:xd.length ≤ s:=by dsimp [s,inputSize];omega
  have hyn:yn.length ≤ s:=by dsimp [s,inputSize];omega
  have hyd:yd.length ≤ s:=by dsimp [s,inputSize];omega
  have hw:template.length ≤ s:=by dsimp [s,inputSize];omega
  have hs0:setupTime op xn yn ≤30*s:=by
    cases op <;> simp only [setupTime,binary,ite_true,Bool.false_eq_true,ite_false] <;> omega
  have hr:=rawTime_le op sx xn xd sy yn yd s hs hxn hxd hyn hyd
  have hc:=cleanupTime_le op sx xn xd sy yn yd template s hs hxn hxd hyn hyd
  have hb:=raw_width op sx xn xd sy yn yd s hxn hxd hyn hyd
  have hf:=finishTime_le (rawWord op sx xn xd sy yn yd).numerator.magnitude
    (rawWord op sx xn xd sy yn yd).denominator template s hs (by omega) (by omega) hw
  have hs1:s ≤ s^6:=Nat.le_pow (by decide:0<6)
  have hs3:s^3 ≤ s^6:=Nat.pow_le_pow_right hs (by decide:3 ≤ 6)
  have hs4:s^4 ≤ s^6:=Nat.pow_le_pow_right hs (by decide:4 ≤ 6)
  change runBound op sx xn xd sy yn yd template ≤100000000000000000000*s^6
  dsimp only [runBound]
  nlinarith only [hs0,hr,hc,hf,hs,hs1,hs3,hs4]
/-- Exact legacy fitted result from the honest five physical input words within its fixed polynomial. -/
theorem source_run_bounded (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    ∃q ≤ polynomial (sx::xn) xd (sy::yn) yd template,SemiprimeD1StackCalls.run program q
      (initial op (sx::xn) xd (sy::yn) yd template)=some (done op sx xn xd sy yn yd template):=
  ⟨runBound op sx xn xd sy yn yd template,runBound_le op sx xn xd sy yn yd template,source_run op sx xn xd sy yn yd template⟩
/-- SAME compiled finite36-role machine uses the whole five-input own polynomial. -/
noncomputable def machineSource (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    StateTransition.EvalsToInTime (machine op).step
      (SemiprimeD1StackCalls.configuration (initial op (sx::xn) xd (sy::yn) yd template))
      (some (SemiprimeD1StackCalls.configuration (done op sx xn xd sy yn yd template)))
      (polynomial (sx::xn) xd (sy::yn) yd template):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .leftSigned) (aux .numeratorOutput) (localLabel .start op false false) program
  exact ⟨⟨_,source_run op sx xn xd sy yn yd template⟩,runBound_le op sx xn xd sy yn yd template⟩
end RiemannGaussian.SemiprimeD1StackRationalOperationBounds

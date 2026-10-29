/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalNormalizeExecution
/-! # Own fixed original-byte polynomial clock for actual rational normalization -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalNormalizeBounds
open SemiprimeD1StackRationalNormalize SemiprimeD1StackRationalNormalizeEncoding
open SemiprimeD1StackRationalNormalizeSetup SemiprimeD1StackRationalNormalizeArithmetic SemiprimeD1StackRationalNormalizeExecution
/-- Actual GCD loop outputs never grow beyond the widths of their physically acquired current operands. -/
theorem iterate_width (n:Nat) (xs ys:List Bool) (s:Nat) (hx:xs.length≤ s) (hy:ys.length≤ s) :
    (SemiprimeD1StackEuclidGCDSpec.iterate n xs ys).word.length≤ s:=by
  induction n generalizing xs ys with
  | zero=>exact (SemiprimeD1StackSourceEnvironmentEncoding.normalize_length xs).trans hx
  | succ n ih=>
    by_cases hz:ys=[]
    · simpa only [SemiprimeD1StackEuclidGCDSpec.iterate,ite_eq_left hz] using
        (SemiprimeD1StackSourceEnvironmentEncoding.normalize_length xs).trans hx
    · simpa only [SemiprimeD1StackEuclidGCDSpec.iterate,ite_eq_right hz] using
        ih ys _ hy ((SemiprimeD1StackEuclidGCDLoop.next_width xs ys).trans hy)
/-- The actual acquired compact divisor is bounded by original binary input bytes, with no supplied width. -/
theorem gcd_length (num den:List Bool) :(S.gcd num den).length≤ inputSize num den:=by
  apply iterate_width
  · unfold inputSize;omega
  · exact (SemiprimeD1StackSourceEnvironmentEncoding.normalize_length den).trans (by unfold inputSize;omega)
/-- Paid physical signed-word copy/parse and actual complete denominator scan are linear in original bytes. -/
theorem setupTime_le (num den:List Bool) :setupTime num den≤100*(inputSize num den):=by
  unfold setupTime inputSize
  omega
/-- A complete real quotient phase pays both operand copies, all restoring steps, output copy and both output drains. -/
theorem quotientTime_le (xs g:List Bool) (s:Nat) (hs:1≤ s) (hx:xs.length≤ s) (hg:g.length≤ s) :
    quotientTime xs g≤1000*s^2:=by
  have hd:=SemiprimeD1StackDividerExecution.source_time xs g
  have hw:=SemiprimeBitDivision.divideLoop_widths xs g
  unfold quotientTime SemiprimeD1StackDividerExecution.timeBound at *
  rw [hw.1,hw.2.1] at *
  have hm:xs.length*(g.length+2)≤ s*(s+2):=Nat.mul_le_mul hx (Nat.add_le_add_right hg 2)
  have hsq:s≤ s^2:=by nlinarith
  nlinarith
/-- Actual positive branch composes the SAME GCD18 whole source with the SAME two Divider11 calls. -/
theorem positiveTime_le (num den:List Bool) :positiveTime num den≤1000000000*(inputSize num den)^4:=by
  let I:=inputSize num den
  have hI:1≤ I:=by dsimp [I,inputSize];omega
  have hn:num.length≤ I:=by dsimp [I,inputSize];omega
  have hd:den.length≤ I:=by dsimp [I,inputSize];omega
  have hg:(S.gcd num den).length≤ I:=gcd_length num den
  have hN:=quotientTime_le num (S.gcd num den) I hI hn hg
  have hD:=quotientTime_le den (S.gcd num den) I hI hd hg
  have hG:=SemiprimeD1StackEuclidGCDBounds.runBound_le num den
  unfold SemiprimeD1StackEuclidGCDBounds.polynomial at hG
  have hsize:SemiprimeD1StackEuclidGCDEncoding.inputSize num den≤ I:=by
    dsimp [SemiprimeD1StackEuclidGCDEncoding.inputSize,I,inputSize];omega
  have hpow:(SemiprimeD1StackEuclidGCDEncoding.inputSize num den)^4≤ I^4:=Nat.pow_le_pow_left hsize 4
  have h1:I≤ I^4:=Nat.le_pow (by decide:0<(4:Nat))
  have h2:I^2≤ I^4:=Nat.pow_le_pow_right hI (by decide:2≤4)
  have hGb:SemiprimeD1StackEuclidGCDExecution.runBound num den≤100000000*I^4:=
    hG.trans (Nat.mul_le_mul_left _ hpow)
  change positiveTime num den≤1000000000*I^4
  unfold positiveTime
  nlinarith only [hN,hD,hGb,h1,h2,hI,hn,hg]
/-- Coefficient and degree are fixed before both original words; neither operand's numeric value is expanded into unary. -/
def polynomial (num den:List Bool) :Nat:=10000000000*(inputSize num den)^4
/-- Whole original-two-word normalizer has its OWN actual fixed polynomial clock, including the guarded zero branch. -/
theorem runBound_le (num den:List Bool) :runBound num den≤ polynomial num den:=by
  have hs:=setupTime_le num den
  have hp:=positiveTime_le num den
  have hI:1≤ inputSize num den:=by unfold inputSize;omega
  have hn:num.length≤ inputSize num den:=by unfold inputSize;omega
  have h14:inputSize num den≤(inputSize num den)^4:=Nat.le_pow (by decide:0<(4:Nat))
  unfold runBound branchTime polynomial
  split <;> nlinarith only [hs,hp,hI,hn,h14]
/-- Actual exact legacy byte result from the original signed binary word and denominator, within the fixed bound. -/
theorem source_run_bounded (negative:Bool) (num den:List Bool) :
    ∃q≤ polynomial num den,SemiprimeD1StackCalls.run program q (initial (negative::num) den)=some (done negative num den):=
  ⟨runBound num den,runBound_le num den,source_run negative num den⟩
/-- SAME genuine fixed22-role machine has the whole original-two-word polynomial certificate. -/
noncomputable def machineSource (negative:Bool) (num den:List Bool) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial (negative::num) den))
      (some (SemiprimeD1StackCalls.configuration (done negative num den))) (polynomial num den):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .originalSigned) (aux .numeratorOutput) .start program
  let h:=source_run_bounded negative num den
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackRationalNormalizeBounds

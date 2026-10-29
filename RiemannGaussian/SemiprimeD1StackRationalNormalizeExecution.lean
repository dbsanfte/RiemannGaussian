/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalNormalizeSetup
import RiemannGaussian.SemiprimeD1StackRationalNormalizeArithmetic
/-! # Whole actual two-word normalizer, exact legacy bytes and its own instruction clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalNormalizeExecution
open SemiprimeD1StackRationalNormalize SemiprimeD1StackRationalNormalizeEncoding SemiprimeD1StackRationalNormalizeCalls
open SemiprimeD1StackRationalNormalizeSetup SemiprimeD1StackRationalNormalizeArithmetic
open SemiprimeD1StackProcedureTrace
namespace S
export SemiprimeD1StackRationalNormalizeSpec (gcd numerator denominator word)
end S
/-- Actual positive-branch calls and drains; no legacy report clock appears. -/
def positiveTime (num den:List Bool) :Nat:=
  (SemiprimeD1StackEuclidGCDExecution.runBound num den+1)+quotientTime num (S.gcd num den)+
    quotientTime den (S.gcd num den)+(((S.gcd num den).length+1)+(num.length+1))
/-- Complete actual positive arithmetic branch, including every real return and private-word drain. -/
theorem positive_run (negative:Bool) (num den:List Bool) :
    Runs program (positiveTime num den) .gcdCall (bank (parsed negative num den)) .done
      (bank {originalSigned:=negative::num,originalRight:=den,signOutput:=[negative], numeratorOutput:=S.numerator num den,denominatorOutput:=S.denominator num den}) :=by
  have h0:=gcd_ready negative num den
  have h1:=numerator_run negative num den (S.gcd num den) [] []
  simp only [List.append_nil] at h1
  have h2:=denominator_run negative num den (S.gcd num den) (S.numerator num den) []
  simp only [List.append_nil] at h2
  have h3:=cleanup_run negative num den (S.gcd num den) (S.numerator num den) (S.denominator num den)
  exact P.join (P.join (P.join h0 h1) h2) h3
/-- Own exact branch clock is selected by the actual copied-denominator OR bit. -/
def branchTime (num den:List Bool) :Nat:=
  if (SemiprimeBitDivision.nonzeroBits den).nonzero then positiveTime num den else 2+1+1+(num.length+1)
/-- Own whole source includes paid signed-word acquisition, guard, arithmetic/zero branch, cleanup and actual halt. -/
def runBound (num den:List Bool) :Nat:=setupTime num den+branchTime num den+1
/-- Honest whole entry has only the original sign-prefixed binary numerator and original binary denominator.
The sign and magnitude are actually parsed; zero denominator is physically guarded. -/
theorem source_trace (negative:Bool) (num den:List Bool) :
    Runs program (runBound num den-1) .start (input (negative::num) den) .done (result negative num den) :=by
  have h0:=setup_run negative num den
  cases hc:(SemiprimeBitDivision.nonzeroBits den).nonzero with
  | false=>
    have hz:SemiprimeBitArithmetic.bitValue den=0:=by
      have hn:¬0<SemiprimeBitArithmetic.bitValue den:=by
        intro hp
        have he:=(SemiprimeBitDivision.nonzeroBits_correct den).mpr hp
        rw [hc] at he;cases he
      omega
    rw [hc] at h0
    have h1:=zero_run negative num den
    have h:=P.join h0 h1
    have he:bank {originalSigned:=negative::num,originalRight:=den,signOutput:=[false],denominatorOutput:=[true]}=
        result negative num den:=by
      unfold result SemiprimeD1StackRationalNormalizeSpec.word
      rw [ite_eq_left hz]
      rfl
    rw [he] at h
    simpa only [runBound,branchTime,hc,Bool.false_eq_true,ite_false,Nat.add_sub_cancel] using h
  | true=>
    have hp:=(SemiprimeBitDivision.nonzeroBits_correct den).mp hc
    have hz:SemiprimeBitArithmetic.bitValue den≠0:=by omega
    rw [hc] at h0
    have h1:=positive_run negative num den
    have h:=P.join h0 h1
    have he:bank {originalSigned:=negative::num,originalRight:=den,signOutput:=[negative], numeratorOutput:=S.numerator num den,denominatorOutput:=S.denominator num den}=result negative num den:=by
      unfold result SemiprimeD1StackRationalNormalizeSpec.word
      rw [ite_eq_right hz]
    rw [he] at h
    simpa only [runBound,branchTime,hc,ite_true,Nat.add_sub_cancel] using h
/-- Exact actual final halt clears flags and whole-entry return cells within the SAME complete source clock. -/
theorem source_run (negative:Bool) (num den:List Bool) :
    SemiprimeD1StackCalls.run program (runBound num den) (initial (negative::num) den)=some (done negative num den) :=by
  obtain ⟨finish,hfin,hAt⟩:=source_trace negative num den [] (initial (negative::num) den) ⟨rfl,rfl,rfl⟩
  have he:runBound num den=(runBound num den-1)+1:=by unfold runBound;omega
  rw [he,SemiprimeD1StackReturnLink.run_add,hfin,Option.bind_some]
  exact halt_run program .done rfl (result negative num den) [] finish hAt
/-- Genuine fixed22-role finite machine executes from the original two actual words to exact normalized output. -/
noncomputable def normalizeInTime (negative:Bool) (num den:List Bool) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial (negative::num) den))
      (some (SemiprimeD1StackCalls.configuration (done negative num den))) (runBound num den):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .originalSigned) (aux .numeratorOutput) .start program
  exact ⟨⟨runBound num den,source_run negative num den⟩,le_rfl⟩
/-- All three physical stopped output words equal exact legacy normalized bytes, without a padding shortcut. -/
theorem output_legacy (negative:Bool) (num den:List Bool) :
    outputWord (done negative num den).data=(SemiprimeRationalBits.reduceBits ⟨⟨negative,num⟩,den⟩).word:=
  SemiprimeD1StackRationalNormalizeSpec.word_legacy negative num den
/-- The actual stopped signed numerator and denominator represent the original rational exactly. -/
theorem output_value (negative:Bool) (num den:List Bool) :
    (outputWord (done negative num den).data).value=(⟨⟨negative,num⟩,den⟩:SemiprimeRationalBits.RationalWord).value:=
  SemiprimeD1StackRationalNormalizeSpec.word_value negative num den
/-- Actual normalized denominator is always positive, including the physically guarded total zero branch. -/
theorem output_valid (negative:Bool) (num den:List Bool) :(outputWord (done negative num den).data).Valid:=
  SemiprimeD1StackRationalNormalizeSpec.word_valid negative num den
/-- Canonical integer numerator and denominator are read from the three actual stopped output words. -/
theorem output_components (negative:Bool) (num den:List Bool) :
    (outputWord (done negative num den).data).numerator.value=(⟨⟨negative,num⟩,den⟩:SemiprimeRationalBits.RationalWord).value.num ∧
      SemiprimeBitArithmetic.bitValue (outputWord (done negative num den).data).denominator=
        (⟨⟨negative,num⟩,den⟩:SemiprimeRationalBits.RationalWord).value.den:=
  SemiprimeD1StackRationalNormalizeSpec.word_components negative num den
end RiemannGaussian.SemiprimeD1StackRationalNormalizeExecution

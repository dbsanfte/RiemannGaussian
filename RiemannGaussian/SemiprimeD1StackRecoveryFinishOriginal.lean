/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishResources
import RiemannGaussian.SemiprimeD1RecoveryPhysicalRun
/-! # Original recovery finalizer binding with its own real fixed-program clock
The canonical numerator/common denominator words are actual inputs to this
stage. Their upstream row/weight/child acquisition is not asserted by this
prepared three-word source. No native report clock is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishOriginal
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishExecution
open SemiprimeD1StackRecoveryFinishBounds
open SemiprimeBitIndexClipping (SignedWord)
open SemiprimeBitArithmetic (bitValue)
namespace I
export SemiprimeD1RecoveryIntegerBits (Entry native denominator accumulate)
end I
namespace Up
export SemiprimeD1RecoveryPhysicalRun (entries original_entry_bounds entries_original width childView run run_bits run_value)
end Up
/-- Exact canonical physical entries, proof-side operand projection only. -/
def entryWords (a M u:Nat) (children:List (List (List Bool))):List I.Entry:=
  (Up.entries children (SemiprimeD1RecoveryRowsBits.acquire a M u).rows).entries
/-- Actual original false-bit template, not an operand supplied to the finish program. -/
def template (a M P:Nat):List Bool:=List.replicate (SemiprimeD1RecoveryPhysicalRun.width a M P) false
/-- Actual physical common-denominator word from the existing upstream data path. -/
def denominatorWord (a M u P:Nat) (children:List (List (List Bool))):List Bool:=
  (I.denominator (template a M P) (entryWords a M u children)).bits
/-- Actual physical accumulated signed numerator from that same data path. -/
def numeratorWord (a M u P:Nat) (children:List (List (List Bool))):SignedWord:=
  (I.accumulate (template a M P) (denominatorWord a M u P children) (entryWords a M u children)).word
/-- Original positivity follows from actual canonical denominator bounds and the paid original template width. -/
theorem denominator_positive (a M u P:Nat) (hM:u ≤M) (children:List (List (List Bool))):
    0 < bitValue (denominatorWord a M u P children):=by
  let es:=entryWords a M u children
  let A:=SemiprimeD1HermiteWeightBits.weightEnvelope a M
  let K:=SemiprimeD1WireKernelOriginal.size a*(4*M)
  have hb:=Up.original_entry_bounds a M u hM children
  change (∀e∈es,0 < bitValue e.denominator ∧bitValue e.denominator ≤2^A ∧
    e.numerator.value.natAbs ≤2^A) ∧es.length ≤K at hb
  have hw:K+A+A*K+P+1 ≤(template a M P).length:=by
    simp only [template,List.length_replicate,SemiprimeD1RecoveryPhysicalRun.width,A,K,
      SemiprimeD1IntegerRecoveryHeight.recoveryExponent]
    nlinarith only
  have hwd:A*es.length+1 ≤(template a M P).length:=by
    have hm:=Nat.mul_le_mul_left A hb.2
    omega
  have hd:=SemiprimeD1RecoveryIntegerBits.denominator_correct (template a M P) es A
    (fun e he=>(hb.1 e he).2.1) hwd
  have he:=Up.entries_original a M u hM children
  change I.native es=SemiprimeD1RecoveryCanonicalRun.canonical
    (SemiprimeD1IntegerRecovery.terms a M u (Up.childView children)) at he
  change 0 < bitValue (I.denominator (template a M P) es).bits
  rw [hd,he,SemiprimeD1RecoveryCanonicalRun.denominator_value]
  exact SemiprimeD1IntegerRecovery.denominator_pos _
/-- This actual prepared-stage output equals the literal original complete physical data-path output byte for byte. -/
theorem output_physical (a M u p P:Nat) (children:List (List (List Bool))):
    (done (numeratorWord a M u P children) (denominatorWord a M u P children) p).data output=
      (SemiprimeD1RecoveryPhysicalRun.run a M u p P children).bits:=by
  rw [output_original,SemiprimeD1RecoveryPhysicalRun.run_bits]
  rfl
/-- Fixed own-source clock plus exact original recovery bytes, with only actual numerator/denominator/WIDTH as physical stage inputs. -/
theorem source_original_bounded (a M u p P:Nat) (hM:u ≤M) (children:List (List (List Bool))):
    ∃q ≤runBound (numeratorWord a M u P children) (denominatorWord a M u P children) p,
      SemiprimeD1StackCalls.run program q
        (initial (B.signedTape (numeratorWord a M u P children)) (denominatorWord a M u P children) (List.replicate p true))=
          some (done (numeratorWord a M u P children) (denominatorWord a M u P children) p) ∧
      (done (numeratorWord a M u P children) (denominatorWord a M u P children) p).data output=
        (SemiprimeD1RecoveryPhysicalRun.run a M u p P children).bits:=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded (numeratorWord a M u P children) (denominatorWord a M u P children)
    (denominator_positive a M u P hM children) p
  exact ⟨q,hq,hr,output_physical a M u p P children⟩
/-- The identical actual output refines the original integer recovery residue, without identifying native and source clocks. -/
theorem output_value (a M u p P:Nat) (hM:u ≤M) (children:List (List (List Bool)))
    (hc:∀row∈children,∀x∈row,x.length ≤P):
    (bitValue ((done (numeratorWord a M u P children) (denominatorWord a M u P children) p).data output):ZMod (2^p))=
      SemiprimeD1IntegerRecoveryResidue.finish p
        (SemiprimeD1IntegerRecovery.run a M u (Up.childView children)):=by
  rw [output_physical]
  exact SemiprimeD1RecoveryPhysicalRun.run_value a M u p P children hM hc
/-- Fixed coefficient/degree precede every input; this is a genuinely uniform actual source theorem. -/
theorem uniform_source:∃coef degree:Nat,∀(n:SignedWord) (d:List Bool) (_hd:0 < bitValue d) (p:Nat),
    ∃q ≤coef*(resource n d p+1)^degree,
      SemiprimeD1StackCalls.run program q (initial (B.signedTape n) d (List.replicate p true))=some (done n d p) ∧
      (done n d p).data output=(SemiprimeD1RecoveryStripBits.finish p n d).bits:=by
  refine ⟨1000000000000,4,?_⟩
  intro n d hd p
  obtain ⟨q,hq,hr⟩:=source_run_bounded n d hd p
  exact ⟨q,hq,hr,output_original n d p⟩
end RiemannGaussian.SemiprimeD1StackRecoveryFinishOriginal

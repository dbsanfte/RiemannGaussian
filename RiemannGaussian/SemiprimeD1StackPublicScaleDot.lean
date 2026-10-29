/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleAcquire
import RiemannGaussian.SemiprimeD1StackPublicScaleInputs
/-! # Whole actual scale dot call with internally derived source validity -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicScaleDot
open SemiprimeD1StackPublicScale SemiprimeD1StackPublicScaleState
open SemiprimeD1StackPublicScaleInputs SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
/-- Actual selected code and literal2 plus retained descriptor markers. -/
def args (bits stride frequency : List Bool) (inverse : Bool) : I.Args :=
  ⟨baseCode bits inverse,stride,frequency,[true,true]⟩
/-- Actual acquired input word, including complete physical EOF padding. -/
def inputWord (bits raw : List Bool) : List Bool := SemiprimeD1StackWordBlockExecution.result raw (cached bits)
/-- Original next output word, physically read only after the actual success bit. -/
def outputWord (bits raw : List Bool) : List Bool :=
  SemiprimeD1StackWordBlockExecution.result (raw.drop (cached bits).length) (cached bits)
/-- Actual full result of the included dot, retaining its actual acquired vector. -/
def evaluated (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) : Stack→List Bool :=
  store (roots bits) (SemiprimeD1StackInputDotExecution.done (paddedRaw bits raw)
    (args bits stride frequency inverse) (cached bits) (expression bits inverse) j k 2 []).data raw [] [] [] [] [] []
/-- Whole real InputDot: canonicality is COMPUTED, not supplied. Original N
acquisition derives base validity and M>1; only physical j/k marker formats remain. -/
theorem dot_call (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ)
    (hj : stride=SemiprimeD1StackUnaryDivmod.unary j)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary k)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ∃t≤SemiprimeD1StackInputDotExecution.timeBound (paddedRaw bits raw) (args bits stride frequency inverse)
      (cached bits) (expression bits inverse) j k 2+1,
      Runs program t .compute (prepared bits raw stride frequency inverse) .branch
        (evaluated bits raw stride frequency inverse j k) := by
  obtain ⟨hm,hb⟩:=original_valid bits hc hN inverse
  rw [←expression_original bits hc hN inverse] at hb
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackInputDotExecution.source_run (paddedRaw bits raw)
    (args bits stride frequency inverse) (cached bits) (expression bits inverse)
    (source_code bits inverse) j k 2 hj hk rfl [] hm hb
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program dotStack Label.dot dot_injective
    I.program .start (fun _=>rfl) .compute .branch rfl t
    (I.initial (paddedRaw bits raw) (args bits stride frequency inverse) (cached bits) [])
    (SemiprimeD1StackInputDotExecution.done (paddedRaw bits raw) (args bits stride frequency inverse)
      (cached bits) (expression bits inverse) j k 2 []) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro q;rfl
    · intro q _;rfl
  · constructor
    · intro q;rfl
    · intro q hq;rcases q with q|q
      · rfl
      · rcases q with q|q
        · exact (hq q rfl).elim
        · rfl
/-- Exact acquired zero/input words, independent of physical source/cache fields. -/
theorem words_value (bits raw stride frequency : List Bool) (inverse : Bool) :
    SemiprimeD1StackInputDotExecution.words (paddedRaw bits raw) (args bits stride frequency inverse) (cached bits)=
      [SemiprimeD1StackPublicScaleMeaning.zeroWord (cached bits),inputWord bits raw] :=
  acquired_words bits raw
/-- The actual status Boolean is the real acquired-vector canonicality guard. -/
theorem status_value (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) :
    evaluated bits raw stride frequency inverse j k (dotStack I.status)=
      [SemiprimeD1StackPublicScaleMeaning.guard (cached bits) (inputWord bits raw)] := by
  change (SemiprimeD1StackInputDotExecution.done (paddedRaw bits raw) (args bits stride frequency inverse)
    (cached bits) (expression bits inverse) j k 2 []).data I.status=_
  rw [SemiprimeD1StackInputDotExecution.status_original,words_value]
  rfl
/-- Actual canonical result bytes, not an expected numeric output operand. -/
theorem result_value (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) :
    evaluated bits raw stride frequency inverse j k (dotStack I.output)=
      if SemiprimeD1StackPublicScaleMeaning.guard (cached bits) (inputWord bits raw) then
        (SemiprimeMacroEntryBitPrimitives.execute (cached bits)
          (SemiprimeMacroEntryBitPrimitives.dotExpr (expression bits inverse) j k
            (SemiprimeD1StackPublicScaleMeaning.inputAt (cached bits) (inputWord bits raw)) 2)).bits else [] := by
  change (SemiprimeD1StackInputDotExecution.done (paddedRaw bits raw) (args bits stride frequency inverse)
    (cached bits) (expression bits inverse) j k 2 []).data I.output=_
  rw [SemiprimeD1StackInputDotExecution.output_original,words_value]
  rfl
/-- The raw suffix after the actual TWO-word dot is the original second word,
not a prepared output-record argument. -/
theorem suffix_value (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) :
    evaluated bits raw stride frequency inverse j k (dotStack I.suffixRole)=raw.drop (cached bits).length := by
  change (SemiprimeD1StackInputDotExecution.done (paddedRaw bits raw) (args bits stride frequency inverse)
    (cached bits) (expression bits inverse) j k 2 []).data I.suffixRole=_
  rw [SemiprimeD1StackInputDotExecution.retained_suffix]
  change (List.replicate (cached bits).length false++raw).drop (2*(cached bits).length)=_
  simp only [List.drop_append,List.length_replicate,List.drop_replicate]
  have h0 : (cached bits).length-2*(cached bits).length=0 := by omega
  have h1 : 2*(cached bits).length-(cached bits).length=(cached bits).length := by omega
  rw [h0,h1]
  rfl
end RiemannGaussian.SemiprimeD1StackPublicScaleDot

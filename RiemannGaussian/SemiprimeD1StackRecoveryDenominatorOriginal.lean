/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorResources
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorSemantics
import RiemannGaussian.SemiprimeD1RecoveryPhysicalRun
/-! # Original canonical-row common denominator, exact bytes and own source cost
This stage consumes actual row/template tapes. The original legacy row family
below specifies those bytes in proofs; it is not an executable row producer or
an assertion of original-N acquisition. No child coefficient read executes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryDenominatorOriginal
open SemiprimeD1StackRecoveryDenominator SemiprimeD1StackRecoveryDenominatorEncoding
open SemiprimeD1StackRecoveryDenominatorExecution SemiprimeD1StackRecoveryDenominatorBounds
open SemiprimeBitArithmetic (bitValue)
namespace R
export SemiprimeD1RecoveryRowsBits (Row acquire)
end R
namespace I
export SemiprimeD1RecoveryIntegerBits (Entry denominator native denominator_correct native_denominator_bound)
end I
namespace Up
export SemiprimeD1RecoveryPhysicalRun (entries original_entry_bounds entries_original childView)
end Up
namespace S
export SemiprimeD1StackRecoveryDenominatorSemantics (entries denominator_words oldWords result_old)
end S
/-- Proof-side literal legacy row codec, not a runtime digit encoder or field getter. -/
def encodeRow (r:R.Row):Row:=![
  (SemiprimeEncodedRowSelection.digits (r.node+1) r.node).bits,
  (SemiprimeEncodedRowSelection.digits (r.index+1) r.index).bits,
  [r.word.numerator.negative],r.word.numerator.magnitude,r.word.denominator]
/-- The fifth physical field is exactly the original copied canonical denominator. -/
theorem encode_denominator (r:R.Row):encodeRow r 4=r.word.denominator:=rfl
/-- Original row bytes, a semantic specification of an upstream acquired tape only. -/
def originalRows (a M u:Nat):List Row:=(R.acquire a M u).rows.map encodeRow
/-- Original paid physical width template, retained by the actual source. -/
def widthTemplate (a M P:Nat):List Bool:=List.replicate (SemiprimeD1RecoveryPhysicalRun.width a M P) false
/-- Actual child-selection reports preserve every original denominator field literally. -/
theorem physical_denominators (children:List (List (List Bool))) (rows:List R.Row):
    ((Up.entries children rows).entries.map (fun e=>e.denominator))=rows.map (fun r=>r.word.denominator):=by
  induction rows with
  | nil=>rfl
  | cons r rows ih=>simp only [Up.entries,List.map_cons,ih]
/-- Child coefficient selection never changes the original row count. -/
theorem physical_length (children:List (List (List Bool))) (rows:List R.Row):
    (Up.entries children rows).entries.length=rows.length:=by
  have h:=congrArg List.length (physical_denominators children rows)
  simpa only [List.length_map] using h
/-- The literal five-field codec preserves the exact original denominator-word sequence. -/
theorem encoded_denominators (rows:List R.Row):
    (S.entries (rows.map encodeRow)).map (fun e=>e.denominator)=rows.map (fun r=>r.word.denominator):=by
  simp only [S.entries,List.map_map,Function.comp_def,encode_denominator]
/-- Original canonical height bounds every actual fifth field; no requested denominator/fit answer enters the source. -/
theorem original_caps (a M u:Nat) (hM:u ≤M):
    (∀r∈originalRows a M u,bitValue (r 4) ≤2^SemiprimeD1HermiteWeightBits.weightEnvelope a M) ∧
      (originalRows a M u).length ≤SemiprimeD1WireKernelOriginal.size a*(4*M):=by
  let rows:=(R.acquire a M u).rows
  let es:=(Up.entries [] rows).entries
  have hb:=Up.original_entry_bounds a M u hM []
  change (∀e∈es,0 < bitValue e.denominator ∧bitValue e.denominator ≤2^SemiprimeD1HermiteWeightBits.weightEnvelope a M ∧
    e.numerator.value.natAbs ≤2^SemiprimeD1HermiteWeightBits.weightEnvelope a M) ∧es.length ≤_ at hb
  constructor
  · intro r hr
    obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hr
    have hm:s.word.denominator∈es.map (fun e=>e.denominator):=by
      rw [physical_denominators]
      exact List.mem_map.mpr ⟨s,hs,rfl⟩
    obtain ⟨e,he,hd⟩:=List.mem_map.mp hm
    rw [encode_denominator,←hd]
    exact (hb.1 e he).2.1
  · change (rows.map encodeRow).length ≤_
    rw [List.length_map]
    rw [physical_length] at hb
    exact hb.2
/-- The actual original template width is large enough for every canonical denominator suffix. -/
theorem original_width (a M u P:Nat) (hM:u ≤M):
    SemiprimeD1HermiteWeightBits.weightEnvelope a M*(originalRows a M u).length+1 ≤(widthTemplate a M P).length:=by
  have hc:=(original_caps a M u hM).2
  have hm:=Nat.mul_le_mul_left (SemiprimeD1HermiteWeightBits.weightEnvelope a M) hc
  have hw:SemiprimeD1WireKernelOriginal.size a*(4*M)+SemiprimeD1HermiteWeightBits.weightEnvelope a M+
      SemiprimeD1HermiteWeightBits.weightEnvelope a M*(SemiprimeD1WireKernelOriginal.size a*(4*M))+P+1 ≤
        (widthTemplate a M P).length:=by
    simp only [widthTemplate,List.length_replicate,SemiprimeD1RecoveryPhysicalRun.width,
      SemiprimeD1IntegerRecoveryHeight.recoveryExponent]
    nlinarith only
  omega
/-- Actual output is EXACT old W-padded common-denominator bytes for all original rows and all child tapes. -/
theorem output_original (a M u P:Nat) (hM:u ≤M) (children:List (List (List Bool))):
    (done (originalRows a M u) (widthTemplate a M P)).data output=
      (I.denominator (widthTemplate a M P) (Up.entries children (R.acquire a M u).rows).entries).bits:=by
  rw [output_result,S.result_old _ _ _ (original_caps a M u hM).1 (original_width a M u P hM),
    S.denominator_words,S.denominator_words]
  rw [originalRows,encoded_denominators,physical_denominators]
/-- Actual acquired binary output represents the ORIGINAL integer common denominator. -/
theorem output_value (a M u P:Nat) (hM:u ≤M) (children:List (List (List Bool))):
    bitValue ((done (originalRows a M u) (widthTemplate a M P)).data output)=
      (SemiprimeD1IntegerRecovery.run a M u (SemiprimeD1RecoveryPhysicalRun.childView children)).denominator:=by
  let es:=(Up.entries children (R.acquire a M u).rows).entries
  have hb:=Up.original_entry_bounds a M u hM children
  have hlen:es.length=(originalRows a M u).length:=by
    rw [physical_length]
    simp only [originalRows,List.length_map]
  have hw:SemiprimeD1HermiteWeightBits.weightEnvelope a M*es.length+1 ≤(widthTemplate a M P).length:=by
    rw [hlen]
    exact original_width a M u P hM
  have hd:∀e∈es,bitValue e.denominator ≤2^SemiprimeD1HermiteWeightBits.weightEnvelope a M:=
    fun e he=>(hb.1 e he).2.1
  rw [output_original a M u P hM children]
  rw [I.denominator_correct _ es _ hd hw,Up.entries_original a M u hM children,
    SemiprimeD1RecoveryCanonicalRun.denominator_value]
  simp only [SemiprimeD1IntegerRecovery.run,SemiprimeD1IntegerRecovery.denominatorRun_value]
/-- Original actual denominator positivity is derived, never supplied as an output answer. -/
theorem output_positive (a M u P:Nat) (hM:u ≤M) (children:List (List (List Bool))):
    0 < bitValue ((done (originalRows a M u) (widthTemplate a M P)).data output):=by
  rw [output_value a M u P hM children]
  simpa only [SemiprimeD1IntegerRecovery.run,SemiprimeD1IntegerRecovery.denominatorRun_value] using
    SemiprimeD1IntegerRecovery.denominator_pos
      (SemiprimeD1IntegerRecovery.terms a M u (SemiprimeD1RecoveryPhysicalRun.childView children))
/-- Numeric common-denominator growth has the actual original canonical-row height cap. -/
theorem output_value_bound (a M u P:Nat) (hM:u ≤M) (children:List (List (List Bool))):
    bitValue ((done (originalRows a M u) (widthTemplate a M P)).data output) ≤
      2^(SemiprimeD1HermiteWeightBits.weightEnvelope a M*(SemiprimeD1WireKernelOriginal.size a*(4*M))):=by
  rw [output_value a M u P hM children]
  simp only [SemiprimeD1IntegerRecovery.run,SemiprimeD1IntegerRecovery.denominatorRun_value]
  have hd:=SemiprimeD1IntegerRecoveryHeight.denominator_bound a M u hM (SemiprimeD1RecoveryPhysicalRun.childView children)
  have hl:=SemiprimeD1IntegerRecoveryHeight.terms_length a M u hM (SemiprimeD1RecoveryPhysicalRun.childView children)
  exact hd.trans (Nat.pow_le_pow_right (by decide:1 ≤(2:Nat))
    (Nat.mul_le_mul_left _ hl))
/-- Complete actual source retains its own uniform quartic clock while returning the original denominator bytes. -/
theorem source_original (a M u P:Nat) (hM:u ≤M) (children:List (List (List Bool))):
    ∃q ≤runBound (originalRows a M u) (widthTemplate a M P),
      SemiprimeD1StackCalls.run program q (initial (tape (originalRows a M u)) (widthTemplate a M P))=
        some (done (originalRows a M u) (widthTemplate a M P)) ∧
      (done (originalRows a M u) (widthTemplate a M P)).data output=
        (I.denominator (widthTemplate a M P) (Up.entries children (R.acquire a M u).rows).entries).bits:=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded (originalRows a M u) (widthTemplate a M P)
  exact ⟨q,hq,hr,output_original a M u P hM children⟩
/-- Original output word has its genuine paid width, except the old literal-one nil case. -/
theorem output_length (rs:List Row) (template:List Bool):
    ((done rs template).data output).length ≤template.length+1:=by
  rw [output_result]
  cases rs with
  | nil=>change 1 ≤template.length+1;omega
  | cons r rs=>
    change (SemiprimeD1StackWordFitExecution.result (raw (r::rs) [true]) template).length ≤template.length+1
    rw [SemiprimeD1StackWordFitExecution.result_length]
    omega
/-- Fixed source coefficient and degree precede every actual row tape and template. -/
theorem uniform_source:∃coef degree:Nat,∀(rs:List Row) (template:List Bool),
    ∃q ≤coef*((tape rs).length+template.length+1)^degree,
      SemiprimeD1StackCalls.run program q (initial (tape rs) template)=some (done rs template):=by
  refine ⟨1000000000000,4,?_⟩
  intro rs template
  exact source_run_bounded rs template
end RiemannGaussian.SemiprimeD1StackRecoveryDenominatorOriginal

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentBounds
import RiemannGaussian.SemiprimeSourceWordBankSemantics
/-! # Same actual source acquires exact original prefix/default environment reads
The selected prefix is newest first, original variable zero is oldest, and
out-of-prefix reads retain the original default candidate ID zero. Free is
identified only for valid original endpoint keys in the actual remaining range.
Original Word functions/environment values occur only in these proofs, never
in the parameterless finite instruction table or physical source operands.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceEnvironmentOriginal
open SemiprimeD1StackSourceEnvironment SemiprimeD1StackSourceEnvironmentExecution
open SemiprimeD1StackSourceEnvironmentEncoding SemiprimeD1StackSourceEnvironmentMeaning
open SemiprimeD1StackSourceEnvironmentBounds
open SemiprimeBitArithmetic (bitValue)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Same-source retained dictionary is the literal first-match ABI in original newest-first prefix order. -/
theorem dictionary_original (ids:List (List Bool)) :
    (done ids).data (aux .dictionary)=L.records (prefixRows ids) [] :=rfl
/-- Actual acquired next-key word is literally the old compact prefix cache counter. -/
theorem nextKey_original (ids:List (List Bool)) :
    (done ids).data (aux .nextKey)=(SemiprimeSourceHistogramPrefix.acquire ids).nextKey :=original_nextKey ids
/-- Exactly one real compact increment per parsed oldest-first prefix field acquires the original prefix size. -/
theorem nextKey_value (ids:List (List Bool)) :bitValue ((done ids).data (aux .nextKey))=ids.length :=variableKey_value _
/-- All physical original-variable keys are compact binary words, including empty key zero. -/
theorem nextKey_compact (ids:List (List Bool)) :SemiprimeSourceCompactBits.Compact ((done ids).data (aux .nextKey)) :=
  variableKey_compact _
/-- Whole source retains the actual newest-first selected input bytes, including high-zero ID padding. -/
theorem prefix_retained (ids:List (List Bool)) :(done ids).data (aux .prefix)=vectorBits ids :=rfl
/-- Original default-empty-ID meaning outside the acquired prefix, with no supplied free/active verdict. -/
theorem expected_outside (ids:List (List Bool)) (i:Nat) (hi:ids.length ≤ i) :
    SemiprimeSourceHistogramPrefix.expected ids i=[] :=by
  have hn:ids.reverse[i]?=none:=List.getElem?_eq_none (by simpa only [List.length_reverse] using hi)
  unfold SemiprimeSourceHistogramPrefix.expected
  rw [hn]
  rfl
/-- Actual lookup always returns the exact original normalized reverse-prefix/default ID. -/
theorem lookup_output_original (ids:List (List Bool)) (chosen q pfx:List Bool) :
    (lookupDone ids chosen q pfx).data output=SemiprimeSourceHistogramPrefix.expected ids (bitValue q) :=by
  change (if bitValue q < ids.length then _ else [])=_
  by_cases h:bitValue q < ids.length
  · simp only [h,ite_true]
  · simp only [h,ite_false]
    exact (expected_outside ids _ (by omega)).symm
/-- Presence is a physically acquired separate singleton; fixed zero remains present even with empty ID output. -/
theorem lookup_found_original (ids:List (List Bool)) (chosen q pfx:List Bool) :
    (lookupDone ids chosen q pfx).data (aux .found)=[decide (bitValue q < ids.length)] :=rfl
/-- Actual output agrees with the ORIGINAL finite environment read, normalized by paid literal instructions. -/
theorem lookup_readFixed (ids:List (List Bool)) (chosen q pfx:List Bool) :
    (lookupDone ids chosen q pfx).data output=
      normalize (SemiprimeSourceWordIdEnvironment.readFixed [] ids q).value :=by
  rw [lookup_output_original,readFixed_original]
/-- Numeric interpretation of the actual candidate ID is EXACToriginal finite-prefix/default lookup, padding included. -/
theorem lookup_value_original (ids:List (List Bool)) (chosen q pfx:List Bool) :
    bitValue ((lookupDone ids chosen q pfx).data output)=
      bitValue (SemiprimeSourceWordIdEnvironment.readFixed [] ids q).value :=by
  rw [lookup_readFixed,normalize_value]
/-- Prefix dictionary/query/current counter/selected input all survive the actual preserving lookup. -/
theorem lookup_retained (ids:List (List Bool)) (chosen q pfx:List Bool) :
    (lookupDone ids chosen q pfx).data (aux .dictionary)=dictionary ids ∧
    (lookupDone ids chosen q pfx).data (aux .nextKey)=variableKey ids.length ∧
    (lookupDone ids chosen q pfx).data (aux .chosenID)=chosen ∧
    (lookupDone ids chosen q pfx).data query=q ∧
    (lookupDone ids chosen q pfx).data (aux .prefix)=pfx :=⟨rfl,rfl,rfl,rfl,rfl⟩
/-- The original concrete candidate-bank decoder observes numeric IDs and therefore preserves paid normalization. -/
theorem decode_normalize (r Q:Nat) [NeZero r] (id:List Bool) :
    SemiprimeSourceWordBankSemantics.decode r Q (normalize id)=SemiprimeSourceWordBankSemantics.decode r Q id :=by
  unfold SemiprimeSourceWordBankSemantics.decode
  rw [normalize_value]
/-- Original default/reverse-prefix word environment is solely a proof interpretation of the actual selected IDs. -/
def originalEnvironment (r Q:Nat) [NeZero r] (ids:List (List Bool)) :
    SemiprimeMaterializedScoreEnvironment.Environment r Q :=
  SemiprimeMaterializedScoreEnvironment.baseEnvironment (SemiprimeSourceWordBankSemantics.decode r Q [])
    (ids.map (SemiprimeSourceWordBankSemantics.decode r Q))
/-- Actual source-produced candidate bytes decode to EXACToriginal environment read; no original getter executes. -/
theorem lookup_decode_original (r Q:Nat) [NeZero r] (ids:List (List Bool)) (chosen q pfx:List Bool) :
    SemiprimeSourceWordBankSemantics.decode r Q ((lookupDone ids chosen q pfx).data output)=
      SemiprimeMaterializedScoreEnvironment.wordAt
        (SemiprimeMaterializedScoreEnvironment.readEnv (originalEnvironment r Q ids) (bitValue q)).value :=by
  rw [lookup_readFixed,decode_normalize]
  have h:=SemiprimeSourceWordIdEnvironment.read_decode (SemiprimeSourceWordBankSemantics.decode r Q)
    ⟨[],ids,[]⟩ q
  simpa only [SemiprimeSourceWordIdEnvironment.read,SemiprimeSourceWordIdEnvironment.readOverrides,
    SemiprimeSourceWordIdEnvironment.decodeEnvironment,originalEnvironment,
    SemiprimeMaterializedScoreEnvironment.baseEnvironment,List.map_map,List.map_nil,Function.comp_def] using h.symm
/-- Exact free mask for original valid endpoint keys, with actual prefix count and actual remaining interval. -/
theorem lookup_free_original (ids:List (List Bool)) (chosen q pfx:List Bool) (N:Nat)
    (hk:ids.length≤N) (hq:bitValue q < N) :
    (lookupDone ids chosen q pfx).data (aux .found)=[false]↔
      bitValue q∈List.range' ids.length (N-ids.length) :=by
  rw [lookup_found_original]
  simp only [List.cons.injEq,and_true,decide_eq_false_iff_not]
  constructor
  · intro h
    apply List.mem_range'.mpr
    exact ⟨bitValue q-ids.length,by omega,by omega⟩
  · intro h
    have he:=List.mem_range'.mp h
    omega
/-- Complete actual prefix source, exact original dictionary/count and retained input, with one own physical-byte clock. -/
theorem source_original (ids:List (List Bool)) :
    ∃t≤2000*((vectorBits ids).length+1)^2,
      SemiprimeD1StackCalls.run program t (initial (vectorBits ids))=some (done ids) ∧
      (done ids).data (aux .dictionary)=L.records (prefixRows ids) [] ∧
      bitValue ((done ids).data (aux .nextKey))=ids.length ∧
      (done ids).data (aux .prefix)=vectorBits ids :=by
  obtain ⟨t,ht,hr⟩:=source_run_bounded ids
  exact ⟨t,ht,hr,dictionary_original ids,nextKey_value ids,prefix_retained ids⟩
/-- Same actual preserving-lookup source and exact original default/prefix ID and physically distinct presence. -/
theorem lookup_original (ids:List (List Bool)) (chosen q pfx:List Bool) :
    ∃t≤201*(cacheSize ids chosen q pfx)^2,
      SemiprimeD1StackCalls.run program t (lookupReady ids chosen q pfx)=some (lookupDone ids chosen q pfx) ∧
      (lookupDone ids chosen q pfx).data output=SemiprimeSourceHistogramPrefix.expected ids (bitValue q) ∧
      (lookupDone ids chosen q pfx).data (aux .found)=[decide (bitValue q < ids.length)] :=by
  obtain ⟨t,ht,hr⟩:=lookup_run_bounded ids chosen q pfx
  exact ⟨t,ht,hr,lookup_output_original ids chosen q pfx,lookup_found_original ids chosen q pfx⟩
end RiemannGaussian.SemiprimeD1StackSourceEnvironmentOriginal

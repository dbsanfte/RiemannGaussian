/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceTerm
/-! # Actual occurrence/cache/power byte bounds for the literal query clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceBytes
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidenceEdges SemiprimeD1StackSourceIncidenceTerm
open SemiprimeD1StackSourceIncidenceSpec (readID)
namespace L
export SemiprimeD1StackOwnerLookup (records result)
end L
namespace Env
export SemiprimeD1StackSourceEnvironmentEncoding (dictionary prefixRows)
end Env
/-- An actual returned first-match payload is a physically framed subword of the retained dictionary. -/
theorem lookup_value_length (q:List Bool) (rows:List (List Bool×List Bool)) :
    (L.result q rows []).1.length ≤ (L.records rows []).length :=by
  induction rows with
  | nil=>simp only [L.result,L.records,List.length_nil,List.length_cons];omega
  | cons row rows ih=>
    rcases row with ⟨key,value⟩
    have ht:(L.records rows []).length ≤ (L.records ((key,value)::rows) []).length:=by
      simp only [L.records,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
      omega
    have hv:value.length ≤ (L.records ((key,value)::rows) []).length:=by
      simp only [L.records,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
      omega
    simp only [L.result]
    split
    · exact hv
    · exact ih.trans ht
/-- Every actual decoded fixed ID is bounded by its physically acquired marked dictionary, including missing/default zero. -/
theorem readID_length (ids:List (List Bool)) (q:List Bool) :
    (readID ids q).length ≤ (Env.dictionary ids).length :=by
  have h:=lookup_value_length q (Env.prefixRows ids)
  rw [SemiprimeD1StackSourceEnvironmentMeaning.lookup_prefix] at h
  by_cases hp:SemiprimeBitArithmetic.bitValue q < ids.length
  · simp only [SemiprimeD1StackSourceEnvironmentMeaning.markedRead,hp,ite_true,List.length_cons] at h
    change (readID ids q).length+1 ≤ (Env.dictionary ids).length at h
    omega
  · have hz:=SemiprimeD1StackSourceEnvironmentOriginal.expected_outside ids (SemiprimeBitArithmetic.bitValue q) (by omega)
    change (SemiprimeSourceHistogramPrefix.expected ids (SemiprimeBitArithmetic.bitValue q)).length ≤ _
    rw [hz]
    exact Nat.zero_le _
/-- Every retained source/power/cache byte allowance is part of the ONE actual query input size. -/
theorem basic_bounds (i:Inputs) :
    (tape i).length ≤ inputSize i ∧ (Env.dictionary i.ids).length ≤ inputSize i ∧
    i.square.length+i.cube.length+i.fourth.length ≤ inputSize i ∧ rowWidth i ≤ inputSize i+1 :=by
  unfold inputSize rowWidth SemiprimeD1StackSourceEnvironmentBounds.cacheSize
  omega
/-- Original record multiplicity is paid by actual pair tags, not supplied as a source count. -/
theorem occurrence_count_le (i:Inputs) :i.rows.length ≤ inputSize i :=by
  have ht:=(basic_bounds i).1
  change (L.records i.rows []).length ≤ _ at ht
  rw [SemiprimeD1StackOwnerLookupBounds.records_length] at ht
  simp only [List.length_nil,Nat.add_zero] at ht
  omega
/-- Every parsed pair's two actual field widths are paid by its physical enclosing record tape. -/
theorem record_width_le (row:List Bool×List Bool) (rows:List (List Bool×List Bool)) (h:row∈rows) :
    row.1.length+row.2.length ≤ (L.records rows []).length :=by
  induction rows with
  | nil=>cases h
  | cons entry rows ih=>
    rcases entry with ⟨key,value⟩
    have ht:(L.records rows []).length ≤ (L.records ((key,value)::rows) []).length:=by
      simp only [L.records,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
      omega
    rcases List.mem_cons.mp h with he|he
    · subst row
      simp only [L.records,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
      omega
    · exact (ih he).trans ht
/-- Every actual original stream endpoint has a width charged to the input source. -/
theorem endpoint_widths (i:Inputs) (row:List Bool×List Bool) (h:row∈i.rows) :
    row.1.length ≤ inputSize i ∧ row.2.length ≤ inputSize i :=by
  have hr:=record_width_le row i.rows h
  have ht:=(basic_bounds i).1
  change (L.records i.rows []).length ≤ _ at ht
  omega
/-- Uniform own classifier clock follows actual key/cache/ID bytes; no original report clock is used. -/
theorem edgeClock_le (i:Inputs) (left right:List Bool) (hl:left.length ≤ inputSize i) (hr:right.length ≤ inputSize i) :
    edgeClock i.ids left right ≤ 10000*(inputSize i)^2 :=by
  have hD:=(basic_bounds i).2.1
  have hL:=(readID_length i.ids left).trans hD
  have hR:=(readID_length i.ids right).trans hD
  have hS:=inputSize_pos i
  have hm:=Nat.mul_le_mul (show left.length+right.length+2 ≤ 2*inputSize i+2 by omega)
    (show (Env.dictionary i.ids).length+1 ≤ inputSize i+1 by omega)
  unfold edgeClock
  nlinarith only [hm,hL,hR,hl,hr,hS]
/-- Actual two-edge selection is uniformly quadratic in acquired physical input bytes. -/
theorem termClock_le (i:Inputs) (lo lf ro rf:List Bool)
    (hlo:lo.length ≤ inputSize i) (hlf:lf.length ≤ inputSize i)
    (hro:ro.length ≤ inputSize i) (hrf:rf.length ≤ inputSize i) :
    termClock i lo lf ro rf ≤ 30000*(inputSize i)^2 :=by
  have h0:=edgeClock_le i lo ro hlo hro
  have h1:=edgeClock_le i lf rf hlf hrf
  have hp:=(basic_bounds i).2.2.1
  have hS:=inputSize_pos i
  unfold termClock
  nlinarith only [h0,h1,hp,hS]
end RiemannGaussian.SemiprimeD1StackSourceIncidenceBytes

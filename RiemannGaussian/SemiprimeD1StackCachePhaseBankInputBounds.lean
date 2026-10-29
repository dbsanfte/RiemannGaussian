/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankEncoding
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedBounds
/-! # Real four-input bytes pay every actual phase call and stopped word
All lengths come from actual source words or SAMEprogram source executions.
Neither native report clocks nor recursive child runtimes enter the bounds.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankInputBounds
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankEncoding
namespace X
export SemiprimeD1StackCachePhaseRootOriginal (rootSource_eq rootSize_eq root_source_run)
end X
namespace A
export SemiprimeD1StackFreshBankRestoreOriginal (banks ordinal)
end A
namespace V
export SemiprimeD1StackRecoveryEntriesIndexedBounds (member_length)
end V
attribute [local irreducible] SemiprimeD1StackRootPhaseFreshRecordsEncoding.result
  SemiprimeD1StackFreshBankRestoreOriginal.banks
  SemiprimeD1StackRootPhaseParametersEncoding.phases
  SemiprimeD1StackRootPhaseParametersEncoding.exponentValue
  SemiprimeD1StackRootPhaseParametersEncoding.levelsValue
  SemiprimeD1StackRootPhaseParametersEncoding.edgeValue
/-- Exactly the four actually supplied runtime words; no count, phase or resource answer is initialized. -/
def resource (bits:List Bool) (requests:List (Request bits)):Nat:=
  (R.result bits R.heap).length+(R.result bits (R.aux .counter)).length+
    (references bits requests).length+(children requests).length
/-- One fixed additive slack for the actual source's own plus-one input conventions. -/
def capacity (bits:List Bool) (requests:List (Request bits)):Nat:=resource bits requests+2
/-- Actual source-field width follows its actual encoded issued-reference vector. -/
theorem reference_length (bits:List Bool) (requests:List (Request bits)) (r:Request bits) (hr:r∈requests):
    (SemiprimeD1StackFreshBankRestoreOriginal.reference bits r.1).length ≤(references bits requests).length:=
  V.member_length _ _ (List.mem_map.mpr ⟨r,hr,rfl⟩)
/-- Actual phase child tape width follows its actual outer source vector, independently of a child runtime. -/
theorem child_length (bits:List Bool) (requests:List (Request bits)) (r:Request bits) (hr:r∈requests):
    (SemiprimeD1StackJetFoldWords.modeTape r.2).length ≤(children requests).length:=
  V.member_length _ _ (List.mem_map.mpr ⟨r,hr,rfl⟩)
/-- Number of actual phase calls is paid by actual source constructors, with no supplied loop count. -/
theorem request_count (bits:List Bool) (requests:List (Request bits)):requests.length ≤(references bits requests).length:=by
  have h:=SemiprimeD1TensorTapeCodec.vectorBits_length (requests.map (fun r=>SemiprimeD1StackFreshBankRestoreOriginal.reference bits r.1))
  simp only [List.length_map] at h
  unfold references
  omega
/-- The same physical heap/counter/reference/children input words pay each actual callee input size. -/
theorem component_size (bits:List Bool) (requests:List (Request bits)) (r:Request bits) (hr:r∈requests):
    O.rootSize bits r.1 r.2+1 ≤capacity bits requests:=by
  have h0:=reference_length bits requests r hr
  have h1:=child_length bits requests r hr
  unfold O.rootSize capacity resource
  omega
/-- Every initialized238-role word is bounded by its actual four physical input lengths. -/
theorem initial_word (bits:List Bool) (r:Request bits) (k:P.Stack):
    ((O.rootSource bits r.1 r.2).data k).length ≤O.rootSize bits r.1 r.2:=by
  have h:=SemiprimeD1StackCachePhaseStorage.initial_role_bound (A.banks bits) (A.ordinal bits r.1) r.2 k
  rw [←X.rootSource_eq bits r.1 r.2,←X.rootSize_eq bits r.1 r.2] at h
  exact h
/-- SAME actual callee source trace bounds every actually retained stopped word, including unused shadows. -/
theorem stopped_word (bits:List Bool) (r:Request bits) (k:P.Stack):
    ((O.rootDone bits r.1 r.2).data k).length ≤O.rootSize bits r.1 r.2+
      10^80*(O.rootSize bits r.1 r.2+1)^16:=by
  obtain ⟨t,ht,hr⟩:=X.root_source_run bits r.1 r.2
  have h:=SemiprimeD1StackReturnLink.run_data_bound P.program t (O.rootSize bits r.1 r.2)
    _ _ (initial_word bits r) hr k
  omega
/-- All real per-phase bank words have a fixed bound in the SAME four whole-iterator input lengths. -/
theorem stopped_word_global (bits:List Bool) (requests:List (Request bits)) (r:Request bits) (hr:r∈requests) (k:P.Stack):
    ((O.rootDone bits r.1 r.2).data k).length ≤10^81*(capacity bits requests)^16:=by
  have hs:=component_size bits requests r hr
  have hw:=stopped_word bits r k
  have hp:=Nat.mul_le_mul_left (10^80) (Nat.pow_le_pow_left hs 16)
  have hlin:capacity bits requests ≤(capacity bits requests)^16:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by unfold capacity;omega:1 ≤capacity bits requests) (by decide:1 ≤16)
  norm_num only at hp ⊢
  omega
end RiemannGaussian.SemiprimeD1StackCachePhaseBankInputBounds

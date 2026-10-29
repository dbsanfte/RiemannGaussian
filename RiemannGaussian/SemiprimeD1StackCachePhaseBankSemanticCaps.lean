/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankInputBounds
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateSemanticCaps
/-! # Child-result byte caps use semantic shapes and precision, never subtree clocks
The recursive child producer is still upstream. Its required word invariant
is expressed on actual child words and finite phase/mode/group/rank counts.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankSemanticCaps
open SemiprimeD1StackCachePhaseBankEncoding SemiprimeD1StackCachePhaseBankInputBounds
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackJetFoldWords (Modes modeTape)
namespace B
export SemiprimeD1StackRecoveryCoordinateSemanticCaps (bankByteBound bank_bytes)
end B
/-- Actual four-level child tape bound from phase/mode/group/rank/working-precision counts. -/
def childByteBound (Q M G R P:Nat):Nat:=2*Q*(B.bankByteBound M G R P+1)+1
/-- Per-phase mode tape uses the identical three-level codec, without a context/value oracle. -/
theorem mode_bytes (modes:Modes) (M G R P:Nat) (hm:modes.length ≤M)
    (hg:∀group∈modes,group.length ≤G) (hr:∀group∈modes,∀jet∈group,jet.length ≤R)
    (hp:∀group∈modes,∀jet∈group,∀word∈jet,word.length ≤P):
    (modeTape modes).length ≤B.bankByteBound M G R P:=
  B.bank_bytes modes M G R P hm hg hr hp
/-- Whole actual child input byte bound; P is CHILD working precision, never OLD parent precision. -/
theorem children_bytes (bits:List Bool) (requests:List (Request bits)) (Q M G R P:Nat)
    (hq:requests.length ≤Q) (hm:∀r∈requests,r.2.length ≤M)
    (hg:∀r∈requests,∀group∈r.2,group.length ≤G)
    (hr:∀r∈requests,∀group∈r.2,∀jet∈group,jet.length ≤R)
    (hp:∀r∈requests,∀group∈r.2,∀jet∈group,∀word∈jet,word.length ≤P):
    (children requests).length ≤childByteBound Q M G R P:=by
  apply SemiprimeD1StackRecoveryEntriesChildCaps.vector_length (requests.map (fun r=>modeTape r.2)) Q
    (B.bankByteBound M G R P) (by simpa only [List.length_map] using hq)
  intro word hw
  obtain ⟨r,hrq,rfl⟩:=List.mem_map.mp hw
  exact mode_bytes r.2 M G R P (hm r hrq) (hg r hrq) (hr r hrq) (hp r hrq)
/-- Every original issued reference is bounded by the already allocated phase count. -/
theorem references_bytes (bits:List Bool) (requests:List (Request bits)) (Q:Nat) (hq:requests.length ≤Q):
    (references bits requests).length ≤2*Q*((SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length+1)+1:=by
  apply SemiprimeD1StackRecoveryEntriesChildCaps.vector_length _ Q _
    (by simpa only [List.length_map] using hq)
  intro word hw
  obtain ⟨r,_,rfl⟩:=List.mem_map.mp hw
  rw [SemiprimeD1StackFreshBankRestoreOriginal.reference_eq,List.length_replicate]
  exact Nat.le_of_lt r.1.isLt
/-- Explicit four-input semantic envelope: heap/counter source bytes plus finite counts and child precision.
No recursive child's execution time appears in this original-input substitution. -/
theorem resource_bytes (bits:List Bool) (requests:List (Request bits)) (Q M G R P:Nat)
    (hq:requests.length ≤Q) (hm:∀r∈requests,r.2.length ≤M)
    (hg:∀r∈requests,∀group∈r.2,group.length ≤G)
    (hr:∀r∈requests,∀group∈r.2,∀jet∈group,jet.length ≤R)
    (hp:∀r∈requests,∀group∈r.2,∀jet∈group,∀word∈jet,word.length ≤P):
    resource bits requests ≤(SemiprimeD1StackCachePhaseBankEncoding.R.result bits SemiprimeD1StackCachePhaseBankEncoding.R.heap).length+
      (SemiprimeD1StackCachePhaseBankEncoding.R.result bits (SemiprimeD1StackCachePhaseBankEncoding.R.aux .counter)).length+
      (2*Q*((SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length+1)+1)+childByteBound Q M G R P:=by
  have h0:=references_bytes bits requests Q hq
  have h1:=children_bytes bits requests Q M G R P hq hm hg hr hp
  unfold resource
  omega
end RiemannGaussian.SemiprimeD1StackCachePhaseBankSemanticCaps

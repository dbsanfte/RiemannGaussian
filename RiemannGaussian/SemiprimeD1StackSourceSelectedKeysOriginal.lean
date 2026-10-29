/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysStorage
import RiemannGaussian.SemiprimeD1IncidenceAcquisition
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesOriginal
/-! # Exact original selected joint-key acquisition from the actual complete prefix cache
Native selected IDs, owner functions and lists occur solely in these meanings.
The fixed39-role source reads the already acquired occurrence/cache words and
executes both ID lookups and framing; it neither reruns selection nor produces
frequencies. Caller joins provide the actual63selector/occurrence-source bank.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysOriginal
open SemiprimeD1StackSourceSelectedKeys SemiprimeD1StackSourceSelectedKeysEncoding
open SemiprimeD1StackSourceSelectedKeysBounds
open SemiprimeBitArithmetic (bitValue)
attribute [local irreducible] SemiprimeD1IncidenceSearch.run SemiprimeD1IncidenceAcquisition.acquire
namespace Ports
export SemiprimeSourceHistogramPortKeys (record encodeKey encodeKey_value encodeKey_compact)
export SemiprimeD1CollisionOriginal (ports)
end Ports
namespace Keys
export SemiprimeSourceHistogramHeadRefinement (numberKey numberKey_value numberKey_compact)
end Keys
/-- Every actual acquired environment word, including arbitrary caller query/chosen/prefix/nextKey, is retained EXACTLY. -/
theorem environment_preserved (i:Inputs) (k:SemiprimeD1StackSourceEnvironment.Stack) :
    (done i).data (environmentStack k)=environment i k :=rfl
/-- The original ordered physical occurrence tape is retained without replay or mutation. -/
theorem occurrences_retained (i:Inputs) :(done i).data (aux .source)=tape i :=rfl
/-- The actual output is exactly the forward key vector, with one entry per physical occurrence and all repetitions. -/
theorem output_keys (i:Inputs) :(done i).data (aux .output)=SemiprimeD1TensorTapeCodec.vectorBits (keys i.ids i.rows) :=rfl
/-- All12 private parser/ID/framing/log/query-save words are genuinely empty after the source. -/
theorem work_clear (i:Inputs) (k:Aux) (hk:k≠.source ∧ k≠.output) :(done i).data (aux k)=[] :=by
  cases k <;> first | rfl | exact (hk.1 rfl).elim | exact (hk.2 rfl).elim
/-- Mathematical original port list supplies the exact original compact owner/factor-key bytes in factor-major order. -/
def originalPairs (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n) :List (List Bool×List Bool) :=
  (Ports.ports n F a arity).map (fun p=>((Ports.record owner p).value.ownerKey,(Ports.record owner p).value.factorKey))
/-- Original code-key acquisition is literally the same canonical namespace bytes emitted by the physical occurrence source. -/
theorem encoded_key (k:Nat) :(Ports.encodeKey k).bits=Keys.numberKey k :=by
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ (Ports.encodeKey_compact k) (Keys.numberKey_compact k)
  rw [Ports.encodeKey_value,Keys.numberKey_value]
/-- Exact original physical namespace/order interface, suitable for the source-occurrence/selector binding. -/
theorem canonical_namespace (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n) :
    originalPairs n F a arity owner=(Ports.ports n F a arity).map
      (fun p=>(Keys.numberKey (owner p).val,Keys.numberKey (n+p.1.val))) :=by
  apply List.map_congr_left
  intro p _
  change ((Ports.encodeKey (owner p).val).bits,(Ports.encodeKey (n+p.1.val)).bits)=_
  rw [encoded_key,encoded_key]
/-- Proof interpretation of the actual complete selected cache and original occurrence source, with arbitrary retained caller words. -/
def originalInput (n F r a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (chosen q pfx:List Bool) :Inputs :=
  ⟨(SemiprimeD1IncidenceSearch.run n F r a arity owner).value,chosen,q,pfx,originalPairs n F a arity owner⟩
/-- Completeness is derived internally from the full original selector's exact n+F length and actual original endpoint ranges. -/
theorem original_complete (n F r a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (chosen q pfx:List Bool) :Complete (originalInput n F r a arity owner chosen q pfx) :=by
  intro row hrow
  obtain ⟨p,_,rfl⟩:=List.mem_map.mp hrow
  have hlen:=SemiprimeD1IncidenceSearch.run_length n F r a arity owner
  change bitValue (Ports.encodeKey (owner p).val).bits < (SemiprimeD1IncidenceSearch.run n F r a arity owner).value.length ∧
    bitValue (Ports.encodeKey (n+p.1.val)).bits < (SemiprimeD1IncidenceSearch.run n F r a arity owner).value.length
  rw [Ports.encodeKey_value,Ports.encodeKey_value,hlen]
  have ho: (owner p).val < n:=(owner p).isLt
  have hf:p.1.val < F:=p.1.isLt
  omega
/-- Exact entire old acquired key list, with no advised key answer or count at any runtime entry. -/
theorem keys_original (n F r a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (chosen q pfx:List Bool) :
    keys (originalInput n F r a arity owner chosen q pfx).ids (originalInput n F r a arity owner chosen q pfx).rows=
      (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys :=by
  rw [SemiprimeD1IncidenceAcquisition.keys_original]
  change ((Ports.ports n F a arity).map (fun p=>((Ports.record owner p).value.ownerKey,(Ports.record owner p).value.factorKey))).map
    (joint (SemiprimeD1IncidenceSearch.run n F r a arity owner).value)=_
  rw [List.map_map]
  apply List.map_congr_left
  intro p _
  exact joint_original (SemiprimeD1IncidenceSearch.run n F r a arity owner).value (Ports.record owner p).value
    (Ports.encodeKey_compact (owner p).val) (Ports.encodeKey_compact (n+p.1.val))
/-- The actual stopped output bytes are precisely the old acquisition keys in its original complete order. -/
theorem output_original (n F r a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (chosen q pfx:List Bool) :
    (done (originalInput n F r a arity owner chosen q pfx)).data (aux .output)=
      SemiprimeD1TensorTapeCodec.vectorBits (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys :=by
  rw [output_keys,keys_original]
/-- Complete actual source, exact oldkey output and all25retained cache words with the SAME own polynomial bit-clock. -/
theorem source_run_original (n F r a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (chosen q pfx:List Bool) :∃t ≤ polynomial (originalInput n F r a arity owner chosen q pfx),
      SemiprimeD1StackCalls.run program t (source (originalInput n F r a arity owner chosen q pfx))=
        some (done (originalInput n F r a arity owner chosen q pfx)) ∧
      (done (originalInput n F r a arity owner chosen q pfx)).data (aux .output)=
        SemiprimeD1TensorTapeCodec.vectorBits (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys ∧
      (∀k,(done (originalInput n F r a arity owner chosen q pfx)).data (environmentStack k)=
        environment (originalInput n F r a arity owner chosen q pfx) k) :=by
  obtain ⟨t,ht,hr⟩:=source_run_bounded (originalInput n F r a arity owner chosen q pfx)
    (original_complete n F r a arity owner chosen q pfx)
  exact ⟨t,ht,hr,output_original n F r a arity owner chosen q pfx,environment_preserved _⟩
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysOriginal

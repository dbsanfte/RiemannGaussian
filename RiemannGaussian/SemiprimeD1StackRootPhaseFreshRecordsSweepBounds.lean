/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsUniform
/-! # Accumulated physical heap, ordinal history and whole chronological sweep clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
set_option exponentiation.threshold 4096
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsSweepBounds
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsRows SemiprimeD1StackRootPhaseFreshRecordsResources
open SemiprimeD1StackRootPhaseFreshRecordsLoop SemiprimeD1StackRootPhaseFreshRecordsUniform
namespace Old
export SemiprimeD1StackRootPhaseParametersResources (references_stream_le stream_length_le heap_bound)
end Old
/-- Actual reference history has its quadratic UNARY-ordinal byte cost. -/
theorem history_bound (n B:Nat) (_hB:1 ≤ B) (hn:n ≤ B) :
    (A.stream (A.references n)).length ≤ 4*B^2 :=by
  have hh: n*(2*n+2) ≤ B*(2*B+2):=Nat.mul_le_mul hn (by omega)
  have h1:B ≤ B^2:=Nat.le_pow (by decide)
  have hp:B*(2*B+2) ≤ 4*B^2:=by nlinarith only [h1]
  exact (Old.references_stream_le n).trans (hh.trans hp)
/-- Every actually read reference byte is paid, including the final vector delimiter. -/
theorem tape_bound {bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool)}
    (es:List (Entry bs)) (B:Nat) (_hB:1 ≤ B) (hlen:es.length ≤ B)
    (hi:∀e∈es,e.1.val ≤ B) :
    (tape es).length ≤ 4*B^2+1 :=by
  have hw:∀w∈es.map (fun e=>List.replicate e.1.val true),w.length ≤ B:=by
    intro w hw
    obtain ⟨e,he,rfl⟩:=List.mem_map.mp hw
    simpa only [List.length_replicate] using hi e he
  have hs:=Old.stream_length_le (es.map (fun e=>List.replicate e.1.val true)) B hw
  rw [List.length_map] at hs
  have hh:es.length*(2*B+2) ≤ B*(2*B+2):=Nat.mul_le_mul_right _ hlen
  have h1:B ≤ B^2:=Nat.le_pow (by decide)
  have hp:B*(2*B+2) ≤ 4*B^2:=by nlinarith only [h1]
  rw [tape,A.rowTape_vector,SemiprimeD1StackRootPhaseParametersEncoding.vector_stream,List.length_append]
  exact Nat.add_le_add_right (hs.trans (hh.trans hp)) 1
/-- The SEPARATE actual output heap grows linearly in cached records and their paid byte widths. -/
theorem heap_bound (prior:List (List Bool)) (B:Nat) (hB:1 ≤ B) (hn:prior.length ≤ B)
    (hw:∀w∈prior,w.length ≤ 10^18*B^2) :
    (SemiprimeD1StackHeapAllocate.heapBytes prior).length ≤ 10^19*B^3 :=by
  have hh:=Old.heap_bound prior (10^18*B^2) hw
  have hm:prior.length*(2*(10^18*B^2)+1) ≤ B*(2*(10^18*B^2)+1):=Nat.mul_le_mul_right _ hn
  have h1:B ≤ B^3:=Nat.le_pow (by decide)
  have he:B*(2*(10^18*B^2)+1)=2*10^18*B^3+B:=by ring
  rw [he] at hm
  exact hh.trans (hm.trans (by omega))
/-- Whole foreach budget charges every physical source/85frame/allocation/145drain
row and every growing counter/heap/history word, without a reported output-size oracle. -/
theorem sweepBound_le (root:R.Stack→List Bool) (bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool))
    (a u edges:Nat) (es:List (Entry bs)) (prior:List (List Bool)) (B:Nat)
    (hB:1 ≤ B) (hroot:∀k,(root k).length ≤ B)
    (hh:root R.heap=E.heap bs) (hc:root (R.aux .counter)=List.replicate bs.length true)
    (hb:∀e∈es,bs[e.1.val]=SemiprimeD1StackPhaseCacheFreshComponents.phase a u edges e.2 [false,true])
    (hresource:∀e∈es,SemiprimeD1StackPhaseCacheFreshBounds.resource bs e.1 a u edges e.2 [false,true] [] ≤ B)
    (hi:∀e∈es,e.1.val ≤ B) (hn:prior.length+es.length ≤ B)
    (hw:∀w∈prior,w.length ≤ 10^18*B^2) :
    sweepBound root bs a u edges es prior ≤ es.length*(10^28*B^3)+1 :=by
  induction es generalizing prior with
  | nil=>simp only [sweepBound,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons e rest ih=>
    have he: e∈e::rest:=List.mem_cons_self
    have hrw:=row_record bs e.1 a u edges e.2 B hB (hresource e he) (hb e he)
    have htail:rest.length ≤ B:=by simp only [List.length_cons] at hn;omega
    have hprior:prior.length ≤ B:=by omega
    have hrestIndex:∀x∈rest,x.1.val ≤ B:=fun x hx=>hi x (List.mem_cons_of_mem _ hx)
    have hrow:=rowBound_le root bs e.1 a u edges e.2 (tape rest)
      (SemiprimeD1StackHeapAllocate.heapBytes prior) prior.length (A.stream (A.references prior.length)).reverse B
      hB hroot hh hc (hb e he) (hresource e he) (hi e he) hprior
      (tape_bound rest B hB htail hrestIndex) (heap_bound prior B hB hprior hw)
      (by rw [List.length_reverse];exact history_bound prior.length B hB hprior)
    have hn':(prior++[record a u edges e.2]).length+rest.length ≤ B:=by
      simp only [List.length_append,List.length_cons,List.length_nil] at hn ⊢
      omega
    have hw':∀w∈prior++[record a u edges e.2],w.length ≤ 10^18*B^2:=by
      intro w hm
      rcases List.mem_append.mp hm with h|h
      · exact hw w h
      · have heq:w=record a u edges e.2:=List.mem_singleton.mp h
        subst w
        exact hrw
    have ht:=ih (prior++[record a u edges e.2]) (fun x hx=>hb x (List.mem_cons_of_mem _ hx))
      (fun x hx=>hresource x (List.mem_cons_of_mem _ hx)) hrestIndex hn' hw'
    change rowBound _ _ _ _ _ _ _ _ _ _ _+sweepBound _ _ _ _ _ _ _ ≤ _
    simp only [List.length_cons]
    nlinarith only [hrow,ht]
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsSweepBounds

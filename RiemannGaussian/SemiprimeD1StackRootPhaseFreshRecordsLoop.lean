/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsRows
/-! # Actual chronological issued-reference sweep, with no source replay -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsLoop
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsRows SemiprimeD1StackRootPhaseFreshRecordsPrimitives
open SemiprimeD1StackRootPhaseFreshRecordsView SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace A
export SemiprimeD1StackRootPhaseParametersEncoding (stream references references_succ stream_append)
export SemiprimeD1StackRootPhaseParametersLoop (rowTape rowTape_vector)
end A
/-- Proof-side indexed phase list; indices identify literal issued words, not runtime getters. -/
abbrev Entry (bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool)) :=Fin bs.length×List Bool
/-- Literal actual issued-reference bytes in the original producer order. -/
def tape {bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool)} (es:List (Entry bs)) :List Bool :=
  A.rowTape (es.map (fun e=>List.replicate e.1.val true)) [false]
/-- One exact full85-word record per phase, including false/rejected phase banks. -/
def cached {bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool)} (a u edges:Nat) (es:List (Entry bs)) :List (List Bool) :=
  es.map (fun e=>record a u edges e.2)
/-- Chronological stable ordinal log advances after every real heap allocation. -/
theorem nextHistory_references (n:Nat) :
    nextHistory n (A.stream (A.references n)).reverse=(A.stream (A.references (n+1))).reverse :=by
  rw [A.references_succ,A.stream_append,List.reverse_append]
  rfl
/-- Recursive budget contains the SAME executed row clocks and physical accumulated heap/history lengths. -/
def sweepBound (root:R.Stack→List Bool) (bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool))
    (a u edges:Nat) (es:List (Entry bs)) (prior:List (List Bool)) :Nat :=
  match es with
  | []=>1
  | e::rest=>rowBound root bs e.1 a u edges e.2 (tape rest)
      (SemiprimeD1StackHeapAllocate.heapBytes prior) prior.length (A.stream (A.references prior.length)).reverse+
      sweepBound root bs a u edges rest (prior++[record a u edges e.2])
/-- The final actual vector sentinel is physically removed before output reversal. -/
theorem header_end (root:R.Stack→List Bool) (hp:List Bool) (n:Nat) (hist:List Bool) :
    Runs program 1 .header (loop root [false] hp n hist) .finishSeed (loop root [] hp n hist) :=by
  apply one_base program _ _ (.pop (aux .reader) .finishSeed .finishSeed .parse) _ _ rfl
  · rfl
  · exact update_reader _ _ _ _ _ _ _ _ _ _
/-- Whole literal pointer sweep dereferences exactly once per actual issued row,
preserves all188 source cells and allocates complete Fresh caches in original order. -/
theorem rows_run (root:R.Stack→List Bool) (bs:List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool))
    (a u edges:Nat) (es:List (Entry bs)) (prior:List (List Bool))
    (hh:root R.heap=E.heap bs) (hc:root (R.aux .counter)=List.replicate bs.length true)
    (hb:∀e∈es,bs[e.1.val]=SemiprimeD1StackPhaseCacheFreshComponents.phase a u edges e.2 [false,true]) :
    ∃q ≤ sweepBound root bs a u edges es prior,
      Runs program q .header
        (loop root (tape es) (SemiprimeD1StackHeapAllocate.heapBytes prior)
          prior.length (A.stream (A.references prior.length)).reverse) .finishSeed
        (loop root [] (SemiprimeD1StackHeapAllocate.heapBytes (prior++cached a u edges es))
          (prior++cached a u edges es).length (A.stream (A.references (prior++cached a u edges es).length)).reverse) :=by
  induction es generalizing prior with
  | nil=>
    refine ⟨1,by rfl,?_⟩
    simpa only [cached,List.map_nil,List.append_nil,tape,A.rowTape,List.foldr_nil] using
      header_end root (SemiprimeD1StackHeapAllocate.heapBytes prior) prior.length
        (A.stream (A.references prior.length)).reverse
  | cons e rest ih=>
    obtain ⟨r,hr,h0⟩:=row_run root bs e.1 a u edges e.2 (tape rest)
      (SemiprimeD1StackHeapAllocate.heapBytes prior) prior.length (A.stream (A.references prior.length)).reverse hh hc
      (hb e (List.mem_cons_self))
    obtain ⟨s,hs,h1⟩:=ih (prior++[record a u edges e.2]) (fun x hx=>hb x (List.mem_cons_of_mem _ hx))
    have hheap:SemiprimeD1StackHeapAllocate.heapBytes (prior++[record a u edges e.2])=
        frame (record a u edges e.2) (SemiprimeD1StackHeapAllocate.heapBytes prior):=
      SemiprimeD1StackHeapAllocate.heapBytes_append prior (record a u edges e.2)
    have hlen:(prior++[record a u edges e.2]).length=prior.length+1:=by
      simp only [List.length_append,List.length_singleton]
    rw [nextHistory_references] at h0
    rw [hheap,hlen] at h1
    have he:(prior++[record a u edges e.2])++cached a u edges rest=prior++cached a u edges (e::rest):=by
      simp only [cached,List.map_cons,List.append_assoc,List.singleton_append]
    rw [he] at h1
    refine ⟨r+s,?_,?_⟩
    · change r+s ≤ rowBound _ _ _ _ _ _ _ _ _ _ _+sweepBound _ _ _ _ _ _ _
      omega
    · exact compose h0 h1
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsLoop

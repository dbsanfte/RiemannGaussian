/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersRows
/-! # Whole chronological phase loop, including rejected stopped banks -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersLoop
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackRootPhaseParametersPrimitives SemiprimeD1StackRootPhaseParametersRows
open SemiprimeD1StackRootPhaseParametersView SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual acquired vector bytes, allowing the physically empty inactive grid. -/
def rowTape (rows:List (List Bool)) (terminal:List Bool) : List Bool :=
  rows.foldr (fun word tail=>true::frame word tail) terminal
/-- Physical row tape is the actual unmarked row stream followed by its terminator. -/
theorem rowTape_eq (rows:List (List Bool)) (terminal:List Bool) : rowTape rows terminal=stream rows++terminal :=by
  induction rows with
  | nil=>rfl
  | cons word rows ih=>
    change true::frame word (rowTape rows terminal)=(true::frame word (stream rows))++terminal
    rw [ih,List.cons_append,SemiprimeD1TensorTapeCodec.frame_append]
/-- The active source uses the ordinary exact vector grammar. -/
theorem rowTape_vector (rows:List (List Bool)) : rowTape rows [false]=SemiprimeD1TensorTapeCodec.vectorBits rows :=by
  rw [rowTape_eq,vector_stream]
/-- One actual acquired counter reference advances the chronological reference list. -/
theorem nextHistory_references (n:Nat) :
    nextHistory n (stream (references n)).reverse=(stream (references (n+1))).reverse :=by
  rw [references_succ,stream_append,List.reverse_append]
  rfl
/-- Whole same-program recursive trace budget; this specification counts the
actual parsed row sources, allocator scans and full188-role cleanup mass. -/
def sweepBound (root:G.Stack→List Bool) (a u edges:Nat)
    (rows cached:List (List Bool)) (terminal:List Bool) : Nat :=
  match rows with
  | []=>1
  | t::ts=>rowBound root a u edges t (rowTape ts terminal) (SemiprimeD1StackHeapAllocate.heapBytes cached)
      cached.length (stream (references cached.length)).reverse+
      sweepBound root a u edges ts (cached++[record a u edges t]) terminal
/-- Empty and false-terminated actual acquired grids both perform one real pop. -/
theorem header_end (root:G.Stack→List Bool) (hp:List Bool) (n:Nat) (hist terminal:List Bool)
    (ht:terminal=[] ∨ terminal=[false]) :
    Runs program 1 .header (loop root terminal hp n hist) .finishSeed (loop root [] hp n hist) :=by
  rcases ht with rfl|rfl
  · apply one_base program _ _ (.pop (aux .reader) .finishSeed .finishSeed .parse) _ _ rfl
    · rfl
    · exact update_reader _ _ _ _ _ _ _ _ _ _ _
  · apply one_base program _ _ (.pop (aux .reader) .finishSeed .finishSeed .parse) _ _ rfl
    · rfl
    · exact update_reader _ _ _ _ _ _ _ _ _ _ _
/-- Actual complete phase-list sweep allocates one entire stopped bank per phase
in the original order, including rejected P/D-empty banks, with stable ordinal history. -/
theorem rows_run (root:G.Stack→List Bool) (a u edges:Nat) (rows cached:List (List Bool))
    (terminal:List Bool) (ht:terminal=[] ∨ terminal=[false])
    (ha:root G.exponent=List.replicate a true)
    (hu:root (G.rootStack (SemiprimeD1StackRootRecursiveControl.sourceStack SemiprimeD1StackRootParameters.levels))=List.replicate u true)
    (hm:root (G.rootStack (SemiprimeD1StackRootRecursiveControl.sourceStack SemiprimeD1StackRootParameters.edges))=List.replicate edges true) :
    ∃q≤ sweepBound root a u edges rows cached terminal,
      Runs program q .header
        (loop root (rowTape rows terminal) (SemiprimeD1StackHeapAllocate.heapBytes cached)
          cached.length (stream (references cached.length)).reverse)
        .finishSeed
        (loop root [] (SemiprimeD1StackHeapAllocate.heapBytes (cached++records a u edges rows))
          (cached++records a u edges rows).length (stream (references (cached++records a u edges rows).length)).reverse) :=by
  induction rows generalizing cached with
  | nil=>
    refine ⟨1,by rfl,?_⟩
    simpa only [records,List.map_nil,List.append_nil,rowTape,List.foldr_nil] using
      header_end root (SemiprimeD1StackHeapAllocate.heapBytes cached) cached.length
        (stream (references cached.length)).reverse terminal ht
  | cons t ts ih=>
    obtain ⟨r,hr,h0⟩:=row_run root a u edges t (rowTape ts terminal)
      (SemiprimeD1StackHeapAllocate.heapBytes cached) cached.length (stream (references cached.length)).reverse ha hu hm
    obtain ⟨s,hs,h1⟩:=ih (cached++[record a u edges t])
    have hheap:SemiprimeD1StackHeapAllocate.heapBytes (cached++[record a u edges t])=
        frame (record a u edges t) (SemiprimeD1StackHeapAllocate.heapBytes cached):=
      SemiprimeD1StackHeapAllocate.heapBytes_append cached (record a u edges t)
    have hlen:(cached++[record a u edges t]).length=cached.length+1:=by simp only [List.length_append,List.length_singleton]
    rw [nextHistory_references] at h0
    rw [hheap,hlen] at h1
    have he:(cached++[record a u edges t])++records a u edges ts=cached++records a u edges (t::ts):=by
      simp only [records,List.map_cons,List.append_assoc,List.singleton_append]
    rw [he] at h1
    refine ⟨r+s,by change r+s≤rowBound _ _ _ _ _ _ _ _ _+sweepBound _ _ _ _ _ _ _;omega,compose h0 h1⟩
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersLoop

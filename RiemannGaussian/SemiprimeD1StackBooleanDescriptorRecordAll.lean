/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordReject
/-! # Actual dispatch trace for every original descriptor, including arithmetic
One unchanged finite program handles all eighteen original constructors. Its
proof-side result distinguishes real Boolean row writes from the real skip.
Neither this distinction nor an original typed vertex is executed as an oracle.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordAll
open SemiprimeD1StackBooleanDescriptorRecord SemiprimeD1StackBooleanDescriptorRecordEncoding
open SemiprimeD1StackBooleanDescriptorRecordOriginal (originalMode)
namespace E
export SemiprimeD1EdgeCatalogueEncoding (vertex)
end E
/-- Proof-only actual record substore after the parsed finite constructor branch. -/
def recordResult {r t digits : Nat} (v : SemiprimeMacroGraph.SubdividedVertex r t digits)
    (scope : List (List Bool)) (hist out : List Bool) : R.Stack→List Bool :=
  match originalMode v with
  | none=>recordInput (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out
  | some mode=>(R.done mode scope hist out).data
/-- Actual canonical halt store of the same unchanged descriptor program. -/
def done {r t digits : Nat} (v : SemiprimeMacroGraph.SubdividedVertex r t digits) (tail : List Bool)
    (scope : List (List Bool)) (hist out : List Bool) : C.State Stack Label :=
  ⟨none,none,none,clean (recordResult v scope hist out) (E.vertex v) tail,[]⟩
/-- Uniform descriptor and actual binary-scope cost allowance across all18 tags. -/
def rowBound (w : Record) (scope : List (List Bool)) (M : Nat) : Nat :=
  110*(scope.length+1)*(M+1)+7*(record w []).length+222
/-- Every original descriptor executes its actual parse/dispatch/record-or-skip
trace with an own byte bound. No finite-mode premise or supplied branch remains. -/
theorem source_run (N : Nat) (hN : 0<N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (tail : List Bool) (scope : List (List Bool)) (hist out : List Bool) (M : Nat)
    (hl:∀s∈scope,s.length ≤ M) (hv:∀s∈scope,SemiprimeBitArithmetic.bitValue s ≤ M) :
    ∃t ≤ rowBound (E.vertex v) scope M,
      C.run program t
        (initial (SemiprimeD1VertexCatalogueEncoding.vertex v tail)
          (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out)=some (done v tail scope hist out) := by
  cases hm:originalMode v with
  | none=>
    cases v with
    | inr signal=>cases hm
    | inl arithmetic=>
      obtain ⟨code,hcode,htag⟩:=SemiprimeD1StackBooleanDescriptorRecordReject.arithmetic_tag arithmetic hm
      let w:=E.vertex (.inl arithmetic)
      have hr:=SemiprimeD1StackBooleanDescriptorRecordReject.rejected_run code hcode w htag
        (recordInput (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out) tail
      have ht:=tag_length_le_mass w
      change w 0=List.replicate code.val true at htag
      rw [htag,List.length_replicate] at ht
      refine ⟨8*mass w+6*code.val+46,?_,?_⟩
      · change 8*mass w+6*code.val+46 ≤ rowBound w scope M
        unfold rowBound
        rw [record_length]
        simp only [List.length_nil]
        omega
      · simpa only [w,initial,done,recordResult,hm,record_vertex] using hr
  | some mode=>
    obtain ⟨code,htag,hd,_⟩:=SemiprimeD1StackBooleanDescriptorRecordOriginal.original_dispatch N hN v mode hm
    obtain ⟨t,ht,hr⟩:=SemiprimeD1StackBooleanDescriptorRecordExecution.source_run code (E.vertex v) tail mode
      htag hd scope hist out
    have hb:=SemiprimeD1StackBooleanDescriptorRecordBounds.timeBound_le code (E.vertex v) mode scope M htag hl hv
    refine ⟨t,ht.trans hb,?_⟩
    simpa only [SemiprimeD1StackBooleanDescriptorRecordExecution.done,done,recordResult,hm,record_vertex] using hr
/-- Actual reverse-history bytes after one physical descriptor branch. -/
def afterHistory {r t digits : Nat} (v : SemiprimeMacroGraph.SubdividedVertex r t digits)
    (scope : List (List Bool)) (hist : List Bool) : List Bool :=
  match originalMode v with
  | none=>hist
  | some mode=>(SemiprimeD1StackBooleanRecord.R.row (SemiprimeD1StackBooleanRecord.S.result scope)
      (SemiprimeD1StackBooleanRecord.table mode)).reverse++hist
/-- The actual record program clears every table/conversion/work role, retaining
only its input bank and real history/output accumulators. -/
theorem record_done_initial (mode : SemiprimeD1StackBooleanEntry.Mode)
    (scope : List (List Bool)) (hist out : List Bool) :
    (R.done mode scope hist out).data=
      recordInput (SemiprimeD1TensorTapeCodec.vectorBits scope)
        ((SemiprimeD1StackBooleanRecord.R.row (SemiprimeD1StackBooleanRecord.S.result scope)
          (SemiprimeD1StackBooleanRecord.table mode)).reverse++hist) out := by
  funext k
  rcases k with k|k|k
  · cases k;rfl
  · cases k <;> rfl
  · cases k <;> rfl
/-- Uniform clean-record invariant across all eighteen real dispatch branches. -/
theorem recordResult_initial {r t digits : Nat} (v : SemiprimeMacroGraph.SubdividedVertex r t digits)
    (scope : List (List Bool)) (hist out : List Bool) :
    recordResult v scope hist out=
      recordInput (SemiprimeD1TensorTapeCodec.vectorBits scope) (afterHistory v scope hist) out := by
  cases h:originalMode v with
  | none=>simp only [recordResult,afterHistory,h]
  | some mode=>simpa only [recordResult,afterHistory,h] using record_done_initial mode scope hist out
end RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordAll

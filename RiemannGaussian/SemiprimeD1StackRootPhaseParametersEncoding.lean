/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParameters
/-! # Exact complete phase records, physical heap layout and chronological references -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackRootPhaseParameters
open SemiprimeSourceHistogramKeyBits (frame)
/-- Complete stopped phase bank serialized in one fixed forty-eight-role order. -/
def phaseRecord (bank:P.Stack→List Bool) : List Bool :=I.roles.foldr (fun k tail=>frame (bank k) tail) []
/-- Exact record of the ACTUAL stopped original working-precision source. -/
def record (a u edges:Nat) (t:List Bool) : List Bool :=phaseRecord
  (SemiprimeD1StackPhaseWorkingPrecisionComponents.result a u edges t [false,true])
/-- Logical oldest-first records; physical framing is newest first. -/
def records (a u edges:Nat) (phases:List (List Bool)) : List (List Bool) :=phases.map (record a u edges)
/-- Actual unary stable allocation references in original phase order. -/
def references (n:Nat) : List (List Bool) :=(List.range n).map (fun i=>List.replicate i true)
/-- Vector entries without a terminal marker, used only to state reverse-history effects. -/
def stream (rows:List (List Bool)) : List Bool :=rows.foldr (fun row tail=>true::frame row tail) []
/-- Exact retained new-work view; every unnamed physical scratch word is empty. -/
def work (reader index record heap counter reference history output:List Bool) : Aux→List Bool
  | .reader=>reader | .index=>index | .record=>record | .heap=>heap | .counter=>counter
  | .reference=>reference | .refsHistory=>history | .refsOutput=>output | _=>[]
/-- Complete physical bank at a parsed/cached phase boundary. -/
def view (root:G.Stack→List Bool) (phase:P.Stack→List Bool)
    (reader index record heap counter reference history output:List Bool) : Stack→List Bool :=
  data root phase (work reader index record heap counter reference history output)
/-- Literal phase-loop boundary after all private phase words were drained. -/
def loop (root:G.Stack→List Bool) (reader heap:List Bool) (n:Nat) (history:List Bool) : Stack→List Bool :=
  view root (fun _=>[]) reader [] [] heap (List.replicate n true) [] history []
/-- Complete retained root/grid result before its sole physical reader copy. -/
def afterGrid (bits:List Bool) : Stack→List Bool :=data
  (SemiprimeD1StackRootPhaseGridEncoding.result bits) (fun _=>[]) (fun _=>[])
/-- Exact finished private bank; the source/grid cells survive literally. -/
def finished (root:G.Stack→List Bool) (cached:List (List Bool)) : Stack→List Bool :=
  view root (fun _=>[]) [] [] [] (SemiprimeD1StackHeapAllocate.heapBytes cached)
    (List.replicate cached.length true) [] [] (SemiprimeD1TensorTapeCodec.vectorBits (references cached.length))
/-- Parent exponent acquired by the original root source. -/
def exponentValue (bits:List Bool) : Nat :=SemiprimeD1StackRootPhaseGridEncoding.exponentValue bits
/-- Parent level tally, distinct from the conditional successor's level tally. -/
def levelsValue (bits:List Bool) : Nat :=SemiprimeD1Schedule.levels
  (SemiprimeD1StackRootRecursiveControlEncoding.lambdaValue bits) 0
/-- Actual root occurrence count M=2E. -/
def edgeValue (bits:List Bool) : Nat :=SemiprimeD1StackRootRecursiveControlEncoding.edgeValue bits
/-- Complete original chronological phase list, conditional on the actual source guard. -/
def phases (bits:List Bool) : List (List Bool) :=
  if SemiprimeD1StackRootPhaseGridEncoding.active bits then
    SemiprimeD1StackAssignmentOrder.assignments (2^(exponentValue bits+1))
      (List.replicate (exponentValue bits+1) false) else []
/-- Exact N-only heap and chronological-reference result, including rejected phases. -/
def result (bits:List Bool) : Stack→List Bool :=finished
  (SemiprimeD1StackRootPhaseGridEncoding.result bits)
  (records (exponentValue bits) (levelsValue bits) (edgeValue bits) (phases bits))
/-- Exact whole final halt with clear finite flags and no pending real return cells. -/
def done (bits:List Bool) : C.State Stack Label :=⟨none,none,none,result bits,[]⟩
/-- Literal source preservation at every completed cache boundary. -/
theorem finished_grid (root:G.Stack→List Bool) (cached:List (List Bool)) (k:G.Stack) :
    finished root cached (gridStack k)=root k :=rfl
/-- Physical numeric values are preserved as their exact original words, not normalized. -/
theorem phaseRecord_length (bank:P.Stack→List Bool) :
    (phaseRecord bank).length=(I.roles.map (fun k=>2*(bank k).length+1)).sum :=by
  unfold phaseRecord
  induction I.roles with
  | nil=>rfl
  | cons k ks ih=>simp only [List.foldr_cons,List.map_cons,List.sum_cons,SemiprimeSourceHistogramKeyBits.frame_length,ih];omega
/-- Appending a logical reference prepends precisely its reversed actual vector entry. -/
theorem stream_append (xs ys:List (List Bool)) : stream (xs++ys)=stream xs++stream ys :=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    change true::frame x (stream (xs++ys))=(true::frame x (stream xs))++stream ys
    rw [ih,List.cons_append,SemiprimeD1TensorTapeCodec.frame_append]
/-- Exact reference ordinals advance by one per actual allocation. -/
theorem references_succ (n:Nat) : references (n+1)=references n++[List.replicate n true] :=by
  simp only [references,List.range_succ,List.map_append,List.map_cons,List.map_nil]
/-- Framed vector bytes are the unmarked row stream followed by one false terminal. -/
theorem vector_stream (rows:List (List Bool)) :
    SemiprimeD1TensorTapeCodec.vectorBits rows=stream rows++[false] :=by
  induction rows with
  | nil=>rfl
  | cons x xs ih=>
    simp only [SemiprimeD1TensorTapeCodec.vectorBits,stream,List.foldr_cons,List.cons_append]
    rw [ih,SemiprimeD1TensorTapeCodec.frame_append]
    rfl
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersEncoding

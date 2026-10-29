/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecords
/-! # Actual aliased heap view and complete fresh85 record/cache specification -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecords
namespace Q
export SemiprimeD1StackPhaseCacheFresh (input)
end Q
open SemiprimeSourceHistogramKeyBits (frame)
/-- Exact complete85-word stopped Fresh record, with no vector-constructor tags. -/
def freshRecord (bank:F.Stack→List Bool) :List Bool :=
  SemiprimeD1StackRootPhaseFreshRecordsInventory.roles.foldr (fun k tail=>frame (bank k) tail) []
/-- Actual entire85-role stopped cache, including rejected phases and all empty work fields. -/
def freshResult (a u edges:Nat) (t:List Bool) :F.Stack→List Bool :=
  SemiprimeD1StackPhaseChildContextFreshComponents.result a u edges t [false,true] []
/-- Exact chronological fresh record bytes associated with one actual parsed source phase. -/
def record (a u edges:Nat) (t:List Bool) :List Bool :=freshRecord (freshResult a u edges t)
/-- All actual source P48 bank records in their acquired original chronological order. -/
def phaseBanks (bits:List Bool) :List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool) :=
  (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).map
    (SemiprimeD1StackRootPhaseParametersRows.stopped
      (SemiprimeD1StackRootPhaseParametersEncoding.exponentValue bits)
      (SemiprimeD1StackRootPhaseParametersEncoding.levelsValue bits)
      (SemiprimeD1StackRootPhaseParametersEncoding.edgeValue bits))
/-- Chronological complete fresh-bank record catalogue; mathematical specification only. -/
def records (a u edges:Nat) (rows:List (List Bool)) :List (List Bool) :=rows.map (record a u edges)
/-- Three raw allocated alias-shadows are always empty; they never hold a copied heap. -/
def privateCache (q:Q.Stack→List Bool) (k:Q.Stack) :List Bool :=
  if k=I.sourceHeap ∨ k=I.sourceCounter ∨ k=I.sourceReference then [] else q k
/-- Source heap/counter are the client's SAME actual fields, not private copies. -/
def rootView (root:R.Stack→List Bool) (q:Q.Stack→List Bool) :R.Stack→List Bool
  | .inr (.inr .heap)=>q I.sourceHeap
  | .inr (.inr .counter)=>q I.sourceCounter
  | k=>root k
/-- Current pointer is the client's SAME actual issued-reference field. -/
def auxView (q:Q.Stack→List Bool) (work:Aux→List Bool) :Aux→List Bool
  | .pointer=>q I.sourceReference
  | k=>work k
/-- Complete physical345-role alias-preserving bank view. -/
def view (root:R.Stack→List Bool) (q:Q.Stack→List Bool) (work:Aux→List Bool) :Stack→List Bool :=
  data (rootView root q) (privateCache q) (auxView q work)
/-- Literal row-local and accumulating auxiliary words; unnamed scratch roles are empty. -/
def work (reader currentRecord heap counter reference history output:List Bool) :Aux→List Bool
  | .reader=>reader | .record=>currentRecord | .heap=>heap | .counter=>counter
  | .reference=>reference | .refsHistory=>history | .refsOutput=>output | _=>[]
/-- Actual caller inputs to the cache consumer; heap/count are retained source words. -/
def cacheInput (root:R.Stack→List Bool) (pointer axes:List Bool) :Q.Stack→List Bool :=
  Q.input (root R.heap) (root (R.aux .counter)) pointer axes
/-- Initial pointer-loop boundary, with just the persistent literal empty old-axis header. -/
def loop (root:R.Stack→List Bool) (reader heap:List Bool) (n:Nat) (history:List Bool) :Stack→List Bool :=
  view root (cacheInput root [] [false]) (work reader [] heap (List.replicate n true) [] history [])
/-- All345 fields after the whole original-N phase source returned, before the reader copy. -/
def afterRoot (bits:List Bool) :Stack→List Bool :=data
  (SemiprimeD1StackRootPhaseParametersEncoding.result bits) (fun _=>[]) (fun _=>[])
/-- Exact completed private bank: all reader/client/shadow/work fields empty,
except the retained old-axis header; all188 original source fields are literal. -/
def finished (root:R.Stack→List Bool) (cached:List (List Bool)) :Stack→List Bool :=
  view root (cacheInput root [] [false])
    (work [] [] (SemiprimeD1StackHeapAllocate.heapBytes cached) (List.replicate cached.length true) [] []
      (SemiprimeD1TensorTapeCodec.vectorBits (SemiprimeD1StackRootPhaseParametersEncoding.references cached.length)))
/-- Exact original-N complete fresh-record cache result. -/
def result (bits:List Bool) :Stack→List Bool :=finished
  (SemiprimeD1StackRootPhaseParametersEncoding.result bits)
  (records (SemiprimeD1StackRootPhaseParametersEncoding.exponentValue bits)
    (SemiprimeD1StackRootPhaseParametersEncoding.levelsValue bits)
    (SemiprimeD1StackRootPhaseParametersEncoding.edgeValue bits)
    (SemiprimeD1StackRootPhaseParametersEncoding.phases bits))
/-- Actual completed halt has clear finite read/return flags and no pending return cells. -/
def done (bits:List Bool) :C.State Stack Label :=⟨none,none,none,result bits,[]⟩
/-- Restored heap/counter equality restores the literal complete original source bank. -/
theorem rootView_eq (root:R.Stack→List Bool) (q:Q.Stack→List Bool)
    (hh:q I.sourceHeap=root R.heap) (hc:q I.sourceCounter=root (R.aux .counter)) :rootView root q=root :=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> first | exact hh | exact hc | rfl
/-- Every actual included client operand views EXACTLY its logical current word. -/
theorem view_cache (root:R.Stack→List Bool) (q:Q.Stack→List Bool) (w:Aux→List Bool) (k:Q.Stack) :
    view root q w (cacheStack k)=q k :=by
  rcases k with k|k
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
  · rfl
/-- Entire logical Fresh85 projection views its actual shared/private client fields. -/
theorem view_fresh (root:R.Stack→List Bool) (q:Q.Stack→List Bool) (w:Aux→List Bool) (k:F.Stack) :
    view root q w (freshStack k)=q (Q.freshStack k) :=view_cache _ _ _ _
/-- The source actual heap and counter retain their exact original data at every loop boundary. -/
theorem cacheInput_heap_counter (root:R.Stack→List Bool) (pointer axes:List Bool) :
    cacheInput root pointer axes I.sourceHeap=root R.heap ∧
    cacheInput root pointer axes I.sourceCounter=root (R.aux .counter) :=⟨rfl,rfl⟩
/-- All188 original source cells, including the input phase heap/counter/refs, survive finalization. -/
theorem finished_root (root:R.Stack→List Bool) (cached:List (List Bool)) (k:R.Stack) :
    finished root cached (rootStack k)=root k :=congrFun (rootView_eq root _ rfl rfl) k
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsEncoding

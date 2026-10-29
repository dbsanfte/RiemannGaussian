/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationRow
/-! # Actual EOF-controlled all-old-vertex activation loop
Rows below are proof-side descriptions of fields acquired from the two actual
source words. They are never runtime inputs, control values, or instructions.
The original-source specialization must derive Valid from the retained caches.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationLoop
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryActivation SemiprimeD1StackChildGroupFactoryActivationView
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace RowSource
export SemiprimeD1StackChildGroupFactoryActivationRow (timeBound source_trace)
end RowSource
/-- Description of physically acquired fields, solely for the correctness statement. -/
structure Row where
  /-- ID physically returned after the real present marker. -/
  selected:List Bool
  /-- Actual unread dictionary suffix, which is physically drained. -/
  unread:List Bool
  /-- Actual fields physically produced by the real paired-row source. -/
  colours:List (List Bool)
/-- The actual full-adder output is the loop's next binary key. -/
def advance (key:List Bool):List Bool:=(SemiprimeBitArithmetic.addBits key [true] false).bits
/-- Domain of the actual acquired source words at every visited physical key. -/
def Valid (environment catalogue:List (List Bool×List Bool)) :List Bool→List Row→Prop
  | _,[]=>True
  | key,row::rows=>
    SemiprimeD1StackOwnerLookup.result key environment []=(true::row.selected,row.unread) ∧
    SemiprimeD1StackPacketRowsEncoding.present row.selected catalogue=true ∧
    SemiprimeD1StackPacketRowsAcquire.payload row.selected catalogue=SemiprimeD1PacketRows.serialize row.colours ∧
    Valid environment catalogue (advance key) rows
/-- Full physical loop-boundary interpretation. No object of this type is in program control. -/
structure Summary where
  /-- Actual generated binary next key. -/
  key:List Bool
  /-- Actual reversed Boolean activation log. -/
  history:List Bool
  /-- Actual newest-first numeric-key/flag map. -/
  map:List Bool
/-- Exact interpretation of repeated actual row logging. -/
def finish (i:Inputs) (coordinate:Nat):List Bool→List Bool→List Bool→List Row→Summary
  | key,hist,map,[]=>⟨key,hist,map⟩
  | key,hist,map,row::rows=>finish i coordinate (advance key)
      (active i coordinate row.colours::hist)
      (true::frame key (frame [active i coordinate row.colours] map)) rows
/-- Sum of the same literal row traces and real marker/EOF pops. -/
def timeBound (i:Inputs) (coordinate:Nat) (environment catalogue:List (List Bool×List Bool)):
    List Bool→List Row→Nat
  | _,[]=>1
  | key,row::rows=>1+RowSource.timeBound i key row.selected row.unread coordinate environment catalogue row.colours+
      timeBound i coordinate environment catalogue (advance key) rows
/-- The only cross-iteration marker-word write updates its physical role. -/
theorem data_write_todo (i:Inputs) (todo next key hist map:List Bool):
    Function.update (data i todo key hist map) (aux .vertexTodo) next=data i next key hist map:=by
  funext k
  rcases k with k|k|k|k|k|k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · cases k <;> rfl
/-- Complete real all-old-vertex loop: every physical marker triggers one actual row source. -/
theorem source_trace (i:Inputs) (coordinate:Nat) (environment catalogue:List (List Bool×List Bool))
    (he:i.environment=SemiprimeD1StackOwnerLookup.records environment [])
    (hk:i.catalogue=SemiprimeD1StackOwnerLookup.records catalogue [])
    (hi:i.colourIndex=List.replicate coordinate true)
    (rows:List Row) (todo key hist map:List Bool)
    (hlen:todo.length=rows.length) (hv:Valid environment catalogue key rows):
    ∃t≤timeBound i coordinate environment catalogue key rows,
      Runs program t (.local 0 3) (data i todo key hist map) (.local 2 16)
        (data i [] (finish i coordinate key hist map rows).key
          (finish i coordinate key hist map rows).history (finish i coordinate key hist map rows).map):=by
  induction rows generalizing todo key hist map with
  | nil=>
    have hz:todo=[]:=by cases todo <;> simp_all
    subst todo
    have h:=pop_run (.local 0 3) (.local 2 16) (.local 0 4) (.local 0 4)
      (aux .vertexTodo) (data i [] key hist map) [] rfl rfl
    simp only [List.head?_nil,List.tail_nil,SemiprimeD1StackBytecode.choose] at h
    rw [data_write_todo] at h
    exact ⟨1,le_refl _,h⟩
  | cons row rows ih=>
    rcases todo with _|⟨bit,todo⟩
    · simp only [List.length_nil,List.length_cons] at hlen;omega
    · have hl:todo.length=rows.length:=by simp only [List.length_cons] at hlen;omega
      rcases hv with ⟨hget,hp,hr,hvalid⟩
      have h0:=pop_run (.local 0 3) (.local 2 16) (.local 0 4) (.local 0 4)
        (aux .vertexTodo) (data i (bit::todo) key hist map) (bit::todo) rfl rfl
      have h0':Runs program 1 (.local 0 3) (data i (bit::todo) key hist map)
          (.local 0 4) (data i todo key hist map):=by
        cases bit <;> simpa only [List.head?_cons,List.tail_cons,
          SemiprimeD1StackBytecode.choose,data_write_todo] using h0
      obtain ⟨a,ha,h1⟩:=RowSource.source_trace i todo key hist map coordinate environment catalogue
        row.selected row.unread row.colours he hk hi hget hp hr
      obtain ⟨b,hb,h2⟩:=ih todo (advance key) (active i coordinate row.colours::hist)
        (true::frame key (frame [active i coordinate row.colours] map)) hl hvalid
      refine ⟨1+(a+b),?_,join h0' (join h1 h2)⟩
      dsimp only [timeBound]
      omega
/-- Actual next-key numeric value advances once per marker, regardless of padding. -/
theorem advance_value (key:List Bool):
    SemiprimeBitArithmetic.bitValue (advance key)=SemiprimeBitArithmetic.bitValue key+1:=by
  rw [advance,SemiprimeBitArithmetic.addBits_correct]
  simp [SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat]
/-- Generated key bytes are bounded by the paid number of markers. -/
theorem advance_length (key:List Bool):(advance key).length≤key.length+2:=by
  have h:=(SemiprimeBitArithmetic.addBits_counts key [true] false).2.2.2.2
  simp only [List.length_cons,List.length_nil] at h
  change (SemiprimeBitArithmetic.addBits key [true] false).bits.length≤key.length+2
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationLoop

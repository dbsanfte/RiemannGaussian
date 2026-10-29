/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexSetup
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexOperations
/-! # Entire actual occurrence-port parsing and owner-pair logging loop
All keys below are literal physical Boolean words. Every vector tag, field byte,
validation pop and emitted owner-pair byte is traversed by the SAME17-role source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexPorts
open SemiprimeD1StackNetworkOwnerIndex SemiprimeD1StackNetworkOwnerIndexPrimitives
open SemiprimeD1StackNetworkOwnerIndexSetup SemiprimeD1StackNetworkOwnerIndexOperations
open SemiprimeD1StackNetworkOwnerIndexEncoding SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Exact literal rows for arbitrary physically parsed keys and the retained binary owner word. -/
def rows (keys:List (List Bool)) (owner:List Bool) :List (List Bool×List Bool) :=keys.map (fun key=>(key,owner))
/-- Actual original UNARY-port rows are the exact original ordered port/owner pairs. -/
theorem rows_unary (n owner:Nat) (ports:List Nat) :
    rows (ports.map SemiprimeD1StackUnaryDivmod.unary) (ownerWord n owner)=portPairs n owner ports :=by
  simp only [rows,portPairs,List.map_map,Function.comp_def]
/-- Complete actual ports-loop clock, including the final false vector-tag pop. -/
def portClock (owner:List Bool) (keys:List (List Bool)) :Nat :=
  (keys.map (fun key=>10*owner.length+19*key.length+30)).sum+1
/-- Real emission clears the parsed-key work and yields exactly the clean source boundary. -/
theorem emit_view (vertices count reader todo ports owner hist key:List Bool) :
    emitAfter (Function.update (view vertices count reader todo ports owner hist) .key key) key owner hist=
      view vertices count reader todo ports owner ((pairBytes (key,owner)).reverse++hist) :=by
  funext k
  cases k <;> simp [emitAfter,view,Function.update]
/-- One actual TRUE vector tag, actual key Field, actual TRUEvalid pop and full real emission. -/
theorem port_step (vertices count reader todo owner hist key:List Bool) (keys:List (List Bool)) :
    Runs program (10*owner.length+19*key.length+30) (ctl .portLoop)
      (view vertices count reader todo (vectorBits (key::keys)) owner hist) (ctl .portLoop)
      (view vertices count reader todo (vectorBits keys) owner ((pairBytes (key,owner)).reverse++hist)) :=by
  let tail:=vectorBits keys
  let b1:=view vertices count reader todo (frame key tail) owner hist
  let clean:=view vertices count reader todo tail owner hist
  let b2:=Function.update (Function.update clean .key key) .valid [true]
  let b3:=Function.update clean .key key
  have h0:=pop_run .portLoop (ctl .abort) (ctl .increment) (ctl .parseKey) .ports
    (view vertices count reader todo (vectorBits (key::keys)) owner hist) (true::frame key tail) rfl rfl
  change Runs program 1 (ctl .portLoop) _ (ctl .parseKey)
    (Function.update (view vertices count reader todo (vectorBits (key::keys)) owner hist) .ports (frame key tail)) at h0
  rw [view_ports] at h0
  have h1:=field_call .key .parseKey .keyValid rfl b1 key tail rfl rfl rfl rfl
  change Runs program (8*key.length+7) (ctl .parseKey) b1 (ctl .keyValid)
    (Function.update (Function.update (Function.update b1 .ports tail) .key key) .valid [true]) at h1
  rw [view_ports] at h1
  have h2:=pop_run .keyValid (ctl .abort) (ctl .abort) (ctl .valueFrame) .valid b2 [true] rfl (by simp [b2])
  have he2:Function.update b2 .valid []=b3:=by
    funext k;cases k <;> simp [b3,b2,clean,view,Function.update]
  change Runs program 1 (ctl .keyValid) b2 (ctl .valueFrame) (Function.update b2 .valid []) at h2
  rw [he2] at h2
  have h3:=emit_pair b3 key owner hist (by simp [b3])
    (by simp [b3,clean,view]) (by simp [b3,clean,view])
    (by simp [b3,clean,view]) (by simp [b3,clean,view])
  rw [emit_view] at h3
  have hh:=join (join (join h0 h1) h2) h3
  have hc:1+(8*key.length+7)+1+(10*owner.length+11*key.length+21)=10*owner.length+19*key.length+30:=by omega
  rw [hc] at hh
  exact hh
/-- Physically consume the actual final FALSEvector tag before incrementing the owner. -/
theorem port_end (vertices count reader todo owner hist:List Bool) :
    Runs program 1 (ctl .portLoop) (view vertices count reader todo (vectorBits []) owner hist)
      (ctl .increment) (view vertices count reader todo [] owner hist) :=by
  have h:=pop_run .portLoop (ctl .abort) (ctl .increment) (ctl .parseKey) .ports
    (view vertices count reader todo (vectorBits []) owner hist) [false] rfl rfl
  rw [view_ports] at h
  exact h
/-- Whole actual key-vector loop preserves BOTHoriginal inputs, suffix reader, countdown and binary owner. -/
theorem ports_run (vertices count reader todo owner hist:List Bool) (keys:List (List Bool)) :
    Runs program (portClock owner keys) (ctl .portLoop)
      (view vertices count reader todo (vectorBits keys) owner hist) (ctl .increment)
      (view vertices count reader todo [] owner ((payload (rows keys owner)).reverse++hist)) :=by
  induction keys generalizing hist with
  | nil=>exact port_end vertices count reader todo owner hist
  | cons key keys ih=>
    have h0:=port_step vertices count reader todo owner hist key keys
    have h1:=ih ((pairBytes (key,owner)).reverse++hist)
    have hh:=join h0 h1
    have hc:portClock owner (key::keys)=(10*owner.length+19*key.length+30)+portClock owner keys:=by
      simp only [portClock,List.map_cons,List.sum_cons]
      omega
    rw [hc]
    simpa only [rows,List.map_cons,payload,List.foldr_cons,List.reverse_append,List.append_assoc] using hh
/-- Exact sum clock accounts for all owner-copy bytes and every actual parsed key byte. -/
theorem portClock_eq (owner:List Bool) (keys:List (List Bool)) :
    portClock owner keys=10*owner.length*keys.length+19*(keys.map List.length).sum+30*keys.length+1 :=by
  induction keys with
  | nil=>simp only [portClock,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.zero_add]
  | cons key keys ih=>
    simp only [portClock,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    simp only [Nat.mul_add,Nat.mul_one]
    omega
/-- Existing vector codec physically contains both constructor/delimiter bytes for each key. -/
theorem vector_length (keys:List (List Bool)) :
    (vectorBits keys).length=2*(keys.map List.length).sum+2*keys.length+1 :=by
  induction keys with
  | nil=>rfl
  | cons key keys ih=>
    simp only [vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,ih,List.map_cons,List.sum_cons]
    omega
/-- Entire actual port loop has one fixed product bound in retained owner width and ACTUALport tape bytes. -/
theorem portClock_le (owner:List Bool) (keys:List (List Bool)) :
    portClock owner keys≤ 100*(owner.length+1)*(vectorBits keys).length :=by
  have hl:=vector_length keys
  have hn:keys.length≤(vectorBits keys).length:=by omega
  have hb:(keys.map List.length).sum≤(vectorBits keys).length:=by omega
  have hz:1≤(vectorBits keys).length:=by omega
  have hp:10*owner.length*keys.length≤ 10*owner.length*(vectorBits keys).length:=by gcongr
  have he:100*(owner.length+1)*(vectorBits keys).length=
      100*(owner.length*(vectorBits keys).length)+100*(vectorBits keys).length:=by ring
  rw [portClock_eq,he]
  simp only [Nat.mul_assoc] at hp ⊢
  omega
end RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexPorts

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkRowsRecords
import RiemannGaussian.SemiprimeD1StackNetworkRowsRow
/-! # Actual complete factor record, all actual port scans, row logger and factor/occurrence tallies -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRowsFactors
open SemiprimeD1StackNetworkRows SemiprimeD1StackNetworkRowsPrimitives SemiprimeD1StackNetworkRowsView
open SemiprimeD1StackNetworkRowsEncoding SemiprimeD1StackNetworkRowsPorts SemiprimeD1StackNetworkRowsRow
open SemiprimeD1StackNetworkRowsRecords SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Mathematical expected row from the physical local-port order; never a runtime owner supplier. -/
def rowWords (route:Nat→List Bool) (v:SemiprimeD1LeafCounter.Vertex) :List (List Bool) :=v.ports.map route
/-- Actual full-factor cap sums the actual parser, lookup-loop, row-construction and row-log caps. -/
def factorBudget (n:Nat) (dictionary:List Bool) (v:SemiprimeD1LeafCounter.Vertex) :Nat :=
  8*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length+
  9*(SemiprimeD1TensorTapeCodec.tape v.table).length+18+
  1000*(n+dictionary.length+2)*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length+
  40*(2*(n+2)*v.ports.length+2)
/-- Each expected owner is identified by the actual singleton scan of the actual acquired catalogue. -/
theorem related_ports (ports:List Nat) (route:Nat→List Bool) (rows:List (List Bool×List Bool)) (n:Nat)
    (hp:∀p∈ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) rows=[route p] ∧ (route p).length≤ n+1) :
    List.Forall₂ (fun key owner=>SemiprimeD1StackOwnerFibre.values key rows=[owner] ∧ owner.length≤ n+1)
      (ports.map SemiprimeD1StackUnaryDivmod.unary) (ports.map route) :=by
  induction ports with
  | nil=>exact List.Forall₂.nil
  | cons p ports ih=>
    exact List.Forall₂.cons (hp p (List.mem_cons_self)) (ih (fun q hq=>hp q (List.mem_cons_of_mem p hq)))
/-- WHOLEactual factor step: parse/drain the complete table, resolve/log every port, emit ONErow and tallyONEfactor. -/
theorem factor_step (index:I.Stack→List Bool) (tail history factors occurrences:List Bool)
    (v:SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool) (rows:List (List Bool×List Bool)) (n:Nat)
    (hd:index .output=SemiprimeD1StackOwnerFibre.records rows [])
    (hp:∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) rows=[route p] ∧ (route p).length≤ n+1) :
    ∃q≤ factorBudget n (SemiprimeD1StackOwnerFibre.records rows []) v,Runs program q (ctl .factorLoop)
      (view index (SemiprimeD1StackNetworkOwnerIndexLoop.vertexBytes v++tail) [] [] history factors occurrences) (ctl .factorLoop)
      (view index tail [] [] ((chunk (SemiprimeD1TensorTapeCodec.vectorBits (rowWords route v))).reverse++history)
        (true::factors) (List.replicate v.ports.length true++occurrences)) :=by
  have h0:=factor_fields index history factors occurrences (SemiprimeD1StackVertexReadExecution.portTape v.ports)
    (SemiprimeD1TensorTapeCodec.tape v.table) tail
  rw [←SemiprimeD1StackNetworkOwnerIndexLoop.vertexBytes_append] at h0
  obtain ⟨b,hb,h1⟩:=ports_run index tail [] history factors occurrences
    (v.ports.map SemiprimeD1StackUnaryDivmod.unary) (v.ports.map route) rows n hd (related_ports v.ports route rows n hp)
  simp only [List.append_nil,List.length_map] at h1
  have hw:∀w∈rowWords route v,w.length≤ n+1:=by
    intro w hw
    obtain ⟨p,hp0,rfl⟩:=List.mem_map.mp hw
    exact (hp p hp0).2
  obtain ⟨c,hc,h2⟩:=finish_row_bounded index tail history factors
    (List.replicate v.ports.length true++occurrences) (rowWords route v) n hw
  have hh:=join (join h0 h1) h2
  have hpClock:=portClock_le n (SemiprimeD1StackOwnerFibre.records rows []) (v.ports.map SemiprimeD1StackUnaryDivmod.unary)
  change portClock n (SemiprimeD1StackOwnerFibre.records rows []) (v.ports.map SemiprimeD1StackUnaryDivmod.unary)≤
    1000*(n+(SemiprimeD1StackOwnerFibre.records rows []).length+2)*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length at hpClock
  have hl:(rowWords route v).length=v.ports.length:=by simp only [rowWords,List.length_map]
  rw [hl] at hc
  refine ⟨(8*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length+
    9*(SemiprimeD1TensorTapeCodec.tape v.table).length+18)+b+c,?_,hh⟩
  unfold factorBudget
  omega
/-- Per-factor primitive caps are charged by ACTUALvertex-record bytes and the ACTUALcatalogue width. -/
theorem factorBudget_le (n:Nat) (dictionary:List Bool) (v:SemiprimeD1LeafCounter.Vertex) :
    factorBudget n dictionary v≤ 10000*(n+dictionary.length+2)*(SemiprimeD1StackNetworkOwnerIndexLoop.vertexBytes v).length :=by
  have hl:=vector_length (v.ports.map SemiprimeD1StackUnaryDivmod.unary)
  change (SemiprimeD1StackVertexReadExecution.portTape v.ports).length=
    2*((v.ports.map SemiprimeD1StackUnaryDivmod.unary).map List.length).sum+2*(v.ports.map SemiprimeD1StackUnaryDivmod.unary).length+1 at hl
  rw [List.length_map] at hl
  have hd:v.ports.length≤(SemiprimeD1StackVertexReadExecution.portTape v.ports).length:=by omega
  have hprod:80*(n+2)*v.ports.length≤ 80*(n+dictionary.length+2)*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length:=by gcongr;omega
  rw [SemiprimeD1StackNetworkOwnerIndexLoop.vertexBytes_length]
  unfold factorBudget
  nlinarith [Nat.zero_le (n*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length),
    Nat.zero_le (dictionary.length*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length),
    Nat.zero_le (n*(SemiprimeD1TensorTapeCodec.tape v.table).length),
    Nat.zero_le (dictionary.length*(SemiprimeD1TensorTapeCodec.tape v.table).length)]
/-- Exact sum of ACTUALfactor caps is paid by the actual original factor-record prefix. -/
theorem factorsBudget_le (n:Nat) (dictionary:List Bool) (factors:List SemiprimeD1LeafCounter.Vertex) :
    (factors.map (factorBudget n dictionary)).sum≤ 10000*(n+dictionary.length+2)*
      (SemiprimeD1StackNetworkOwnerIndexLoop.vertexPrefix factors).length :=by
  induction factors with
  | nil=>simp [SemiprimeD1StackNetworkOwnerIndexLoop.vertexPrefix]
  | cons v factors ih=>
    have h:=factorBudget_le n dictionary v
    change factorBudget n dictionary v+(factors.map (factorBudget n dictionary)).sum≤
      10000*(n+dictionary.length+2)*(SemiprimeD1StackNetworkOwnerIndexLoop.vertexBytes v++SemiprimeD1StackNetworkOwnerIndexLoop.vertexPrefix factors).length
    rw [List.length_append,Nat.mul_add]
    exact Nat.add_le_add h ih
end RiemannGaussian.SemiprimeD1StackNetworkRowsFactors

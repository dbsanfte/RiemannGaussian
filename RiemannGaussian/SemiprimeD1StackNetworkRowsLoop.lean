/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkRowsFactors
/-! # Whole actual factor-record loop, preserving empty rows and actual F/M tallies
Expected routing below is used ONLYin mathematical state/semantic propositions;
no route function, row list, factor count or occurrence count is a runtime input.
The original-network instance closes every singleton/width premise explicitly.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRowsLoop
open SemiprimeD1StackNetworkRows SemiprimeD1StackNetworkRowsPrimitives SemiprimeD1StackNetworkRowsView
open SemiprimeD1StackNetworkRowsEncoding SemiprimeD1StackNetworkRowsFactors SemiprimeD1StackNetworkRowsRecords
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Mathematical expected ordered row words; each is physically acquired by the actual lookup loop. -/
def ownerRows (route:Nat→List Bool) (factors:List SemiprimeD1LeafCounter.Vertex) :List (List (List Bool)) :=
  factors.map (rowWords route)
/-- Actual occurrence count described by literal local port records, including repeated owners. -/
def occurrences (factors:List SemiprimeD1LeafCounter.Vertex) :Nat :=(factors.map (fun v=>v.ports.length)).sum
/-- Repeated physical true pushes accumulate their exact acquired unary tally. -/
theorem tally_append (a b:Nat) (tail:List Bool) :
    List.replicate a true++(List.replicate b true++tail)=List.replicate (a+b) true++tail :=by
  rw [←List.append_assoc,←List.replicate_add]
/-- One further physically counted factor is retained after the subsequent factors' pushes. -/
theorem tally_succ (a:Nat) (tail:List Bool) :
    List.replicate a true++true::tail=List.replicate (a+1) true++tail :=by
  have h:=tally_append a 1 tail
  exact h
/-- Entire actual factor loop has one paid original primitive-cap sum and actual final factor-tag pop. -/
theorem factors_loop (index:I.Stack→List Bool) (history factorCount occurrenceCount:List Bool)
    (factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool) (rows:List (List Bool×List Bool)) (n:Nat)
    (hd:index .output=SemiprimeD1StackOwnerFibre.records rows [])
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) rows=[route p] ∧ (route p).length≤ n+1) :
    ∃q≤(factors.map (factorBudget n (SemiprimeD1StackOwnerFibre.records rows []))).sum+1,
      Runs program q (ctl .factorLoop)
        (view index (SemiprimeD1StackNetworkOwnerIndexLoop.vertexPrefix factors++[false]) [] [] history factorCount occurrenceCount)
        (ctl .finish)
        (view index [] [] [] ((payload ((ownerRows route factors).map SemiprimeD1TensorTapeCodec.vectorBits)).reverse++history)
          (List.replicate factors.length true++factorCount) (List.replicate (occurrences factors) true++occurrenceCount)) :=by
  induction factors generalizing history factorCount occurrenceCount with
  | nil=>
    refine ⟨1,by simp,?_⟩
    exact factors_end index history factorCount occurrenceCount
  | cons v factors ih=>
    obtain ⟨b,hb,h0⟩:=factor_step index (SemiprimeD1StackNetworkOwnerIndexLoop.vertexPrefix factors++[false]) history factorCount occurrenceCount
      v route rows n hd (hp v (List.mem_cons_self))
    obtain ⟨c,hc,h1⟩:=ih ((chunk (SemiprimeD1TensorTapeCodec.vectorBits (rowWords route v))).reverse++history)
      (true::factorCount) (List.replicate v.ports.length true++occurrenceCount)
      (fun w hw=>hp w (List.mem_cons_of_mem v hw))
    have hh:=join h0 h1
    refine ⟨b+c,?_,?_⟩
    · simp only [List.map_cons,List.sum_cons]
      omega
    · have hm:List.replicate (occurrences factors) true++(List.replicate v.ports.length true++occurrenceCount)=
          List.replicate (occurrences (v::factors)) true++occurrenceCount:=by
        rw [tally_append]
        have he:occurrences factors+v.ports.length=occurrences (v::factors):=by
          unfold occurrences
          simp only [List.map_cons,List.sum_cons]
          omega
        rw [he]
      simpa only [SemiprimeD1StackNetworkOwnerIndexLoop.vertexPrefix,List.foldr_cons,List.append_assoc,
        ownerRows,List.map_cons,payload,List.foldr_cons,List.reverse_append,List.length_cons,tally_succ,hm] using hh
end RiemannGaussian.SemiprimeD1StackNetworkRowsLoop

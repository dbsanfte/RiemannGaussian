/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordsOriginal
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsExecution
open SemiprimeD1StackOwnerRecords SemiprimeD1StackOwnerRecordsView
open SemiprimeD1StackOwnerRecordsLoop SemiprimeD1StackOwnerRecordsAcquisition
open SemiprimeD1StackOwnerRecordsFinish SemiprimeD1StackOwnerRecordsOriginal
open SemiprimeD1StackProcedureTrace (Runs runs_trans halt_run)
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (wireCount)
open SemiprimeD1OwnerPrefixBits (records)
/-- Exact complete physical halt store with original source data and prefix retained. -/
def done (bits:List Bool) (hN:0<bitValue bits) (fixed:List (Fin (wireCount (bitValue bits))×Bool))
    (tail:List Bool) :C.State Stack Label:=
  result (SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN).data
    (bytes (originalRows (bitValue bits) hN) (prefixRows (bitValue bits) fixed))
    (records (prefixRows (bitValue bits) fixed) tail)
/-- SAME actual acquisition and row loop, including physical final reversal and halt. -/
def budget (bits:List Bool) (hN:0<bitValue bits) (fixed:List (Fin (wireCount (bitValue bits))×Bool))
    (tail:List Bool) :Nat:=
  acquisitionBudget bits hN+
    loopBudget (originalRows (bitValue bits) hN) (prefixRows (bitValue bits) fixed) tail+
    2*(bytes (originalRows (bitValue bits) hN) (prefixRows (bitValue bits) fixed)).length+5
/-- Complete original-N acquisition and ALL owners, retaining arbitrary actual caller prefix bytes. -/
theorem main_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃time≤budget bits hN fixed tail-1,Runs program time (.local .main)
      (initialPrefix bits (records (prefixRows (bitValue bits) fixed) tail)).data
      (.local .halt) (done bits hN fixed tail).data:=by
  let s:=(SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN).data
  let rs:=originalRows (bitValue bits) hN
  let ps:=prefixRows (bitValue bits) fixed
  obtain ⟨a,ha,h0⟩:=acquisition_run bits (records ps tail) hc hN
  rw [ready_original bits (records ps tail) hN] at h0
  obtain ⟨b,hb,h1⟩:=loop_run s rs ps tail [] [false]
  simp only [List.append_nil] at h1
  have h2:=finish_run s (bytes rs ps) (records ps tail)
  refine ⟨a+(b+(2*(bytes rs ps).length+4)),?_,?_⟩
  · dsimp only [budget,rs,ps] at *
    omega
  · exact runs_trans program _ _ _ _ _ _ _ _ h0 (runs_trans program _ _ _ _ _ _ _ _ h1 h2)
/-- Caller-prefix entry supplies ONLY original N and its actual encoded prefix/tail. -/
theorem source_run_prefix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃time≤budget bits hN fixed tail,C.run program time
      (initialPrefix bits (records (prefixRows (bitValue bits) fixed) tail))=some (done bits hN fixed tail):=by
  obtain ⟨t,ht,hr⟩:=main_run bits hc hN fixed tail
  obtain ⟨finish,hf,ho⟩:=hr [] (initialPrefix bits (records (prefixRows (bitValue bits) fixed) tail)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .halt) rfl (done bits hN fixed tail).data [] finish ho
  refine ⟨t+1,?_,?_⟩
  · unfold budget at *;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some,hh];rfl
/-- N-only EMPTY-prefix run physically pushes the prefix terminator and acquires EVERY owner operand. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃time≤budget bits hN [] []+1,C.run program time (initial bits)=some (done bits hN [] []):=by
  obtain ⟨t,ht,hr⟩:=main_run bits hc hN [] []
  have h:=runs_trans program _ _ _ _ _ _ _ _ (empty_seed bits) hr
  obtain ⟨finish,hf,ho⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .halt) rfl (done bits hN [] []).data [] finish ho
  refine ⟨(1+t)+1,?_,?_⟩
  · unfold budget at *;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some,hh];rfl
/-- ACTUAL complete output equals ALL original owner records with exact unary old-reader ports. -/
theorem output_original (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (done bits hN fixed tail).data output=
      SemiprimeD1StackVertexProduct.records (vertices (bitValue bits) hN fixed):=by
  change bytes _ _++[false]=_
  exact bytes_original (bitValue bits) hN fixed
/-- Complete source/catalogue and actual caller prefix/tail survive every original owner row. -/
theorem retained_prefix (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (done bits hN fixed tail).data (aux .prefixBytes)=records (prefixRows (bitValue bits) fixed) tail:=rfl
end RiemannGaussian.SemiprimeD1StackOwnerRecordsExecution

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseGridPrimitives
/-! # One actual N-only trace acquires and conditionally enumerates every phase index -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseGridExecution
open SemiprimeD1StackRootPhaseGrid SemiprimeD1StackRootPhaseGridEncoding
open SemiprimeD1StackRootPhaseGridPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => (Sum.inl : Control→Label)
/-- Actual branch/copy/zero/enumeration budget before the literal final halt. -/
def preparedBound (a:Nat) : Nat :=100*(a+2)*2^(a+1)+7*a+18
/-- Same fixed program before N: real root acquisition, conditional catalogue,
each real call/return, physical count-byte consumption and final halt. -/
def runBound (bits:List Bool) : Nat :=R.runBound bits+preparedBound (exponentValue bits)+2
/-- Prepared acquired-root boundary, not an N-only claim by itself. The runtime
branch reads the actual supplied source cell; no evaluator/callback enters code. -/
theorem prepared_trace (root:R.Stack→List Bool) (verdict:Bool) (a:Nat)
    (hg:root R.output=[verdict])
    (ha:root (R.sourceStack SemiprimeD1StackRootParameters.exponent)=List.replicate a true) :
    ∃t≤ preparedBound a,Runs program t (ctl .branch) (prepared root) (ctl .done) (finished root verdict a) :=by
  cases verdict with
  | false=>
    refine ⟨1,by unfold preparedBound;omega,?_⟩
    exact branch_false root hg
  | true=>
    have h0:=branch_true root hg
    have h1:=copy_exponent root (List.replicate a true) ha
    rw [List.length_replicate] at h1
    have h2:=seed_zero root (List.replicate a true)
    have h3:=fill_zero root a 1
    obtain ⟨t,ht,h4⟩:=enumerate_call root a
    have hh:=compose (compose (compose (compose h0 h1) h2) h3) h4
    refine ⟨(((1+(5*a+4))+1)+(2*a+1))+(t+1),?_,hh⟩
    unfold preparedBound
    omega
/-- One actual original-input call acquires all119 source operands before the guard is read. -/
theorem root_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤R.runBound bits,Runs program (t+1) (ctl .start) (input bits) (ctl .branch) (afterRoot bits) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootRecursiveControlExecution.source_run bits hc hN
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rootStack rootLabel Sum.inl_injective
    R.program (.inl .start) (fun _=>rfl) (ctl .start) (ctl .branch) rfl t
    (R.initial bits) (R.done bits) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      cases k with
      | inl k=>exact (hk k rfl).elim
      | inr k=>rfl
/-- Source-produced guard and exponent words discharge every prepared-stage
premise; the entire actual original-N input path stays in this same program. -/
theorem source_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t,t+1≤ runBound bits ∧ Runs program t (ctl .start) (input bits) (ctl .done) (result bits) :=by
  obtain ⟨r,hr,h0⟩:=root_call bits hc hN
  obtain ⟨p,hp,h1⟩:=prepared_trace (R.result bits) (active bits) (exponentValue bits)
    (acquired_guard bits hc) (acquired_exponent bits hc)
  rw [←afterRoot_eq] at h1
  refine ⟨(r+1)+p,?_,compose h0 h1⟩
  unfold runBound
  omega
/-- Whole genuine source execution: N-only acquisition, physical guard, binary
zero construction, actual full grid if active, and all actual final cleanup. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤ runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) :=by
  obtain ⟨t,ht,h⟩:=source_trace bits hc hN
  obtain ⟨finish,hf,hs⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits) [] finish hs
  refine ⟨t+1,ht,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
end RiemannGaussian.SemiprimeD1StackRootPhaseGridExecution

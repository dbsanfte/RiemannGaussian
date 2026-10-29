/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryContexts
/-! # Whole front door reaches the SAME actual two-context ready bank -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryAcquisition
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryContexts SemiprimeD1StackChildTableEntryPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Original positive-axis contexts really have positive acquired rank. -/
theorem prod_positive (axes:List Nat) (hp:∀q∈axes,0<q):0<axes.prod:=by
  induction axes with
  | nil=>decide
  | cons q qs ih=>exact Nat.mul_pos (hp q List.mem_cons_self) (ih (fun r hr=>hp r (List.mem_cons_of_mem q hr)))
/-- Exact own sum of both real context-source budgets and their two actual caller returns. -/
def budget (oldAxes newAxes:List Nat) (oldp newp:List Bool):Nat:=
  SemiprimeD1StackJetContextCorrectness.budget oldAxes oldp+
    SemiprimeD1StackJetContextCorrectness.budget newAxes newp+2
/-- Whole actual seven-input front door physically acquires BOTH context caches, preserving every other source word. -/
theorem contexts_run (oldAxes newAxes:List Nat) (ho:∀q∈oldAxes,0<q) (hn:∀q∈newAxes,0<q)
    (oldp newp table order assignment:List Bool):
    ∃t ≤ budget oldAxes newAxes oldp newp,Runs program t (.local .start)
      (initial table order assignment (vectorBits (oldAxes.map unary)) oldp (vectorBits (newAxes.map unary)) newp).data
      (.local .ready) (ready oldAxes newAxes oldp newp table order assignment).data:=by
  let g:=G.contents [] assignment [] [] [] []
  let tree:=T.contents [] [] [] [] []
  let r:=R.store [] [] [] [] [] [] [] []
  let w:=words ({parentTable:=table,order:=order}:Words)
  obtain ⟨t0,ht0,h0⟩:=old_call oldAxes ho oldp (J.initial (vectorBits (newAxes.map unary)) newp).data g tree r w
  obtain ⟨t1,ht1,h1⟩:=child_call newAxes hn newp (Context.finalData oldAxes oldp) g tree r w
  have h:=join h0 h1
  rw [initial_bank]
  exact ⟨t0+t1,by unfold budget;omega,h⟩
end RiemannGaussian.SemiprimeD1StackChildTableEntryAcquisition

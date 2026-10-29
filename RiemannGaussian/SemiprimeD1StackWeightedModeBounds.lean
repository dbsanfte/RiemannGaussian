/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeExecution
import RiemannGaussian.SemiprimeD1StackWeightedModeCapacities
/-! # Same-program source cost per actual feasible visit
Even output reversal is paid from the actual successfully executed logger
trace. No native execution report or supplied output-size bound is used.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeBounds
open SemiprimeD1StackWeightedMode SemiprimeD1StackWeightedModeView
open SemiprimeD1StackWeightedModeSpec SemiprimeD1StackWeightedModeLoop
open SemiprimeD1StackWeightedModeExecution SemiprimeD1StackWeightedModeCapacities
open SemiprimeD1WeightedTuples (visits)
local notation "ctl" => (Sum.inl : Control→Label)
attribute [local irreducible] nodeBudget timeBound
/-- Every initialized node word fits its actual physical catalogue, WIDTH and path byte count. -/
theorem node_initial_length (ws:List Nat) (width:Nat) (k:Stack) :
    (store (node (vector ws) (unary width) ws (width-1) (path []) [] [] []) k).length ≤
      (vector ws).length+width+1:=by
  cases k <;> simp only [store,node,base,unary_length,path,List.reverse_nil,vector_nil,
    List.length_cons,List.length_nil] <;> omega
/-- Literal logged bytes are bounded by the SAME actual successful DFS trace. -/
theorem history_length (ws:List Nat) (hw:∀w∈ws,0 < w) (width:Nat) :
    (history (payloads ws width) []).length ≤
      (vector ws).length+width+1+nodeBudget ws (width-1) 1:=by
  obtain ⟨t,ht,hr⟩:=visit_run (vector ws) (unary width) ws hw (width-1) [] [] [] []
  let start:C.State Stack Label:=⟨some (ctl .visit),none,none,
    store (node (vector ws) (unary width) ws (width-1) (path []) [] [] []),[]⟩
  obtain ⟨finish,hf,ha⟩:=hr [] start ⟨rfl,rfl,rfl⟩
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program t ((vector ws).length+width+1)
    start finish (node_initial_length ws width) hf .history
  rw [ha.2.1] at hd
  change (history (payloads ws width) []).length ≤ (vector ws).length+width+1+t at hd
  change t ≤ nodeBudget ws (width-1) 1 at ht
  omega
/-- Whole caller source budget charges copies, predecessor, true recursion, output and final halt. -/
theorem timeBound_le (ws:List Nat) (hw:∀w∈ws,0 < w) (width:Nat) :
    timeBound ws width ≤10*((vector ws).length+width+nodeBudget ws (width-1) 1+2):=by
  have h:=history_length ws hw width
  unfold timeBound
  omega
/-- Polynomial in real catalogue/WIDTH bytes, paid once per actual feasible visited node. -/
def visitCoefficient (ws:List Nat) (width:Nat) :Nat:=
  10*((vector ws).length+width+200*capacity ws (width-1) 1*(ws.length+1)+2)
/-- One complete same-source allowance, with no oracle step or free native catalogue work. -/
def runBound (ws:List Nat) (width:Nat) :Nat:=visitCoefficient ws width*visits ws (width-1)
/-- Actual source clock is polynomial per actual feasible node, including actual output-byte reversal. -/
theorem timeBound_visits (ws:List Nat) (hw:∀w∈ws,0 < w) (width:Nat) :
    timeBound ws width ≤ runBound ws width:=by
  have ht:=timeBound_le ws hw width
  have hn:=nodeBudget_le ws hw (width-1) 1
  have hv:1 ≤ visits ws (width-1):=Nat.succ_le_of_lt (SemiprimeD1WeightedTuples.visits_positive _ _)
  have hb:(vector ws).length+width+2 ≤ ((vector ws).length+width+2)*visits ws (width-1):=by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((vector ws).length+width+2) hv
  unfold runBound visitCoefficient
  nlinarith only [ht,hn,hb]
/-- One successful actual prepared-input run, with the own feasible-node allowance. -/
theorem source_run_bounded (ws:List Nat) (hw:∀w∈ws,0 < w) (width:Nat) :
    ∃t ≤ runBound ws width,C.run program t (initial (vector ws) (unary width))=some (done ws width):=by
  obtain ⟨t,ht,hr⟩:=source_run ws hw width
  exact ⟨t,ht.trans (timeBound_visits ws hw width),hr⟩
/-- Actual feasible menu cardinality can be applied to this SAME physical program. -/
theorem runBound_le_leaves (ws:List Nat) (width:Nat) :
    runBound ws width ≤visitCoefficient ws width*(ws.length+1)*
      (SemiprimeD1WeightedTuples.tuples ws (width-1)).length:=by
  have h:=Nat.mul_le_mul_left (visitCoefficient ws width) (SemiprimeD1WeightedTuples.visits_le ws (width-1))
  simpa only [runBound,Nat.mul_assoc] using h
end RiemannGaussian.SemiprimeD1StackWeightedModeBounds

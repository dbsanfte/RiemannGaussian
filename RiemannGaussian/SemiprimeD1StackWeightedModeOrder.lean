/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeView
/-! # Original feasible-branch order for the real subtraction controller
Natural division occurs ONLY in these mathematical target lists. The executed
source decides continuation by physically subtracting one positive weight.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeOrder
open SemiprimeD1WeightedTuples (tuples visits)
/-- Remaining feasible branches when the current real exponent is e. -/
def branches (w:Nat) (ws:List Nat) (R e:Nat) :List (List Nat):=
  (List.range (R/w+1)).flatMap fun k=>(tuples ws (R-w*k)).map ((e+k)::·)
/-- Actual child-node count of those remaining feasible branches; never a runtime counter input. -/
def childVisits (w:Nat) (ws:List Nat) (R:Nat) :Nat:=
  ((List.range (R/w+1)).map fun k=>visits ws (R-w*k)).sum
/-- A successful actual subtraction creates exactly the next residual in the native target order. -/
theorem residual_succ (R w k:Nat) :R-w*(k+1)=(R-w)-w*k:=by
  rw [Nat.mul_succ]
  omega
/-- Current exponent zero is exactly the original weighted tuple list. -/
theorem branches_zero (w:Nat) (ws:List Nat) (P:Nat) :branches w ws P 0=tuples (w::ws) P:=by
  simp only [branches,SemiprimeD1WeightedTuples.tuples,Nat.zero_add]
/-- The only failed subtraction leaves exactly the current zero-offset branch. -/
theorem branches_last (w:Nat) (ws:List Nat) (R e:Nat) (h:R < w) :
    branches w ws R e=(tuples ws R).map (e::·):=by
  simp only [branches,Nat.div_eq_of_lt h,Nat.zero_add,List.range_one,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,Nat.add_zero,Nat.mul_zero,Nat.sub_zero]
/-- Successful subtraction follows the current complete child by the next feasible exponent block. -/
theorem branches_step (w:Nat) (ws:List Nat) (R e:Nat) (hw:0 < w) (hr:w ≤ R) :
    branches w ws R e=(tuples ws R).map (e::·)++branches w ws (R-w) (e+1):=by
  unfold branches
  rw [Nat.div_eq_sub_div hw hr,List.range_succ_eq_map]
  simp only [List.flatMap_cons,List.flatMap_map,Nat.mul_zero,Nat.sub_zero,Nat.add_zero]
  apply congrArg (fun tail=>(tuples ws R).map (e::·)++tail)
  apply congrArg (fun f=>List.flatMap f (List.range ((R-w)/w+1)))
  funext k
  change (tuples ws (R-w*(k+1))).map ((e+(k+1))::·)=_
  rw [residual_succ]
  have he:e+(k+1)=(e+1)+k:=by omega
  rw [he]
/-- Native visits are the exact feasible recursion node plus its actual child blocks. -/
theorem visits_cons (w:Nat) (ws:List Nat) (P:Nat) :visits (w::ws) P=1+childVisits w ws P:=rfl
/-- The last physical subtraction failure contributes no further child visits. -/
theorem childVisits_last (w:Nat) (ws:List Nat) (R:Nat) (h:R < w) :childVisits w ws R=visits ws R:=by
  simp only [childVisits,Nat.div_eq_of_lt h,Nat.zero_add,List.range_one,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,Nat.add_zero,Nat.mul_zero,Nat.sub_zero]
/-- Successful repeated subtraction partitions the SAME actual feasible children. -/
theorem childVisits_step (w:Nat) (ws:List Nat) (R:Nat) (hw:0 < w) (hr:w ≤ R) :
    childVisits w ws R=visits ws R+childVisits w ws (R-w):=by
  unfold childVisits
  rw [Nat.div_eq_sub_div hw hr,List.range_succ_eq_map]
  simp only [List.map_cons,List.sum_cons,List.map_map,Function.comp_def,Nat.mul_zero,Nat.sub_zero]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro k _
  change visits ws (R-w*(k+1))=visits ws ((R-w)-w*k)
  rw [residual_succ]
/-- Every real branch has a zero completion, so branch overhead is charged to feasible nodes. -/
theorem branches_le_visits (w:Nat) (ws:List Nat) (R:Nat) :R/w+1 ≤ childVisits w ws R:=by
  have h:=List.sum_le_sum (fun k (_:k∈List.range (R/w+1))=>
    Nat.succ_le_of_lt (SemiprimeD1WeightedTuples.visits_positive ws (R-w*k)))
  simpa [childVisits] using h
/-- Each successful continuation has strictly smaller physical residual for a positive weight. -/
theorem residual_lt (R w:Nat) (hw:0 < w) (hr:w ≤ R) :R-w < R:=by omega
end RiemannGaussian.SemiprimeD1StackWeightedModeOrder

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeRound
import RiemannGaussian.SemiprimeD1StackWeightedModeOrder
/-! # Literal output and primitive-derived allowance for the same feasible DFS
All target lists and allowances here are proof notation. The executing program
contains only Boolean stack operations, finite labels and genuine returns.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeSpec
open SemiprimeD1StackWeightedModeView SemiprimeD1StackWeightedModeOrder
open SemiprimeD1StackWeightedModeActivation (mass)
open SemiprimeD1WeightedTuples (tuples)
/-- Actual scalar field mass of a saved current branch. -/
def edge (w:Nat) (ws:List Nat) (R e L:Nat) :Nat:=200*(w+(vector ws).length+R+e+L+1)
/-- Own allowance: actual leaf byte work or actual positive-weight entry plus real feasible children/edges. -/
def nodeBudget :List Nat→Nat→Nat→Nat
  | [],P,L=>70*(P+L+1)+1
  | w::ws,P,L=>8*w+10+((List.range (P/w+1)).map fun e=>
      nodeBudget ws (P-w*e) (L+2*e+2)+edge w ws (P-w*e) e L).sum
/-- Remaining actual feasible-child allowances at current residual/exponent. -/
def branchBudget (w:Nat) (ws:List Nat) (R e L:Nat) :Nat:=
  ((List.range (R/w+1)).map fun k=>
    nodeBudget ws (R-w*k) (L+2*(e+k)+2)+edge w ws (R-w*k) (e+k) L).sum
/-- Literal tuple payloads after the already chosen original coordinates. -/
def values (ws:List Nat) (P:Nat) (chosen:List Nat) :List (List Bool):=
  (tuples ws P).map (fun rest=>vector (chosen++rest))
/-- Current/exponent-shifted remaining complete tuple payloads. -/
def branchValues (w:Nat) (ws:List Nat) (R e:Nat) (chosen:List Nat) :List (List Bool):=
  (branches w ws R e).map (fun rest=>vector (chosen++rest))
/-- Actual path framing has exactly this physical byte increment. -/
theorem extend_length (e:Nat) (p:List Bool) :(extend e p).length=p.length+2*e+2:=by
  simp only [extend,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,unary_length]
  omega
/-- The child path is the same physical framing of the next chosen exponent. -/
theorem path_length (chosen:List Nat) (e:Nat) :(path (chosen++[e])).length=(path chosen).length+2*e+2:=by
  rw [path_extend,extend_length]
/-- The primitive edge allowance is derived from the actual five current word lengths. -/
theorem loop_mass (cat width:List Bool) (w:Nat) (ws:List Nat) (R e:Nat) (p fs hist out:List Bool) :
    mass (loop cat width w ws R e p fs hist out)=w+(vector ws).length+R+e+p.length:=by
  simp only [mass,loop,node,base,unary_length]
/-- Numeric budget recursion is exactly the initial actual exponent-zero loop allowance. -/
theorem nodeBudget_cons (w:Nat) (ws:List Nat) (P L:Nat) :
    nodeBudget (w::ws) P L=8*w+10+branchBudget w ws P 0 L:=by
  simp only [nodeBudget,branchBudget,Nat.zero_add]
/-- The final physical failure leaves precisely one actual child/edge allowance. -/
theorem branchBudget_last (w:Nat) (ws:List Nat) (R e L:Nat) (h:R < w) :
    branchBudget w ws R e L=nodeBudget ws R (L+2*e+2)+edge w ws R e L:=by
  simp only [branchBudget,Nat.div_eq_of_lt h,Nat.zero_add,List.range_one,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_zero,Nat.sub_zero]
/-- One successful actual subtraction removes exactly the first actual child/edge allowance. -/
theorem branchBudget_step (w:Nat) (ws:List Nat) (R e L:Nat) (hw:0 < w) (hr:w ≤ R) :
    branchBudget w ws R e L=nodeBudget ws R (L+2*e+2)+edge w ws R e L+
      branchBudget w ws (R-w) (e+1) L:=by
  unfold branchBudget
  rw [Nat.div_eq_sub_div hw hr,List.range_succ_eq_map]
  simp only [List.map_cons,List.sum_cons,List.map_map,Nat.mul_zero,Nat.sub_zero,Nat.add_zero]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro k _
  change nodeBudget ws (R-w*(k+1)) (L+2*(e+(k+1))+2)+edge w ws (R-w*(k+1)) (e+(k+1)) L=_
  rw [residual_succ]
  have he:e+(k+1)=(e+1)+k:=by omega
  rw [he]
/-- Current exponent zero is the unchanged native target order for all remaining tuples. -/
theorem branchValues_zero (w:Nat) (ws:List Nat) (P:Nat) (chosen:List Nat) :
    branchValues w ws P 0 chosen=values (w::ws) P chosen:=by
  rw [branchValues,branches_zero]
  rfl
/-- Chosen-coordinate concatenation agrees with physically extending the reverse path. -/
theorem cons_values (ws:List Nat) (R e:Nat) (chosen:List Nat) :
    ((tuples ws R).map (e::·)).map (fun rest=>vector (chosen++rest))=values ws R (chosen++[e]):=by
  simp only [List.map_map,values,Function.comp_def,List.append_assoc,List.singleton_append]
/-- No further feasible exponent survives the sole failed physical subtraction test. -/
theorem branchValues_last (w:Nat) (ws:List Nat) (R e:Nat) (chosen:List Nat) (hr:R < w) :
    branchValues w ws R e chosen=values ws R (chosen++[e]):=by
  rw [branchValues,branches_last w ws R e hr,cons_values]
/-- Remaining payloads follow the current complete child before the next feasible exponent. -/
theorem branchValues_step (w:Nat) (ws:List Nat) (R e:Nat) (chosen:List Nat) (hw:0 < w) (hr:w ≤ R) :
    branchValues w ws R e chosen=values ws R (chosen++[e])++branchValues w ws (R-w) (e+1) chosen:=by
  rw [branchValues,branches_step w ws R e hw hr,List.map_append,cons_values]
  rfl
/-- One emitted tuple has its actual literal row bytes in the reverse history. -/
theorem history_single (x old:List Bool) :history [x] old=(row x).reverse++old:=by
  simp only [history,List.foldr_cons,List.foldr_nil,List.append_nil]
end RiemannGaussian.SemiprimeD1StackWeightedModeSpec

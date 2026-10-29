/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeSpec
/-! # Polynomial byte allowance per feasible node of the actual source
The recurrence bounded here is the allowance derived from literal parser,
copy, frame, subtraction, cleanup and logger executions, not a native clock.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeCapacities
open SemiprimeD1StackWeightedModeView SemiprimeD1StackWeightedModeSpec
open SemiprimeD1WeightedTuples (visits)
/-- Physical suffix bytes plus the maximum actual remaining path growth. -/
def capacity (ws:List Nat) (P L:Nat) :Nat:=
  (vector ws).length+L+2*ws.length*(P+1)+P+1
/-- Exact real framed catalogue byte length at a positive or repeated weight. -/
theorem vector_length_cons (w:Nat) (ws:List Nat) :
    (vector (w::ws)).length=2*w+2+(vector ws).length:=by
  simp only [vector_cons,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,unary_length]
  omega
/-- Every feasible exponent is bounded by the acquired residual unary budget. -/
theorem exponent_le (w P e:Nat) (he:e∈List.range (P/w+1)) :e ≤ P:=by
  have h:e ≤ P/w:=by have h:=List.mem_range.mp he;omega
  exact h.trans (Nat.div_le_self P w)
/-- A real child cannot increase the shared physical capacity allowance. -/
theorem child_capacity (w:Nat) (ws:List Nat) (P L e:Nat) (he:e ≤ P) :
    capacity ws (P-w*e) (L+2*e+2) ≤ capacity (w::ws) P L:=by
  have hr:P-w*e ≤ P:=Nat.sub_le _ _
  unfold capacity
  rw [vector_length_cons,List.length_cons]
  nlinarith
/-- All literal branch overhead fits a polynomial in current physical input capacity. -/
theorem edge_capacity (w:Nat) (ws:List Nat) (P L e:Nat) (he:e ≤ P) :
    edge w ws (P-w*e) e L ≤ 200*capacity (w::ws) P L:=by
  have hr:P-w*e ≤ P:=Nat.sub_le _ _
  unfold edge capacity
  rw [vector_length_cons,List.length_cons]
  nlinarith
/-- Whole actual primitive DFS allowance is polynomial per actual feasible visit. -/
theorem nodeBudget_le (ws:List Nat) (hw:∀w∈ws,0 < w) (P L:Nat) :
    nodeBudget ws P L ≤200*capacity ws P L*(ws.length+1)*visits ws P:=by
  induction ws generalizing P L with
  | nil=>
    simp only [nodeBudget,capacity,vector_nil,List.length_cons,List.length_nil,
      Nat.mul_zero,Nat.zero_mul,Nat.add_zero,visits,Nat.mul_one]
    omega
  | cons w ws ih=>
    have hws:∀v∈ws,0 < v:=fun v hv=>hw v (by simp [hv])
    let cap:=capacity (w::ws) P L
    let coeff:=200*cap*(ws.length+2)
    have hentry:8*w+10 ≤ coeff:=by
      have hc:w+1 ≤ cap:=by
        dsimp [cap,capacity]
        rw [vector_length_cons]
        omega
      have hh:200*cap ≤ coeff:=by
        dsimp [coeff]
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (200*cap) (by omega:1 ≤ ws.length+2)
      omega
    have hterm:∀e∈List.range (P/w+1),
        nodeBudget ws (P-w*e) (L+2*e+2)+edge w ws (P-w*e) e L ≤
          coeff*visits ws (P-w*e):=by
      intro e he
      have heP:=exponent_le w P e he
      have hc:=child_capacity w ws P L e heP
      have hn:nodeBudget ws (P-w*e) (L+2*e+2) ≤200*cap*(ws.length+1)*visits ws (P-w*e):=
        (ih hws (P-w*e) (L+2*e+2)).trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 200 hc)))
      have hedge:edge w ws (P-w*e) e L ≤200*cap:=edge_capacity w ws P L e heP
      have hv:1 ≤ visits ws (P-w*e):=Nat.succ_le_of_lt (SemiprimeD1WeightedTuples.visits_positive _ _)
      have hpay:200*cap ≤200*cap*visits ws (P-w*e):=by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (200*cap) hv
      dsimp [coeff]
      nlinarith only [hn,hedge,hpay]
    have hsum:=List.sum_le_sum hterm
    rw [List.sum_map_mul_left] at hsum
    change 8*w+10+_ ≤ _
    simp only [List.length_cons,visits]
    change 8*w+10+_ ≤ coeff*(1+_)
    nlinarith only [hentry,hsum]
/-- The same actual clock can be bounded by the actual feasible leaf cardinality. -/
theorem nodeBudget_le_leaves (ws:List Nat) (hw:∀w∈ws,0 < w) (P L:Nat) :
    nodeBudget ws P L ≤200*capacity ws P L*(ws.length+1)^2*
      (SemiprimeD1WeightedTuples.tuples ws P).length:=by
  have h:=nodeBudget_le ws hw P L
  have hv:=SemiprimeD1WeightedTuples.visits_le ws P
  have hh:=h.trans (Nat.mul_le_mul_left (200*capacity ws P L*(ws.length+1)) hv)
  convert hh using 1;ring
end RiemannGaussian.SemiprimeD1StackWeightedModeCapacities

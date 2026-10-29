/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryLoop
import RiemannGaussian.SemiprimeD1StackChildTableEntryScalarCost
/-! # Paid complete coefficient-loop bounds, including every appended zero
All caps sum SAME actual scalar/field/counter/logger/reverse clocks.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryLoopCost
open SemiprimeD1StackChildTableEntryEncoding SemiprimeD1StackChildTableEntryScalar
open SemiprimeD1StackChildTableEntryScalarCost SemiprimeD1StackChildTableEntryRows
open SemiprimeBitArithmetic (bitValue)
namespace Old
export SemiprimeD1StackChildTableEntryOld (budget)
end Old
namespace Zero
export SemiprimeD1StackChildTableEntryZeros (budget budget_eq)
end Zero
/-- All original coefficient headers, marker pops, individual reductions and logger costs are charged linearly per actual coefficient. -/
theorem rowTime_le (word p:List Bool):rowTime word p ≤200*(word.length+p.length+bitValue p+1):=by
  have h:=scalarTime_le word p
  unfold rowTime
  omega
/-- Entire actual old-coefficient loop sums the actual input coefficient bytes and actual NEWp expansion per coefficient. -/
theorem old_budget_le (p:List Bool) (ws:List (List Bool)):
    Old.budget p ws ≤200*((ws.map List.length).sum+ws.length*(p.length+bitValue p+1))+3:=by
  induction ws with
  | nil=>simp only [Old.budget,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | cons word ws ih=>
    have h:=rowTime_le word p
    simp only [Old.budget,List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [h,ih]
/-- Every new-axis zero also pays its own actual precision conversion and individual reduction. -/
theorem zero_budget_le (p:List Bool) (n:Nat):Zero.budget p n ≤201*n*(p.length+bitValue p+1)+1:=by
  have h:=scalarTime_le [] p
  rw [Zero.budget_eq]
  have hp:1+scalarTime [] p ≤201*(p.length+bitValue p+1):=by simpa only [List.length_nil,Nat.zero_add] using (show 1+scalarTime [] p ≤201*(p.length+bitValue p+1) by simp only [List.length_nil,Nat.zero_add] at h;omega)
  have hh:=Nat.mul_le_mul_left n hp
  nlinarith only [hh]
/-- Every actual tagged coefficient frame contributes its exact byte length to final reversal. -/
theorem history_length_le (ws:List (List Bool)) (P:Nat) (hw:∀w∈ws,w.length ≤P):
    (history ws).length ≤2*(P+1)*ws.length:=by
  induction ws with
  | nil=>exact le_rfl
  | cons w ws ih=>
    have h:=hw w List.mem_cons_self
    have ht:=ih (fun v hv=>hw v (List.mem_cons_of_mem w hv))
    dsimp only [history] at ht
    simp only [history,List.flatMap_cons,List.length_append,row,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
    nlinarith only [h,ht]
/-- The complete REAL output history is bounded using exact individual reduced widths, with no aggregate-lift substitution. -/
theorem lifted_history_length (p:List Bool) (ws:List (List Bool)) (zeros:Nat):
    (history (lifted p ws zeros)).length ≤2*(bitValue p+1)*(ws.length+zeros):=by
  have hh:=history_length_le (lifted p ws zeros) (bitValue p) (by
    intro word hw
    obtain ⟨v,_,rfl⟩:=List.mem_map.mp hw
    exact SemiprimeD1JetScalarBits.reduce_length _ _)
  simpa only [lifted,List.length_map,List.length_append,List.length_replicate] using hh
end RiemannGaussian.SemiprimeD1StackChildTableEntryLoopCost

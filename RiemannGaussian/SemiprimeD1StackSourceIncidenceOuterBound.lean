/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceOuter
import RiemannGaussian.SemiprimeD1StackSourceIncidenceInnerBound
/-! # Own complete ordered-pair clock under a physical total-growth ceiling -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceOuterBound
open SemiprimeD1StackSourceIncidenceEncoding SemiprimeD1StackSourceIncidenceOuter
open SemiprimeD1StackSourceIncidenceInner SemiprimeD1StackSourceIncidenceInnerBound
open SemiprimeD1StackSourceIncidenceBytes
/-- One complete physical outer iteration includes its whole inner scan and all actual source-copy/parse/cleanup bytes. -/
def outerCeiling (i:Inputs) (B:Nat) :Nat :=(i.rows.length+1)*ceiling i B+100*(inputSize i+1)
/-- Complete actual outer clock retains the exact M² multiplicity and charges total growth in the same run. -/
theorem outerClock_le (i:Inputs) (B:Nat) (rows:List (List Bool×List Bool)) :∀acc,
    (∀row∈rows,row.1.length ≤ inputSize i ∧ row.2.length ≤ inputSize i)→
    acc.length+rows.length*i.rows.length*rowWidth i ≤ B→
    outerClock i rows acc ≤ (rows.length+1)*outerCeiling i B :=by
  induction rows with
  | nil=>
    intro acc _ _
    simp only [outerClock,List.length_nil,Nat.zero_add,Nat.one_mul]
    unfold outerCeiling
    omega
  | cons row rows ih=>
    rcases row with ⟨lo,lf⟩
    intro acc hrows hcap
    have hr:=hrows (lo,lf) List.mem_cons_self
    change lo.length ≤ inputSize i ∧ lf.length ≤ inputSize i at hr
    have hh:∀row∈rows,row.1.length ≤ inputSize i ∧ row.2.length ≤ inputSize i:=
      fun row h=>hrows row (List.mem_cons_of_mem _ h)
    let next:=Spec.inner i.ids i.square i.cube i.fourth (lo,lf) i.rows acc
    have hg:=Spec.inner_length i.ids i.square i.cube i.fourth (lo,lf) i.rows acc
    change next.length ≤ acc.length+i.rows.length*rowWidth i at hg
    have hinner:acc.length+i.rows.length*rowWidth i ≤ B:=by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hcap
      omega
    have hcap':next.length+rows.length*i.rows.length*rowWidth i ≤ B:=by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hcap
      omega
    have hi:=ih next hh hcap'
    have h0:=innerClock_le i lo lf hr.1 hr.2 B i.rows acc (fun row h=>endpoint_widths i row h) hinner
    have ht:=(basic_bounds i).1
    have hother:8*(lo.length+lf.length)+17+(5*(tape i).length+4)+1+((lo.length+1)+(lf.length+1)) ≤
        100*(inputSize i+1):=by omega
    have hbody:8*(lo.length+lf.length)+17+(5*(tape i).length+4)+innerClock i lo lf i.rows acc+
        1+((lo.length+1)+(lf.length+1)) ≤ outerCeiling i B:=by
      unfold outerCeiling
      omega
    dsimp only [outerClock]
    change 8*(lo.length+lf.length)+17+(5*(tape i).length+4)+innerClock i lo lf i.rows acc+
      1+((lo.length+1)+(lf.length+1))+outerClock i rows next ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hi ⊢
    omega
end RiemannGaussian.SemiprimeD1StackSourceIncidenceOuterBound

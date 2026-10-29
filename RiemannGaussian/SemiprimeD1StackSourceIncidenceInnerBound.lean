/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceInner
import RiemannGaussian.SemiprimeD1StackSourceIncidenceBytes
/-! # Own inner-scan clock from physical source bytes and actual accumulator growth -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceInnerBound
open SemiprimeD1StackSourceIncidenceEncoding SemiprimeD1StackSourceIncidenceInner
open SemiprimeD1StackSourceIncidenceAddition SemiprimeD1StackSourceIncidenceBytes
open SemiprimeBitArithmetic (addBits)
namespace Spec
export SemiprimeD1StackSourceIncidenceSpec (term inner payload payload_length add_length inner_length)
end Spec
/-- A fixed physical-per-pair allowance for every actual total up to the proved byte ceiling B. -/
def ceiling (i:Inputs) (B:Nat) :Nat :=100000*(inputSize i)^2+100*(B+inputSize i+1)
/-- Every selected count payload has actual width no larger than the acquired three-power byte mass. -/
theorem term_length (i:Inputs) (left right:List Bool×List Bool) :
    (Spec.term i.ids i.square i.cube i.fourth left right).length ≤ inputSize i :=by
  have h:=Spec.payload_length i.square i.cube i.fourth
    (SemiprimeD1StackSourceIncidenceSpec.edge i.ids left.1 right.1)
    (SemiprimeD1StackSourceIncidenceSpec.edge i.ids left.2 right.2)
  exact h.trans (basic_bounds i).2.2.1
/-- One actual ripple sum consumes at most the actual power mass plus one additional bit of growth. -/
theorem accumulator_growth (i:Inputs) (left right:List Bool×List Bool) (acc:List Bool) :
    (addBits acc (Spec.term i.ids i.square i.cube i.fourth left right) false).bits.length ≤ acc.length+rowWidth i :=by
  have h0:=Spec.add_length acc (Spec.term i.ids i.square i.cube i.fourth left right)
  have h1:=Spec.payload_length i.square i.cube i.fourth
    (SemiprimeD1StackSourceIncidenceSpec.edge i.ids left.1 right.1)
    (SemiprimeD1StackSourceIncidenceSpec.edge i.ids left.2 right.2)
  change (Spec.term i.ids i.square i.cube i.fourth left right).length ≤ _ at h1
  unfold rowWidth
  omega
/-- The complete actual inner clock is bounded at every remaining suffix by the same physical growth ceiling. -/
theorem innerClock_le (i:Inputs) (lo lf:List Bool) (hlo:lo.length ≤ inputSize i) (hlf:lf.length ≤ inputSize i)
    (B:Nat) (rows:List (List Bool×List Bool)) :∀acc,
    (∀row∈rows,row.1.length ≤ inputSize i ∧ row.2.length ≤ inputSize i)→
    acc.length+rows.length*rowWidth i ≤ B→
    innerClock i lo lf rows acc ≤ (rows.length+1)*ceiling i B :=by
  induction rows with
  | nil=>
    intro acc _ _
    simp only [innerClock,List.length_nil,Nat.zero_add,Nat.one_mul]
    unfold ceiling
    omega
  | cons row rows ih=>
    rcases row with ⟨ro,rf⟩
    intro acc hrows hcap
    have hr:=hrows (ro,rf) List.mem_cons_self
    have hh:∀row∈rows,row.1.length ≤ inputSize i ∧ row.2.length ≤ inputSize i:=
      fun row h=>hrows row (List.mem_cons_of_mem _ h)
    let word:=Spec.term i.ids i.square i.cube i.fourth (lo,lf) (ro,rf)
    let next:=(addBits acc word false).bits
    have hg:=accumulator_growth i (lo,lf) (ro,rf) acc
    change next.length ≤ acc.length+rowWidth i at hg
    have hacc:acc.length ≤ B:=by omega
    have hcap':next.length+rows.length*rowWidth i ≤ B:=by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hcap
      omega
    have hi:=ih next hh hcap'
    have ht:=termClock_le i lo lf ro rf hlo hlf hr.1 hr.2
    have hs:=sumTime_le acc word
    have hw:=term_length i (lo,lf) (ro,rf)
    change word.length ≤ inputSize i at hw
    have hbody:8*(ro.length+rf.length)+17+pairClock i lo lf ro rf acc ≤ ceiling i B:=by
      change 8*(ro.length+rf.length)+17+
        (SemiprimeD1StackSourceIncidenceTerm.termClock i lo lf ro rf+sumTime acc word+ro.length+1+(rf.length+1)) ≤ _
      unfold ceiling
      nlinarith only [ht,hs,hw,hr.1,hr.2,hacc]
    dsimp only [innerClock]
    change 8*(ro.length+rf.length)+17+pairClock i lo lf ro rf acc+innerClock i lo lf rows next ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hi ⊢
    omega
end RiemannGaussian.SemiprimeD1StackSourceIncidenceInnerBound

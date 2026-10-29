/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildVertexChoiceSpec
/-! # Complete eight-word source: activity pop through actual enclosing halt -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildVertexChoiceSource
open SemiprimeD1StackChildVertexChoice SemiprimeD1StackChildVertexChoiceSpec
open SemiprimeD1StackChildVertexChoiceExecution
variable {d : ℕ}
/-- Same whole literal169-source run; the inactive constructor derives its own new dimensions. -/
theorem source_run (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) (bit : Bool) :
    ∃t≤timeBound old extra oldp newp parent order ports bit,
      SemiprimeD1StackCalls.run program t (originalInitial old extra oldp newp parent order ports bit)=
        some (done old extra oldp newp parent order ports bit) := by
  cases bit
  · have hn:=SemiprimeD1StackChildTableEntryOriginal.appended_positive old.axes extra ho he
    obtain ⟨t,ht,hr⟩:=SemiprimeD1StackChildUnitVertexBounds.source_run_bounded (extra++old.axes) hn newp
    refine ⟨t+3,?_,?_⟩
    · change t+3≤UB.polynomial (extra++old.axes) newp+3
      omega
    · exact inactive_run _ _ _ _ _ _ _ t _ rfl rfl hr
  · obtain ⟨t,ht,hr⟩:=SemiprimeD1StackChildLiftVertexBounds.source_run_bounded
      old ho extra he oldp newp hp parent hg order ports
    refine ⟨t+3,?_,?_⟩
    · change t+3≤AB.polynomial old extra oldp newp parent order ports+3
      omega
    · exact active_run _ _ _ _ _ _ _ t _ rfl rfl hr
/-- The real inactive inclusion does not touch an unshared active word. -/
theorem inactive_foreign (a : A.Stack→List Bool) (u : U.Stack→List Bool) (k : A.Stack)
    (ha : k≠newAxes) (hp : k≠newPrecision) (hr : k≠A.aux .record) (hs : k≠A.aux .scratch) :
    SemiprimeD1StackChildVertexChoiceView.inactiveResult a u (active k)=a k := by
  rw [SemiprimeD1StackChildVertexChoiceView.inactive_outside]
  · rfl
  · intro i hi
    unfold inactive at hi
    split_ifs at hi <;> simp_all [active,output,inactiveWork]
/-- The actually popped activity tape is empty at the end in both branches. -/
theorem activity_empty (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) (bit : Bool) :
    (done old extra oldp newp parent order ports bit).data activity=[] := by
  cases bit
  · change SemiprimeD1StackChildVertexChoiceView.inactiveResult
      (AO.originalInitial old extra oldp newp parent order ports).data
      (UO.done (extra++old.axes) newp).data activity=[]
    rw [SemiprimeD1StackChildVertexChoiceView.inactive_outside]
    · rfl
    · intro k h
      unfold inactive at h
      split_ifs at h <;> cases h
  · rfl
end RiemannGaussian.SemiprimeD1StackChildVertexChoiceSource

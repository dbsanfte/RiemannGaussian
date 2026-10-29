/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildVertexChoiceExecution
/-! # Original operand banks and the exact whole branch result
All dimensions, tables and the activity below are proof-side source descriptions.
The program accepts only the seven acquired words and one actual singleton bit.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildVertexChoiceSpec
open SemiprimeD1StackChildVertexChoice SemiprimeD1StackChildVertexChoiceView
open SemiprimeD1StackChildVertexChoiceExecution
open SemiprimeD1TensorTapeCodec (tape vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace AO
export SemiprimeD1StackChildLiftVertexOriginal (originalInitial done)
end AO
namespace UO
export SemiprimeD1StackChildUnitVertexOriginal (originalInitial done)
end UO
namespace AB
export SemiprimeD1StackChildLiftVertexBounds (resource polynomial)
end AB
namespace UB
export SemiprimeD1StackChildUnitVertexBounds (resource polynomial)
end UB
variable {d : ℕ}
/-- The seven original words and one actual activity bit are present before either constructor runs. -/
def originalInitial (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) (bit : Bool) : C.State Stack Label:=
  initial (tape parent) (SemiprimeD1StackChildTableEntryPrepare.orderTape order)
    (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp
    (vectorBits (ports.map unary)) [bit]
/-- Full actual stopped bank in either physical branch. -/
noncomputable def result (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) (bit : Bool) : Stack→List Bool:=
  if bit then activeResult (AO.done old extra oldp newp parent order ports).data
  else inactiveResult (AO.originalInitial old extra oldp newp parent order ports).data
    (UO.done (extra++old.axes) newp).data
/-- Actual whole halt clears both flags and all saved return cells. -/
noncomputable def done (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) (bit : Bool) : C.State Stack Label:=
  stopped (result old extra oldp newp parent order ports bit)
/-- Both independent acquired-rank/precision VALUE resources are paid without an elapsed-clock operand. -/
def resource (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) : ℕ:=
  AB.resource old extra oldp newp parent order ports+UB.resource (extra++old.axes) newp+1
/-- Own exact branch envelope counts the physical pop, call and final halt. -/
def timeBound (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) (bit : Bool) : ℕ:=
  (if bit then AB.polynomial old extra oldp newp parent order ports
    else UB.polynomial (extra++old.axes) newp)+3
/-- Both source resources and the literal flag fit in one common positive source resource. -/
theorem resource_bounds (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) :
    1≤resource old extra oldp newp parent order ports ∧
    AB.resource old extra oldp newp parent order ports≤resource old extra oldp newp parent order ports ∧
    UB.resource (extra++old.axes) newp+1≤resource old extra oldp newp parent order ports := by
  unfold resource;omega
/-- Exact inactive output projection, including the fixed-zero-precision convention. -/
theorem inactive_output (a : A.Stack→List Bool) (u : U.Stack→List Bool) :
    inactiveResult a u output=u (U.aux .record) := by
  change inactiveResult a u (inactive (U.aux .record))=u (U.aux .record)
  exact inactive_project a u _
/-- All four displaced input/output allocations remain counted and physically empty. -/
theorem inactive_shadows (a : A.Stack→List Bool) (u : U.Stack→List Bool) (k : U.Stack) (hk : shared k) :
    inactiveResult a u (inactiveWork k)=[] := by
  rw [inactive_outside]
  · simp only [activeResult,bank,inactiveWork,Sum.elim_inr,Sum.elim_inl,ite_eq_left hk]
  · intro i hi
    unfold inactive at hi
    split_ifs at hi <;> simp_all [inactiveWork,active,output,shared]
end RiemannGaussian.SemiprimeD1StackChildVertexChoiceSpec

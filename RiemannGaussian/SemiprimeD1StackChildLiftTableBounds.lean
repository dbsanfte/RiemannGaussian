/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftTableOriginal
import RiemannGaussian.SemiprimeD1StackChildLiftTableResources
/-! # Closed whole-table physical cost in actual bytes and acquired dimension VALUES
The full source costs a fixed quadratic per actual assignment. This includes
every repeated parent-table scan, individual integer lift, actual template
copy, source cleanup, scope scan, tree tag, real return and final reversal.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftTableBounds
open SemiprimeD1StackChildLiftTable
open SemiprimeD1TensorTapeCodec (tape vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace R
export SemiprimeD1StackChildLiftTableResources (resource resource_pos scope_le template_bytes entry_budget)
end R
namespace O
export SemiprimeD1StackChildLiftTableOriginal (original answer done timeBound)
end O
namespace Input
export SemiprimeD1StackChildLiftTableInput (budget raw_empty source_trace)
end Input
/-- One fixed coefficient/degree precedes ALL original table/context/scope input instances. -/
def polynomial {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) (scope : List (List Bool)) : ℕ :=
  10^20*(R.resource old extra oldp newp parent order scope)^2*2^scope.length
/-- SAME source's actual whole clock has a quadratic physical-resource cap per assignment. -/
theorem timeBound_le {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) (scope : List (List Bool)) :
    O.timeBound old extra oldp newp parent order scope≤polynomial old extra oldp newp parent order scope := by
  let r := R.resource old extra oldp newp parent order scope
  have hr : 1≤r := R.resource_pos old extra oldp newp parent order scope
  have hi := R.template_bytes old extra oldp newp parent order scope
  have hn := R.scope_le old extra oldp newp parent order scope
  have hb := R.entry_budget old extra oldp newp parent order scope
  change SemiprimeD1StackVectorTableSpec.inputBytes (O.original old extra oldp newp parent order)≤61*r at hi
  change scope.length≤r at hn
  change Input.budget old extra oldp newp parent order scope.length≤10^8*r^2 at hb
  have hs : (vectorBits scope).length≤r := Nat.le_add_left _ _
  have hp : r≤r^2 := Nat.le_pow (by decide : 0<2)
  have h1 : 1≤r^2 := Nat.one_le_pow _ _ hr
  dsimp only [O.timeBound,SemiprimeD1StackVectorTableBounds.runBound,
    SemiprimeD1StackVectorTableDFS.weight,SemiprimeD1StackVectorTableLeaf.leafBound,polynomial]
  apply Nat.mul_le_mul_right (2^scope.length)
  rw [E.stack_card,show source.roles.length=61 from roles_length]
  change _≤10^20*r^2
  omega
/-- SAME complete fixed source, exact whole original table bytes and closed own bit-operation budget. -/
theorem source_run_bounded {d : ℕ} (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order : List ℕ) (scope : List (List Bool)) :
    ∃t ≤ polynomial old extra oldp newp parent order scope,
      SemiprimeD1StackCalls.run program t
        (initial (tape parent) (SemiprimeD1StackChildTableEntryPrepare.orderTape order)
          (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp (vectorBits scope))=
      some (O.done old extra oldp newp parent order scope) ∧
      (O.done old extra oldp newp parent order scope).data (SemiprimeD1StackVectorTable.aux .output)=
        tape (SemiprimeD1StackChildLiftTableMeaning.table old extra (SemiprimeBitArithmetic.bitValue newp)
          scope.length parent order) := by
  obtain ⟨t,ht,hr,hout⟩ := SemiprimeD1StackChildLiftTableOriginal.source_run old ho extra he oldp newp hp parent hg order scope
  exact ⟨t,ht.trans (timeBound_le old extra oldp newp parent order scope),hr,hout⟩
/-- Genuine compiled134-role source has this SAME prepared input, output and closed whole time. -/
noncomputable def machineSource {d : ℕ} (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order : List ℕ) (scope : List (List Bool)) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (initial (tape parent) (SemiprimeD1StackChildTableEntryPrepare.orderTape order)
          (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp (vectorBits scope)))
      (some (SemiprimeD1StackCalls.configuration (O.done old extra oldp newp parent order scope)))
      (polynomial old extra oldp newp parent order scope) := by
  apply SemiprimeD1StackCalls.evalsCorrect (SemiprimeD1StackVectorTable.counter .bank)
    (SemiprimeD1StackVectorTable.aux .output) .start program
  let h := source_run_bounded old ho extra he oldp newp hp parent hg order scope
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2.1⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackChildLiftTableBounds

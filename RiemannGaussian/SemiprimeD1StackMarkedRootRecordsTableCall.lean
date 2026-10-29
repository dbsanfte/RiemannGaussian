/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsCalls
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRowView
/-! # Whole144 source physically aliased to the parsed original unary port tape -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTableCall
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsView
open SemiprimeD1StackMarkedRootRecordsTableView SemiprimeD1StackMarkedRootRecordsRowView
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Changing private table words preserves every actual foreign role, including both source banks. -/
theorem table_foreign (r : R.Stack → List Bool) (v : V.Stack → List Bool)
    (before after : T.Stack → List Bool) (a : Aux → List Bool) (k : Stack)
    (hk : ∀ j, tableStack j≠k) : data r v after a k=data r v before a k := by
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · by_cases h : k=tableNumber
        · subst k;rfl
        · exact False.elim (hk k (by simp only [tableStack,h,ite_false,tablePrivate]))
      · rfl
/-- Actual completed144 source, preserving original ports, caches and all callers' other words.
The payload words are arbitrary; in particular actual UNARY numeric port fields are allowed. -/
theorem table_run (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits indexWord : List Bool)
    (sideBit : Bool) (scope : List (List Bool)) (w : Work)
    (hn : r R.originalInput=bits) (hb : bits≠[]) :
    ∃ t ≤ SemiprimeD1StackMarkedPublicInputTableExecution.runBound bits indexWord sideBit scope+1,
      Runs program t (ctl .inputTable)
        (view r v bits {indexWord := indexWord,sideWord := [sideBit],portsWord := vectorBits scope} w)
        (ctl .log)
        (view r v bits {indexWord := indexWord,sideWord := [sideBit],portsWord := vectorBits scope,countWord := List.replicate scope.length true,tableWord := SemiprimeD1StackMarkedPublicInputTableExecution.outputTape bits indexWord sideBit scope} w) := by
  apply SemiprimeD1StackMarkedRootRecordsCalls.table_call bits indexWord sideBit scope hb
  · constructor
    · intro k
      rw [view_table r v bits _ w hn k]
      exact (congrFun (initial_table bits indexWord sideBit (vectorBits scope)) k).symm
    · intro k _;rfl
  · constructor
    · intro k
      rw [view_table r v bits _ w hn k]
      exact (congrFun (result_table bits indexWord sideBit scope) k).symm
    · intro k hk
      exact table_foreign r v _ _ (words w) k hk
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTableCall

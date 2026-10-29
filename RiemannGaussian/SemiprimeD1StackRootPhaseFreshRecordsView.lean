/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsCalls
/-! # Literal original root header, exact four-word client input and physical work updates -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsView
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsPrimitives
/-- Before the real client call, exactly the acquired heap/count/reference and old header exist. -/
theorem input_only (hp cn ref axes:List Bool) (k:Q.Stack) :
    SemiprimeD1StackPhaseCacheFresh.input hp cn ref axes k=
      if k=I.sourceHeap then hp else if k=I.sourceCounter then cn
      else if k=I.sourceReference then ref else if k=I.oldHeader then axes else [] :=by
  rcases k with k|k
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rcases k with k|k
          · cases k <;> rfl
          · rcases k with k|k
            · cases k <;> rfl
            · fin_cases k <;> rfl
        · rcases k with k|k
          · rcases k with k|k
            · cases k <;> rfl
            · rcases k with k|k
              · cases k <;> rfl
              · fin_cases k <;> rfl
          · cases k <;> rfl
    · cases k <;> rfl
/-- The private bank initially contains only the actual old-axis header; all142 other addresses are empty. -/
theorem private_input (hp cn ref axes:List Bool) (k:Q.Stack) :
    privateCache (SemiprimeD1StackPhaseCacheFresh.input hp cn ref axes) k=
      if k=I.oldHeader then axes else [] :=by
  rw [privateCache,input_only]
  by_cases h0:k=I.sourceHeap
  · subst k;simp only [true_or,ite_true];rfl
  · by_cases h1:k=I.sourceCounter
    · subst k;simp only [or_true,true_or,ite_true];rfl
    · by_cases h2:k=I.sourceReference
      · subst k;simp only [or_true,ite_true];rfl
      · simp only [h0,h1,h2,or_false,ite_false]
/-- Persistent old-axis bytes are preserved by the actual context/cache result on both outcomes. -/
theorem completed_header (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hp cn ref:List Bool) :
    SemiprimeD1StackPhaseCacheFreshComponents.completed a u edges t p axes hp cn ref I.oldHeader=
      SemiprimeD1StackPhaseChildContextPrimitives.header axes :=by
  change (if SemiprimeD1StackPhaseChildContextArithmetic.good a u edges t then
    SemiprimeD1StackPhaseChildContextPrimitives.contextResult axes p else
    SemiprimeD1StackPhaseChildContext.oldInput (SemiprimeD1StackPhaseChildContextPrimitives.header axes))
      SemiprimeD1StackJetContext.axesCache=_
  split <;> rfl
/-- One physical reader write changes its actual auxiliary word alone. -/
theorem update_reader (root:R.Stack→List Bool) (q:Q.Stack→List Bool)
    (reader currentRecord heap counter reference history output next:List Bool) :
    Function.update (view root q (work reader currentRecord heap counter reference history output)) (aux .reader) next=
      view root q (work next currentRecord heap counter reference history output) :=by
  rw [update_aux _ _ _ _ (by decide)]
  congr 1
  funext k
  cases k <;> rfl
/-- One physical currentRecord write changes its actual auxiliary word alone. -/
theorem update_currentRecord (root:R.Stack→List Bool) (q:Q.Stack→List Bool)
    (reader currentRecord heap counter reference history output next:List Bool) :
    Function.update (view root q (work reader currentRecord heap counter reference history output)) (aux .record) next=
      view root q (work reader next heap counter reference history output) :=by
  rw [update_aux _ _ _ _ (by decide)]
  congr 1
  funext k
  cases k <;> rfl
/-- One physical heap write changes its actual auxiliary word alone. -/
theorem update_heap (root:R.Stack→List Bool) (q:Q.Stack→List Bool)
    (reader currentRecord heap counter reference history output next:List Bool) :
    Function.update (view root q (work reader currentRecord heap counter reference history output)) (aux .heap) next=
      view root q (work reader currentRecord next counter reference history output) :=by
  rw [update_aux _ _ _ _ (by decide)]
  congr 1
  funext k
  cases k <;> rfl
/-- One physical counter write changes its actual auxiliary word alone. -/
theorem update_counter (root:R.Stack→List Bool) (q:Q.Stack→List Bool)
    (reader currentRecord heap counter reference history output next:List Bool) :
    Function.update (view root q (work reader currentRecord heap counter reference history output)) (aux .counter) next=
      view root q (work reader currentRecord heap next reference history output) :=by
  rw [update_aux _ _ _ _ (by decide)]
  congr 1
  funext k
  cases k <;> rfl
/-- One physical reference write changes its actual auxiliary word alone. -/
theorem update_reference (root:R.Stack→List Bool) (q:Q.Stack→List Bool)
    (reader currentRecord heap counter reference history output next:List Bool) :
    Function.update (view root q (work reader currentRecord heap counter reference history output)) (aux .reference) next=
      view root q (work reader currentRecord heap counter next history output) :=by
  rw [update_aux _ _ _ _ (by decide)]
  congr 1
  funext k
  cases k <;> rfl
/-- One physical history write changes its actual auxiliary word alone. -/
theorem update_history (root:R.Stack→List Bool) (q:Q.Stack→List Bool)
    (reader currentRecord heap counter reference history output next:List Bool) :
    Function.update (view root q (work reader currentRecord heap counter reference history output)) (aux .refsHistory) next=
      view root q (work reader currentRecord heap counter reference next output) :=by
  rw [update_aux _ _ _ _ (by decide)]
  congr 1
  funext k
  cases k <;> rfl
/-- One physical output write changes its actual auxiliary word alone. -/
theorem update_output (root:R.Stack→List Bool) (q:Q.Stack→List Bool)
    (reader currentRecord heap counter reference history output next:List Bool) :
    Function.update (view root q (work reader currentRecord heap counter reference history output)) (aux .refsOutput) next=
      view root q (work reader currentRecord heap counter reference history next) :=by
  rw [update_aux _ _ _ _ (by decide)]
  congr 1
  funext k
  cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsView

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootInputView
/-! # Real original-input handoff, with its exact preserving-copy trace -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedRootInputPrimitives
open SemiprimeD1StackPackedRootInput SemiprimeD1StackPackedRootInputEncoding
open SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Actual component fragments concatenate with all external real return frames retained. -/
theorem join {m n : ℕ} {pc mid next : Label} {before between after : Stack→List Bool}
    (h : Runs program m pc before mid between) (g : Runs program n mid between next after) :
    Runs program (m+n) pc before next after := runs_trans program m n pc mid next before between after h g
/-- One literal restoring copy, without an operand getter or supplied context word. -/
theorem copy_call (before : Stack→List Bool) (xs ys : List Bool)
    (hx : before originalInput=xs) (hy : before (contextStack J.originalInput)=ys)
    (hs : before (rootStack R.copyScratch)=[]) :
    Runs program (5*xs.length+4) (.local .copyNumber) before (.local .context)
      (Function.update before (contextStack J.originalInput) (xs++ys)) := by
  let start:=SemiprimeD1StackCopy.state 0 none xs ys []
  let stop:=SemiprimeD1StackCopy.done xs (xs++ys)
  have hi : Link.DataRel copyStack before start.store before := by
    constructor
    · intro k
      fin_cases k
      · exact hx
      · exact hy
      · exact hs
    · intro k _
      rfl
  have ho:=Link.data_update copyStack copy_injective before start.store before hi (1 : Fin 3) (xs++ys)
  have he : Function.update start.store 1 (xs++ys)=stop.store := by
    funext k
    fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program copyStack Label.copy copy_injective SemiprimeD1StackCopy.code 0
    (fun _ => rfl) (.local .copyNumber) (.local .context) rfl (5*xs.length+3) start stop before _ rfl rfl
    (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- The actual retained N, actual empty target and actual empty scratch discharge all copy premises. -/
theorem copy_N (bits : List Bool) (hN : 0<SemiprimeBitArithmetic.bitValue bits) :
    Runs program (5*bits.length+4) (.local .copyNumber) (markedReady bits hN)
      (.local .context) (contextReady bits hN) := by
  have h:=copy_call (markedReady bits hN) bits [] (marked_N bits hN) rfl (marked_scratch bits hN)
  simpa only [List.append_nil,contextReady_copy] using h
end RiemannGaussian.SemiprimeD1StackPackedRootInputPrimitives

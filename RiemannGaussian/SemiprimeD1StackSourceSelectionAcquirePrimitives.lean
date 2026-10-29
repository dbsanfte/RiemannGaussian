/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireView
/-! # Actual acquisition-handoff copies with their own physical calls and returns -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectionAcquirePrimitives
open SemiprimeD1StackSourceSelectionAcquire SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Actual fragments concatenate with all external real return frames retained. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=runs_trans program m n pc mid next before between after h g
/-- Every cache/input handoff is a real preserving copy, not a semantic operand assignment. -/
theorem copy_call (site:Copy) (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (copySource site)=xs) (hy:before (copyTarget site)=ys) (hs:before copyScratch=[]) :
    Runs program (5*xs.length+4) (ctl (.copy site)) before (copyNext site)
      (Function.update before (copyTarget site) (xs++ys)) :=by
  let start:=SemiprimeD1StackCopy.state 0 none xs ys []
  let stop:=SemiprimeD1StackCopy.done xs (xs++ys)
  have hi:Link.DataRel (copyStack site) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (copyStack site) (copy_injective site) before start.store before hi (1:Fin 3) (xs++ys)
  have he:Function.update start.store 1 (xs++ys)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (copyStack site) (Label.copy site) (copy_injective site) SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (ctl (.copy site)) (copyNext site) rfl (5*xs.length+3) start stop before _ rfl rfl
    (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
end RiemannGaussian.SemiprimeD1StackSourceSelectionAcquirePrimitives

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootContextEncoding
/-! # Actual derived-precision copy with its own physical call and return -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedRootContextPrimitives
open SemiprimeD1StackPackedRootContext SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Actual fragments concatenate with all external real return frames retained. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=runs_trans program m n pc mid next before between after h g
/-- Actual preserving copy of the derived binary precision, including restoring scratch and the real return. -/
theorem copy_call (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (copyStack 0)=xs) (hy:before (copyStack 1)=ys) (hs:before (copyStack 2)=[]) :
    Runs program (5*xs.length+4) (ctl .copyPrecision) before (ctl .seedAxes)
      (Function.update before (copyStack 1) (xs++ys)) :=by
  let start:=SemiprimeD1StackCopy.state 0 none xs ys []
  let stop:=SemiprimeD1StackCopy.done xs (xs++ys)
  have hi:Link.DataRel copyStack before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update copyStack copy_injective before start.store before hi (1:Fin 3) (xs++ys)
  have he:Function.update start.store 1 (xs++ys)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program copyStack copyLabel copy_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (ctl .copyPrecision) (ctl .seedAxes) rfl (5*xs.length+3) start stop before _ rfl rfl
    (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- Literal empty-axis header seed pays its actual FALSE-cell push. -/
theorem axes_seed (before:Stack→List Bool):
    Runs program 1 (ctl .seedAxes) before (ctl .acquireContext)
      (Function.update before (context J.axesCache) (false::before (context J.axesCache))) :=
  one_base program _ _ _ _ _ rfl rfl rfl
end RiemannGaussian.SemiprimeD1StackPackedRootContextPrimitives

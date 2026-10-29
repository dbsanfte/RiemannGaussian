/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseProjection
/-! # Actual restored phase flag, retaining every source/cache field -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseGuard
open SemiprimeD1StackCachePhase SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- One real peek selects the original phase branch without consuming its retained flag. -/
theorem guard_run (before:Stack→List Bool) (b:Bool) (hb:before phaseValid=[b]) :
    Runs program 1 (ctl .check) before (if b then ctl (.copy .newAxes) else ctl .reject) before :=by
  apply one_base program (ctl .check) _
    (.peek phaseValid (ctl .reject) (ctl .reject) (ctl (.copy .newAxes))) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose (ctl .reject) (ctl .reject)
      (ctl (.copy .newAxes)) (before phaseValid).head?)=_
    rw [hb]
    cases b <;> rfl
  · rfl
end RiemannGaussian.SemiprimeD1StackCachePhaseGuard

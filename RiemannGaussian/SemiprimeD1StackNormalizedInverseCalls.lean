/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInversePrimitives
/-! # Actual complete fitted R36 call inside the fixed inverse program -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseCalls
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackProcedureTrace
namespace PTrace
export SemiprimeD1StackNormalizedInversePrimitives (join copy_call push_run pop_run peek_run drain_loop frame_call field_read local_call)
end PTrace
/-- R36 reads the four actually copied fields and retained W; every foreign inverse word is retained. -/
theorem rational_call (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hi:w.rational=SemiprimeD1StackRationalOperation.input (sx::xn) xd (sy::yn) yd width) :
    Runs program (SemiprimeD1StackRationalOperationExecution.runBound (operation site) sx xn xd sy yn yd width+1)
      (.operation site .run) (store w) (.operation site (.clearDestination false))
      (store {w with rational:=SemiprimeD1StackRationalOperationExecution.result (operation site) sx xn xd sy yn yd width}):=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rational Label.rational rational_injective R.program
    (SemiprimeD1StackRationalOperation.localLabel .start (operation site) false false) (fun _=>rfl)
    (.operation site .run) (.operation site (.clearDestination false)) rfl _
    (SemiprimeD1StackRationalOperation.initial (operation site) (sx::xn) xd (sy::yn) yd width)
    (SemiprimeD1StackRationalOperationExecution.done (operation site) sx xn xd sy yn yd width) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackRationalOperationExecution.source_run (operation site) sx xn xd sy yn yd width)
  · constructor
    · intro slot;exact congrFun hi slot
    · intro slot _;rfl
  · constructor
    · intro slot;rfl
    · intro role hk;rcases role with role|role
      · exact (hk role rfl).elim
      · rfl
end RiemannGaussian.SemiprimeD1StackNormalizedInverseCalls

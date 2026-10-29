/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearView
/-! # Exact retained29-role restoring-division views and updates -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearDivisionView
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearView
/-- Complete division preparation/result bank; all other divider work is empty. -/
def divisionData (w:Words) (input divisor remainder quotient:List Bool):Stack→List Bool:=
  bank (SemiprimeD1StackDivider.payload input divisor [] [] [] [] [] remainder quotient [] []) w
/-- Every unused arithmetic role is physically empty at these boundaries. -/
theorem divisionData_empty (w:Words):divisionData w [] [] [] []=data w:=by
  funext r;rcases r with r|r
  · rcases r with r|r <;> cases r <;> rfl
  · rfl
/-- Auxiliary updates preserve the actual whole eleven-role divider bank. -/
theorem divisionData_aux_update (w:Words) (input divisor remainder quotient:List Bool) (role:Aux) (value:List Bool):
    Function.update (divisionData w input divisor remainder quotient) (aux role) value=
      divisionData (SemiprimeD1StackKernelLinearView.set w role value) input divisor remainder quotient:=
  bank_aux_update _ _ _ _
/-- Exact actual dividend-copy update. -/
theorem divisionData_input_update (w:Words) (input divisor remainder quotient value:List Bool):
    Function.update (divisionData w input divisor remainder quotient) (divider (.inr .input)) value=
      divisionData w value divisor remainder quotient:=by
  funext r;rcases r with r|r
  · rcases r with r|r
    · cases r <;> rfl
    · cases r <;> rfl
  · rfl
/-- Exact actual divisor-copy update. -/
theorem divisionData_divisor_update (w:Words) (input divisor remainder quotient value:List Bool):
    Function.update (divisionData w input divisor remainder quotient) (divider (.inr .divisor)) value=
      divisionData w input value remainder quotient:=by
  funext r;rcases r with r|r
  · rcases r with r|r
    · cases r <;> rfl
    · cases r <;> rfl
  · rfl
/-- Exact actual quotient cleanup update. -/
theorem divisionData_quotient_update (w:Words) (input divisor remainder quotient value:List Bool):
    Function.update (divisionData w input divisor remainder quotient) (divider (.inr .quotient)) value=
      divisionData w input divisor remainder value:=by
  funext r;rcases r with r|r
  · rcases r with r|r
    · cases r <;> rfl
    · cases r <;> rfl
  · rfl
/-- Exact actual remainder cleanup update. -/
theorem divisionData_remainder_update (w:Words) (input divisor remainder quotient value:List Bool):
    Function.update (divisionData w input divisor remainder quotient) (divider (.inr .remainder)) value=
      divisionData w input divisor value quotient:=by
  funext r;rcases r with r|r
  · rcases r with r|r
    · cases r <;> rfl
    · cases r <;> rfl
  · rfl
end RiemannGaussian.SemiprimeD1StackKernelLinearDivisionView

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetRoute
import RiemannGaussian.SemiprimeD1StackProcedureInclusion
/-! # Included physical mixed-radix operand acquisition calls -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetRouteCalls
open SemiprimeD1StackJetRoute
namespace Trace
export SemiprimeD1StackProcedureTrace (Runs At included_call one_base runs_trans)
end Trace
local notation "ctl" => SemiprimeD1StackJetRoute.control

/-- Literal staging bank, with all unlisted work stacks physically empty. -/
def bank (axes records left right result radix q d quotLeft remLeft quotRight remRight valid : List Bool) : Stack→List Bool
  | .axes=>axes
  | .records=>records
  | .left=>left
  | .right=>right
  | .result=>result
  | .radix=>radix
  | .q=>q
  | .d=>d
  | .quotLeft=>quotLeft
  | .remLeft=>remLeft
  | .quotRight=>quotRight
  | .remRight=>remRight
  | .valid=>valid
  | _=>[]
@[simp] theorem bank_apply (axes records left right result radix q d quotLeft remLeft quotRight remRight valid: List Bool) (k : Stack) :
    bank axes records left right result radix q d quotLeft remLeft quotRight remRight valid k = match k with
    | .axes=>axes
    | .records=>records
    | .left=>left
    | .right=>right
    | .result=>result
    | .radix=>radix
    | .q=>q
    | .d=>d
    | .quotLeft=>quotLeft
    | .remLeft=>remLeft
    | .quotRight=>quotRight
    | .remRight=>remRight
    | .valid=>valid
    | _=>[] := rfl

theorem copy_injective (b : Bool) : Function.Injective (copyStack b) := by
  intro x y h
  cases b <;> fin_cases x <;> fin_cases y <;> simp_all [copyStack]

/-- The actual first index is copied once, preserving its original unary input. -/
theorem copy_left (axes left right : List Bool) :
    Trace.Runs code (5*left.length+4) (ctl .copyLeft)
      (bank axes [] left right [] [] [] [] [] [] [] [] [])
      (ctl .copyRight) (bank axes [] left right left [] [] [] [] [] [] [] []) := by
  have hr := SemiprimeD1StackCopy.copy_words left [] none
  apply Trace.included_call code (copyStack false) copyLeftLabel (copy_injective false)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (ctl .copyLeft) (ctl .copyRight) rfl
    (5*left.length+3) _ _ _ _ rfl rfl hr
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload]
    · intro k hk
      cases k <;> first | rfl | exact (hk 1 rfl).elim

/-- The second actual index is copied onto the retained first index. -/
theorem copy_right (axes left right result : List Bool) :
    Trace.Runs code (5*right.length+4) (ctl .copyRight)
      (bank axes [] left right result [] [] [] [] [] [] [] [])
      (ctl .suffixCall) (bank axes [] left right (right++result) [] [] [] [] [] [] [] []) := by
  have hr := SemiprimeD1StackCopy.copy_words right result none
  apply Trace.included_call code (copyStack true) copyRightLabel (copy_injective true)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (ctl .copyRight) (ctl .suffixCall) rfl
    (5*right.length+3) _ _ _ _ rfl rfl hr
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk 1 rfl).elim

theorem suffix_injective : Function.Injective suffixStack := by
  intro x y h
  cases x <;> cases y <;> simp_all [suffixStack]

/-- The closed route really calls the original-axis supplier; no acquired record
or rank is an input to this caller. The retained sum and indices are untouched. -/
theorem suffix_call (axes : List ℕ) (hp : ∀q∈axes,0<q) (left right result : List Bool) :
    ∃m≤100*(axes.length+1)*(axes.prod+1)+2,
      Trace.Runs code m (ctl .suffixCall)
        (bank (SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary))
          [] left right result [] [] [] [] [] [] [] [])
        (ctl .suffixDone)
        (bank [] (SemiprimeD1StackJetSuffixOriginal.recordTape axes 1 []) left right result
          (SemiprimeD1StackUnaryDivmod.unary axes.prod) [] [] [] [] [] [] [true]) := by
  obtain ⟨m,hm,hr⟩ := SemiprimeD1StackJetSuffixOriginal.acquire_run axes hp
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call code suffixStack suffixLabel suffix_injective
    SemiprimeD1StackJetSuffix.code (SemiprimeD1StackJetSuffix.control .vector) (fun _=>rfl)
    (ctl .suffixCall) (ctl .suffixDone) rfl m _ _ _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk .axes rfl).elim | exact (hk .radix rfl).elim | exact (hk .records rfl).elim | exact (hk .valid rfl).elim

end RiemannGaussian.SemiprimeD1StackJetRouteCalls

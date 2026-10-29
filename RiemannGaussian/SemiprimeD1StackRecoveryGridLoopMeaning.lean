/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridExecution
import RiemannGaussian.SemiprimeD1StackRecoveryGridOriginalStep
/-! # Exact legacy forward-order whole grid payload
Descending physical execution is the original forward-list right fold. Every
repeat and raw padded byte agrees; no old clock field is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridLoopMeaning
namespace Loop
export SemiprimeD1StackRecoveryGridLoop (iterate)
end Loop
namespace Old
export SemiprimeD1StackRecoveryGridOriginalStep (loop payload step_original)
export SemiprimeD1RecoveryGridBits (acquire)
export SemiprimeD1RecoveryScalarRun (indices_value)
export SemiprimeD1RecoveryWeightRun (geometry_size)
end Old
namespace Dec
export SemiprimeD1StackRecoveryGridDecrement (difference difference_value)
export SemiprimeD1StackRecoveryGridLoopPrimitives (difference_width)
end Dec
/-- Exact legacy list order: physical q=count−1 down to0 realizes the original forward range right fold. -/
theorem iterate_original (a M u selected count:Nat) (t q width:List Bool) (qs:List Nat)
    (ht:SemiprimeBitArithmetic.bitValue t=selected) (hselected:selected<2^(a+1))
    (hc:count≤2^(a+1)) (hl:q.length=a+2) (hv:SemiprimeBitArithmetic.bitValue q=count-1) :
    Loop.iterate a M u t width count q (Old.loop a M u selected width qs)=
      Old.loop a M u selected width (List.range count++qs):=by
  induction count generalizing q qs with
  | zero=>rfl
  | succ n ih=>
    have hq:SemiprimeBitArithmetic.bitValue q=n:=by omega
    have hn:n<2^(a+1):=by omega
    rw [Loop.iterate,Old.step_original a M u selected n t q width qs ht hselected hq hl hn]
    cases n with
    | zero=>rfl
    | succ n=>
      have hp:0<SemiprimeBitArithmetic.bitValue q:=by omega
      have hl':(Dec.difference q).length=a+2:=Dec.difference_width a q hl
      have hv':SemiprimeBitArithmetic.bitValue (Dec.difference q)=(n+1)-1:=by
        rw [Dec.difference_value q hp]
        omega
      rw [ih (Dec.difference q) ((n+1)::qs) (by omega) hl' hv']
      simp only [List.range_succ,List.append_assoc,List.cons_append,List.nil_append]
/-- All actual original five-input payload bytes equal the full original range fold. -/
theorem payload_original (a M u selected:Nat) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected) (hs:selected<2^(a+1)) :
    SemiprimeD1StackRecoveryGridExecution.payload a M u t width=
      Old.loop a M u selected width (List.range (2^(a+1))):=by
  have hl: (SemiprimeD1StackRecoveryGridExecution.firstWord a).length=a+2:=
    SemiprimeD1StackRecoveryGridFront.q_width a M u t width
  have hv:SemiprimeBitArithmetic.bitValue (SemiprimeD1StackRecoveryGridExecution.firstWord a)=2^(a+1)-1:=
    SemiprimeD1StackRecoveryGridFront.q_value a M u t width
  have h:=iterate_original a M u selected (2^(a+1)) t (SemiprimeD1StackRecoveryGridExecution.firstWord a) width [] ht hs le_rfl hl hv
  have hone:Old.loop a M u selected width []=SemiprimeD1StackRecoveryGridModel.one:=rfl
  rw [hone] at h
  simpa only [SemiprimeD1StackRecoveryGridExecution.payload,List.append_nil] using h
/-- Actual payload equals the authoritative acquire report's three grid fields for every original finite index and raw binary padding. -/
theorem acquire_payload (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) :
    SemiprimeD1StackRecoveryGridExecution.payload a M u t width=
      Old.payload (Old.acquire width a M u selected).grid:=by
  rw [payload_original a M u selected.val t width ht selected.isLt]
  change Old.loop a M u selected.val width (List.range (2^(a+1)))=
    Old.payload (SemiprimeD1RecoveryGridBits.loop width a (SemiprimeD1TaperedLoss.height M u) u selected.val
      (SemiprimeD1RecoveryWeightRun.geometry a selected.val)
      (SemiprimeD1StackRecoveryGridModel.center a width) (SemiprimeD1StackRecoveryGridModel.alpha a width)
      (SemiprimeD1RecoveryGridBits.index a selected.val).word
      (SemiprimeD1RecoveryScalarRun.indices (SemiprimeD1RecoveryWeightRun.geometry a selected.val).size).value)
  rw [Old.indices_value,Old.geometry_size]
  rfl
end RiemannGaussian.SemiprimeD1StackRecoveryGridLoopMeaning

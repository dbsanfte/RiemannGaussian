/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridLoopPrimitives
/-! # Whole actual decreasing grid loop with its own recursive trace budget
The iteration and budget below are proof invariants of the same fixed physical
program. The actual todo and binary q words determine every runtime branch.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridLoop
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackProcedureTrace
namespace Model
export SemiprimeD1StackRecoveryGridModel (Payload view)
end Model
namespace Row
export SemiprimeD1StackRecoveryGridRowMeaning (step)
export SemiprimeD1StackRecoveryGridRow (runBound)
end Row
namespace L
export SemiprimeD1StackRecoveryGridLoopPrimitives (row_view_run zeroWord zero_eq advance_zero advance_succ difference_width)
end L
namespace Dec
export SemiprimeD1StackRecoveryGridDecrement (difference difference_value runBound)
end Dec
/-- Chronological actual payload updates as physical q decreases; unused final subtraction is only a proof-side argument of zero iteration. -/
def iterate (a M u:Nat) (t width:List Bool) :Nat→List Bool→Model.Payload→Model.Payload
  | 0,_,p=>p
  | n+1,q,p=>iterate a M u t width n (Dec.difference q) (Row.step a M u t q width p)
/-- Own actual row clock at the existing physical original-input bank. -/
def rowBound (a M u n:Nat) (t q width:List Bool) (p:Model.Payload) :Nat:=
  Row.runBound (Model.view a M u (n+1) t q width p) width a (SemiprimeD1TaperedLoss.height M u) u n q t
/-- Own whole loop clock: each actual row, actual end-test, paid positive-q decrement and subsequent same-program loop. -/
def timeBound (a M u:Nat) (t width:List Bool) :Nat→List Bool→Model.Payload→Nat
  | 0,_,_=>1
  | n+1,q,p=>rowBound a M u n t q width p+1+
      (if n=0 then 0 else Dec.runBound q q+timeBound a M u t width n (Dec.difference q) (Row.step a M u t q width p))
attribute [local irreducible] rowBound Row.runBound Dec.runBound
/-- The entire actual binary-grid loop terminates at final arithmetic, with exact chronological payload and exact padded q0 retained. -/
theorem rows_run (a M u remaining:Nat) (t q width:List Bool) (p:Model.Payload)
    (hl:q.length=a+2) (hv:SemiprimeBitArithmetic.bitValue q=remaining-1) :
    ∃s≤ timeBound a M u t width remaining q p,Runs program s (.local .row)
      (bank (Model.view a M u remaining t q width p)) (.local .scalarInverse)
      (bank (Model.view a M u 0 t (L.zeroWord a) width (iterate a M u t width remaining q p))):=by
  induction remaining generalizing q p with
  | zero=>
    have h0:=PTrace.pop_run (.local .row) (.local .scalarInverse) (.local .abort) (.local .rowGeometry)
      (aux .todo) (bank (Model.view a M u 0 t q width p)) [] rfl rfl
    have he:Function.update (bank (Model.view a M u 0 t q width p)) (aux .todo) []=
      bank (Model.view a M u 0 t q width p):=Function.update_eq_self_iff.mpr rfl
    simp only [List.tail_nil] at h0
    rw [he] at h0
    change Runs program 1 _ _ (.local .scalarInverse) _ at h0
    have hz:q=L.zeroWord a:=L.zero_eq a q hl hv
    refine ⟨1,by rfl,?_⟩
    simpa only [iterate,hz] using h0
  | succ n ih=>
    obtain ⟨s,hs,h0⟩:=L.row_view_run a M u n t q width p
    have hs':s≤ rowBound a M u n t q width p:=by unfold rowBound;exact hs
    cases n with
    | zero=>
      have h1:=L.advance_zero a M u t q width (Row.step a M u t q width p)
      have hz:q=L.zeroWord a:=L.zero_eq a q hl (by simpa only [Nat.add_sub_cancel_left] using hv)
      have hfin:bank (Model.view a M u 0 t q width (Row.step a M u t q width p))=
          bank (Model.view a M u 0 t (L.zeroWord a) width (iterate a M u t width 1 q p)):=by
        change bank (Model.view a M u 0 t q width (Row.step a M u t q width p))=
          bank (Model.view a M u 0 t (L.zeroWord a) width (Row.step a M u t q width p))
        rw [hz]
      have h:=PTrace.join h0 h1
      rw [hfin] at h
      refine ⟨s+1,?_,h⟩
      change s+1≤ rowBound a M u 0 t q width p+1+0
      omega
    | succ n=>
      have hp:0<SemiprimeBitArithmetic.bitValue q:=by omega
      have h1:=L.advance_succ a M u n t q width (Row.step a M u t q width p) hp
      have hl':(Dec.difference q).length=a+2:=L.difference_width a q hl
      have hv':SemiprimeBitArithmetic.bitValue (Dec.difference q)=(n+1)-1:=by
        rw [Dec.difference_value q hp]
        omega
      obtain ⟨r,hr,h2⟩:=ih (Dec.difference q) (Row.step a M u t q width p) hl' hv'
      have h:=PTrace.join (PTrace.join h0 h1) h2
      change Runs program _ _ _ _
        (bank (Model.view a M u 0 t (L.zeroWord a) width (iterate a M u t width (n+1+1) q p))) at h
      refine ⟨s+(1+Dec.runBound q q)+r,?_,h⟩
      change s+(1+Dec.runBound q q)+r≤ rowBound a M u (n+1) t q width p+1+
        (if n+1=0 then 0 else Dec.runBound q q+timeBound a M u t width (n+1) (Dec.difference q) (Row.step a M u t q width p))
      rw [ite_eq_right (by omega :¬n+1=0)]
      omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridLoop

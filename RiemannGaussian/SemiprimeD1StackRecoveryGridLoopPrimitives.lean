/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridRowMeaning
/-! # Actual canonical row-loop entry, end test and decreasing binary counter -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridLoopPrimitives
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackProcedureTrace
namespace Model
export SemiprimeD1StackRecoveryGridModel (Payload view)
end Model
namespace Row
export SemiprimeD1StackRecoveryGridRow (row_run runBound)
export SemiprimeD1StackRecoveryGridRowMeaning (step row_eq)
end Row
namespace Dec
export SemiprimeD1StackRecoveryGridDecrement (difference decrement_run difference_value runBound)
end Dec
/-- Actual source row execution on the complete original-input loop bank, with all premises internally concrete. -/
theorem row_view_run (a M u n:Nat) (t q width:List Bool) (p:Model.Payload) :
    ∃s≤ Row.runBound (Model.view a M u (n+1) t q width p) width a (SemiprimeD1TaperedLoss.height M u) u n q t,
      Runs program s (.local .row) (bank (Model.view a M u (n+1) t q width p)) (.local .advance)
        (bank (Model.view a M u n t q width (Row.step a M u t q width p))):=by
  have hp:(Model.view a M u (n+1) t q width p).product=SemiprimeD1StackUnaryProduct.contents [] [] [] []:=by
    funext k;cases k <;> rfl
  have hc:(Model.view a M u (n+1) t q width p).registers (.center,false)≠[]:=List.cons_ne_nil _ _
  have hn:(Model.view a M u (n+1) t q width p).registers (.node,false)≠[]:=List.cons_ne_nil _ _
  have ha:(Model.view a M u (n+1) t q width p).registers (.alpha,false)≠[]:=List.cons_ne_nil _ _
  have hgn:(Model.view a M u (n+1) t q width p).registers (.gridNum,false)≠[]:=List.cons_ne_nil _ _
  have hgd:(Model.view a M u (n+1) t q width p).registers (.gridDen,false)≠[]:=List.cons_ne_nil _ _
  obtain ⟨s,hs,h⟩:=Row.row_run (Model.view a M u (n+1) t q width p) width a (SemiprimeD1TaperedLoss.height M u) u n q t
    rfl rfl rfl rfl rfl rfl (fun _=>rfl) rfl hp rfl rfl rfl rfl rfl rfl rfl hc hn ha hgn hgd
  rw [Row.row_eq] at h
  exact ⟨s,hs,h⟩
/-- Zero counter bytes retain exactly the acquired a+2 width. -/
def zeroWord (a:Nat) :List Bool:=List.replicate (a+2) false
/-- Literal false binary padding has value zero. -/
theorem zero_value (n:Nat) :SemiprimeBitArithmetic.bitValue (List.replicate n false)=0:=by
  induction n with
  | zero=>rfl
  | succ n ih=>simp [List.replicate_succ,SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat,ih]
/-- Physical fixed-width zero is unique; padding is preserved exactly. -/
theorem zero_eq (a:Nat) (q:List Bool) (hl:q.length=a+2) (hv:SemiprimeBitArithmetic.bitValue q=0) :q=zeroWord a:=by
  apply SemiprimeD1StackAssignmentOrder.word_value_injective
  · simpa only [zeroWord,List.length_replicate] using hl
  · rw [hv,zeroWord,zero_value]
/-- Actual binary subtraction preserves the entire a+2 physical width, including q0 padding. -/
theorem difference_width (a:Nat) (q:List Bool) (hl:q.length=a+2) :(Dec.difference q).length=a+2:=by
  rw [Dec.difference,(SemiprimeBitDivision.subBits_counts _ _ false).2.2.2.2]
  simp only [List.length_cons,List.length_nil]
  omega
/-- Actual q write changes no source, payload, shadow or metadata field. -/
theorem decrement_view (a M u n:Nat) (t q width:List Bool) (p:Model.Payload) :
    bank {Model.view a M u n t q width p with auxiliary:=Function.update (Model.view a M u n t q width p).auxiliary .q (Dec.difference q)}=
      bank (Model.view a M u n t (Dec.difference q) width p):=by
  rw [←update_auxiliary]
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · rfl
          · cases k <;> rfl
/-- Empty physical todo chooses the true final arithmetic entry, preserving every acquired word. -/
theorem advance_zero (a M u:Nat) (t q width:List Bool) (p:Model.Payload) :
    Runs program 1 (.local .advance) (bank (Model.view a M u 0 t q width p)) (.local .scalarInverse)
      (bank (Model.view a M u 0 t q width p)):=by
  exact PTrace.peek_run (.local .advance) (.local .scalarInverse) (.local .abort) (.local (.decrement .next))
    (aux .todo) (bank (Model.view a M u 0 t q width p)) [] rfl rfl
/-- Nonempty physical todo chooses a paid real binary decrement and returns to the actual row entry. -/
theorem advance_succ (a M u n:Nat) (t q width:List Bool) (p:Model.Payload)
    (hv:0<SemiprimeBitArithmetic.bitValue q) :
    Runs program (1+Dec.runBound q q) (.local .advance) (bank (Model.view a M u (n+1) t q width p))
      (.local .row) (bank (Model.view a M u (n+1) t (Dec.difference q) width p)):=by
  have h0:=PTrace.peek_run (.local .advance) (.local .scalarInverse) (.local .abort) (.local (.decrement .next))
    (aux .todo) (bank (Model.view a M u (n+1) t q width p)) (true::List.replicate n true) rfl
    (by change List.replicate (n+1) true=true::List.replicate n true;exact List.replicate_succ)
  change Runs program 1 _ _ (.local (.decrement .next)) _ at h0
  have hr:∀k,(Model.view a M u (n+1) t q width p).rational (SemiprimeD1StackRationalOperation.adderStack k)=[]:=by
    intro k;cases k <;> rfl
  have h1:=Dec.decrement_run .next (Model.view a M u (n+1) t q width p) q q rfl rfl hr rfl hv
  rw [decrement_view] at h1
  exact PTrace.join h0 h1
end RiemannGaussian.SemiprimeD1StackRecoveryGridLoopPrimitives

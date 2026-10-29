/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridCalls
/-! # Exact actual literal initialization of the whole recovery-grid source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridLiterals
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackProcedureTrace
/-- Exactly the15 already compiled physical literal push sites. -/
def literals :List (Stack×Bool):=
  [(aux .slopes,false),(aux .todo,true),(aux .todo,true),(aux .indexTemplate,false),(aux .indexTemplate,false),
   (reg .two false,true),(reg .two false,false),(reg .two false,false),(reg .two true,true),
   (reg .gridNum false,true),(reg .gridNum false,false),(reg .gridNum true,true),
   (reg .gridDen false,true),(reg .gridDen false,false),(reg .gridDen true,true)]
/-- Static initializer positions agree exactly with the actual constant instruction table. -/
theorem literals_get (i:Fin 15) :literals[i.val]=seed i:=by fin_cases i <;> rfl
/-- Actual data effect of the first fixed literal push instructions; not a runtime function operand. -/
def pushed (data:Stack→List Bool) (position:Nat) :Stack→List Bool:=
  (literals.take position).foldl (fun d pair=>Function.update d pair.1 (pair.2::d pair.1)) data
/-- Zero initializer instructions leave all original words intact. -/
theorem prefix_zero (data:Stack→List Bool) :pushed data 0=data:=rfl
/-- Every literal push is exactly the next fixed pushed of the existing instruction table. -/
theorem prefix_succ (data:Stack→List Bool) (i:Fin 15) :
    Function.update (pushed data i.val) (seed i).1 ((seed i).2::pushed data i.val (seed i).1)=pushed data (i.val+1):=by
  have hp:i.val<literals.length:=by change i.val<15;exact i.isLt
  have ht:=List.take_succ_eq_append_getElem hp
  rw [literals_get] at ht
  unfold pushed
  rw [ht,List.foldl_append,List.foldl_cons,List.foldl_nil]
/-- Proof-side static control notation; no original dimension is consulted. -/
def pc (position:Nat) :Label:=if h:position<15 then .local (.seed ⟨position,h⟩) else .local .copyA
/-- The actual literal block executes exactly one physical push per fixed position. -/
theorem sweep (remaining position:Nat) (hp:position+remaining=15) (data:Stack→List Bool) :
    Runs program remaining (pc position) (pushed data position) (.local .copyA) (pushed data 15):=by
  induction remaining generalizing position with
  | zero=>
    have he:position=15:=by omega
    subst position
    exact runs_refl program (.local .copyA) (pushed data 15)
  | succ remaining ih=>
    have hpos:position<15:=by omega
    let i:Fin 15:=⟨position,hpos⟩
    have hc:program (pc position)=.base (.push (seed i).1 (seed i).2 (pc (position+1))):=by
      dsimp only [pc]
      rw [dite_eq_left hpos]
      change mainProgram (.seed i)=_
      simp only [mainProgram]
      by_cases hn:position+1<15
      · have hi:i.val<14:=by dsimp [i];omega
        simp only [dite_eq_left hi,dite_eq_left hn]
        rfl
      · have hi:¬i.val<14:=by dsimp [i];omega
        simp only [dite_eq_right hi,dite_eq_right hn]
    have h0:=PTrace.push_run (pc position) (pc (position+1)) (seed i).1 (seed i).2 (pushed data position) hc
    have hu:=prefix_succ data i
    change Function.update (pushed data position) (seed i).1 ((seed i).2::pushed data position (seed i).1)=pushed data (position+1) at hu
    rw [hu] at h0
    have h1:=ih (position+1) (by omega)
    have h:=PTrace.join h0 h1
    simpa only [Nat.add_comm] using h
/-- Actual original five-word source initializes both exact oneWord right-fold bases, literal two, rowtodo2 and empty slopevector. -/
theorem literals_run (data:Stack→List Bool) :
    Runs program 16 (.local .start) data (.local .copyA) (pushed data 15):=by
  have h0:Runs program 1 (.local .start) data (.local (.seed 0)) data:=
    one_base program _ _ (.jump (.local (.seed 0))) data data rfl rfl rfl
  have h1:=sweep 15 0 rfl data
  have hz:(⟨0,by decide⟩:Fin 15)=0:=Fin.ext rfl
  have hp:pc 0=Label.local (.seed 0):=by unfold pc;rw [dite_eq_left (by decide),hz]
  rw [hp,prefix_zero] at h1
  exact PTrace.join h0 h1
end RiemannGaussian.SemiprimeD1StackRecoveryGridLiterals

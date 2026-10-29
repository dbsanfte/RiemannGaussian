/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineOperationOutput
/-! # All six real inner-pair fields are drained before the physical k decrement -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineInnerClear
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryAffineCleanup
/-- The six literal old-bank roles exactly match the already fixed source instructions. -/
def slot (i:Fin 6):Q.Stack:=match i.val with
  | 0=>Q.reg .numBase false | 1=>Q.reg .numBase true | 2=>Q.reg .denBase false
  | 3=>Q.reg .denBase true | 4=>Q.reg .numPower false | _=>Q.reg .numPower true
/-- Both fields of all three actual transient rational caches are EMPTY at the endpoint. -/
def result (w:Words):Words:=
  SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg
    (SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg
      (SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg w .numBase) .denBase) .numPower
/-- Exact six physical update endpoints, rather than a native replacement of the cleanup loop. -/
theorem cleared_result (w:Words):cleared slot w 6=bank (result w):=by
  have h0:=cleared_succ slot w (0:Fin 6)
  have h1:=cleared_succ slot w (1:Fin 6)
  have h2:=cleared_succ slot w (2:Fin 6)
  have h3:=cleared_succ slot w (3:Fin 6)
  have h4:=cleared_succ slot w (4:Fin 6)
  have h5:=cleared_succ slot w (5:Fin 6)
  change Function.update (cleared slot w 0) (grid (slot (0:Fin 6))) []=cleared slot w 1 at h0
  change Function.update (cleared slot w 1) (grid (slot (1:Fin 6))) []=cleared slot w 2 at h1
  change Function.update (cleared slot w 2) (grid (slot (2:Fin 6))) []=cleared slot w 3 at h2
  change Function.update (cleared slot w 3) (grid (slot (3:Fin 6))) []=cleared slot w 4 at h3
  change Function.update (cleared slot w 4) (grid (slot (4:Fin 6))) []=cleared slot w 5 at h4
  change Function.update (cleared slot w 5) (grid (slot (5:Fin 6))) []=cleared slot w 6 at h5
  rw [←h5,←h4,←h3,←h2,←h1,←h0,cleared_zero]
  change Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (bank w) (reg .numBase false) []) (reg .numBase true) []) (reg .denBase false) [])
    (reg .denBase true) []) (reg .numPower false) []) (reg .numPower true) []=bank (result w)
  simp only [update_register]
  rfl
/-- SAME actual program physically drains every byte and six actual EOF branches. -/
theorem source_run (part:Part) (w:Words):
    ∃q≤6*(mass (bank w)+1),Runs program q (.local (.clearInner part 0)) (bank w)
      (.local (.innerNext part)) (bank (result w)):=by
  have hc:∀i:Fin 6,program (.local (.clearInner part i))=.base
      (.pop (grid (slot i)) (next (fun j=>Label.local (.clearInner part j)) (.local (.innerNext part)) i)
        (.local (.clearInner part i)) (.local (.clearInner part i))):=by
    intro i
    fin_cases i <;> rfl
  obtain ⟨q,hq,hr⟩:=sweep (by decide:0<6) slot (fun i=>Label.local (.clearInner part i))
    (.local (.innerNext part)) hc 5 0 rfl w
  rw [cleared_zero,cleared_result] at hr
  refine ⟨q,?_,hr⟩
  have hsub:=old_mass_le w
  nlinarith
end RiemannGaussian.SemiprimeD1StackRecoveryAffineInnerClear

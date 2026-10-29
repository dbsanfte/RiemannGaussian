/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWidthLoop
/-! # Paid W-marker to FALSE-template emission and all64 physical register drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWidthFinish
open SemiprimeD1StackRecoveryWidth SemiprimeD1StackRecoveryWidthEncoding
open SemiprimeD1StackRecoveryWidthPrimitives SemiprimeD1StackRecoveryWidthLoop SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary unary_succ)
/-- Each actual width marker causes one real false template push; EOF is paid too. -/
theorem fill_run (n:Nat) (w:Words) (hw:w.registers 63=unary n) :
    Runs program (2*n+1) .fill (bank w) (.clean 0)
      (bank {w with registers:=Function.update w.registers 63 [],output:=List.replicate n false++w.output}) :=by
  induction n generalizing w with
  | zero=>
    have h0:=pop_run .fill (.clean 0) .write .write (reg 63) (bank w) [] rfl hw
    rw [update_reg] at h0
    exact h0
  | succ n ih=>
    have h0:=pop_run .fill (.clean 0) .write .write (reg 63) (bank w) (true::unary n) rfl hw
    rw [update_reg] at h0
    have h1:=push_run .write .fill (aux .output) false
      (bank {w with registers:=Function.update w.registers 63 (unary n)}) rfl
    change Runs _ _ _ _ _ (Function.update (bank _) (aux .output) (false::w.output)) at h1
    rw [update_output] at h1
    have h2:=ih {w with registers:=Function.update w.registers 63 (unary n),output:=false::w.output} (by
      change Function.update w.registers (63:W.Gate) (unary n) 63=unary n
      exact Function.update_self _ _ _)
    change Runs _ _ _ _ _ (bank {w with registers:=Function.update (Function.update w.registers 63 (unary n)) 63 [], output:=List.replicate n false++false::w.output}) at h2
    rw [Function.update_idem] at h2
    have he:List.replicate n false++false::w.output=List.replicate (n+1) false++w.output:=by
      rw [show List.replicate (n+1) false=List.replicate n false++[false] from List.replicate_add n 1 false,List.append_assoc]
      rfl
    rw [he] at h2
    have h:=join (join h0 h1) h2
    convert h using 1
    omega
/-- Only a previously drained fixed prefix is empty; the remaining actual registers stay untouched. -/
def cleared (stage:Nat) (registers:W.Gate→List Bool) (g:W.Gate) :List Bool:=if g.val<stage then [] else registers g
/-- Each real EOF-drain clears exactly its actual current fixed register. -/
theorem cleared_write (g:W.Gate) (registers:W.Gate→List Bool) :
    Function.update (cleared g.val registers) g []=cleared (g.val+1) registers:=by
  funext j
  by_cases hj:j=g
  · subst j
    simp only [Function.update_self,cleared,ite_eq_left (Nat.lt_succ_self _)]
  · rw [Function.update_of_ne hj]
    have hv:j.val≠g.val:=fun h=>hj (Fin.ext h)
    by_cases he:j.val<g.val
    · simp only [cleared,ite_eq_left he,ite_eq_left (by omega:j.val<g.val+1)]
    · simp only [cleared,ite_eq_right he,ite_eq_right (by omega:¬j.val<g.val+1)]
/-- Before the first literal drain, all actual register words are unchanged. -/
theorem cleared_zero (registers:W.Gate→List Bool) :cleared 0 registers=registers:=by
  funext g;exact ite_eq_right (Nat.not_lt_zero _)
/-- After all64 literal EOF-drains, every actual arithmetic register is empty. -/
theorem cleared_all (registers:W.Gate→List Bool) :cleared 64 registers=fun _=>[]:=by
  funext g;exact ite_eq_left g.isLt
/-- All64 real drains pay every retained old marker and EOF, while preserving the entire actual auxiliary bank. -/
theorem clean_loop (remaining stage:Nat) (hs:stage+remaining=64) (w:Words) (cap:Nat)
    (hw:∀g,(w.registers g).length≤ cap) :
    ∃q≤ remaining*(cap+1),Runs program q (cleanLabel stage) (bank {w with registers:=cleared stage w.registers})
      .done (bank {w with registers:=fun _=>[]}) :=by
  induction remaining generalizing stage with
  | zero=>
    have he:stage=64:=by omega
    subst stage
    rw [cleared_all]
    exact ⟨0,by omega,runs_refl program .done _⟩
  | succ remaining ih=>
    have hstage:stage<64:=by omega
    let g:W.Gate:=⟨stage,hstage⟩
    have h0:=drain_loop (.clean g) (nextClean g) (reg g) rfl
      (bank {w with registers:=cleared stage w.registers}) (w.registers g) (by
        change (if g.val<stage then [] else w.registers g)=_
        rw [ite_eq_right (by dsimp [g];omega)])
    rw [update_reg] at h0
    have he:Function.update (cleared stage w.registers) g []=cleared (stage+1) w.registers:=cleared_write g w.registers
    rw [he,next_clean] at h0
    obtain ⟨q,hq,h1⟩:=ih (stage+1) (by omega)
    have hl:cleanLabel stage=.clean g:=by unfold cleanLabel;rw [dite_eq_left hstage]
    rw [hl]
    refine ⟨_,?_,join h0 h1⟩
    have hb:=hw g
    nlinarith only [hb,hq]
/-- Real output emission is charged by W VALUE, plus all64 actual bounded register drains. -/
def finishBound (a M N:Nat) :Nat:=2*V.value 63 a M N+1+64*(wordCap a M N+1)
/-- Exact template production and all arithmetic-word cleanup from the physically completed64-gate bank. -/
theorem finish_run (a M N:Nat) :
    ∃q≤ finishBound a M N,Runs program q .fill (bank (atGate 64 a M N)) .done
      (bank {a:=unary a,m:=unary M,grid:=unary N,output:=List.replicate (V.value 63 a M N) false}) :=by
  have h0:=fill_run (V.value 63 a M N) (atGate 64 a M N) (by change registers 64 a M N 63=_;rw [complete_registers])
  let middle:Words:={atGate 64 a M N with registers:=Function.update (registers 64 a M N) 63 [], output:=List.replicate (V.value 63 a M N) false}
  have hc:∀g,(middle.registers g).length≤ wordCap a M N:=by
    intro g
    change (Function.update (registers 64 a M N) 63 [] g).length≤_
    by_cases hg:g=63
    · subst g;rw [Function.update_self,List.length_nil];omega
    · rw [Function.update_of_ne hg,complete_registers]
      simp only [unary,List.length_replicate]
      exact SemiprimeD1StackRecoveryWidthPolynomial.value_bound g a M N
  obtain ⟨q,hq,h1⟩:=clean_loop 64 0 rfl middle (wordCap a M N) hc
  rw [cleared_zero] at h1
  change Runs _ _ _ _ _ (bank {atGate 64 a M N with registers:=Function.update (registers 64 a M N) 63 [], output:=List.replicate (V.value 63 a M N) false++[]}) at h0
  rw [List.append_nil] at h0
  refine ⟨_,?_,join h0 h1⟩
  unfold finishBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryWidthFinish

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineOperationOutput
/-! # Complete literal grid arithmetic site, including physical operands/output/cleanup
This is an INTERNAL trace of the already fixed whole-grid program. Four actual
cache copies call the actual R36 source before any destination is erased.
Both fitted outputs and the actual sign are saved; every private R36 field is
then physically drained. No supplied operation stream or raw result appears.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineOperation
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackRecoveryAffineCalls
open SemiprimeD1StackRecoveryAffineOperationInput SemiprimeD1StackRecoveryAffineOperationOutput
open SemiprimeD1StackRecoveryAffineCleanup SemiprimeD1StackProcedureTrace
/-- Physical empty helper bank contains only the actual W template, never hidden original operands/results. -/
theorem emptyRational_explicit (width:List Bool) :emptyRational width=
    fun k=>if k=SemiprimeD1StackRationalOperation.aux .template then width else []:=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Own exact elapsed arithmetic-site prefix, through acquired output/sign and before physical35-role cleanup. -/
def prefixTime (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) :Nat:=
  inputsTime (sx::xn) xd (sy::yn) yd+
    (SemiprimeD1StackRationalOperationExecution.runBound (operation site) sx xn xd sy yn yd width+1)+
    ((w.registers (destination site,false)).length+1+(w.registers (destination site,true)).length+1)+
    saveTime (word (operation site) sx xn xd sy yn yd width)
/-- Stopped output cache plus actual R36 bank before its35 real drains. -/
def beforeCleanup (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) :Words:=
  saved {w with rational:=SemiprimeD1StackRationalOperationExecution.result (operation site) sx xn xd sy yn yd width}
    site (word (operation site) sx xn xd sy yn yd width)
/-- Every prefix action is an actual copy, whole normalization/two-fit call, old-destination drain, or actual-sign read/write. -/
theorem prefix_run (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hls:w.registers (operand site false,false)=sx::xn) (hld:w.registers (operand site false,true)=xd)
    (hrs:w.registers (operand site true,false)=sy::yn) (hrd:w.registers (operand site true,true)=yd) :
    Runs program (prefixTime site w sx xn xd sy yn yd width) (.operation site (.copyInput false false)) (bank w)
      (.operation site (.clear 0)) (bank (beforeCleanup site w sx xn xd sy yn yd width)):=by
  let ready:Words:={w with rational:=SemiprimeD1StackRationalOperation.input (sx::xn) xd (sy::yn) yd width}
  let stopped:Words:={w with rational:=SemiprimeD1StackRationalOperationExecution.result (operation site) sx xn xd sy yn yd width}
  have h0:=inputs_run site w width (sx::xn) xd (sy::yn) yd hr hs hls hld hrs hrd
  have h1:=rational_call site ready sx xn xd sy yn yd width rfl
  have h2:=erase_run site stopped
  have hshape:=word_shape (operation site) sx xn xd sy yn yd width
  have h3:=save_run site stopped (word (operation site) sx xn xd sy yn yd width) hs hshape.1 hshape.2.1 hshape.2.2
  exact PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
/-- Actual saved W is unchanged by sign consumption and all source arithmetic. -/
theorem beforeCleanup_template (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) :
    (beforeCleanup site w sx xn xd sy yn yd width).rational (SemiprimeD1StackRationalOperation.aux .template)=width:=by
  change Function.update (SemiprimeD1StackRationalOperationExecution.result (operation site) sx xn xd sy yn yd width)
    SemiprimeD1StackRationalOperation.signOutput [] (SemiprimeD1StackRationalOperation.aux .template)=width
  rw [Function.update_of_ne (by decide)]
  exact SemiprimeD1StackRationalOperationOriginal.template_retained (operation site) sx xn xd sy yn yd width
/-- Real cleanup preserves the actual width, cached output and all external caller data. -/
theorem cleanup_result (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hr:w.rational=emptyRational width) :
    cleared (fun i:Fin 35=>Q.rationalStack (Q.rationalRole i)) (beforeCleanup site w sx xn xd sy yn yd width) 35=
      bank (putReg w (destination site) (word (operation site) sx xn xd sy yn yd width)):=by
  let stopped:=beforeCleanup site w sx xn xd sy yn yd width
  rw [rational_cleared stopped]
  have hf:(fun k=>if k=SemiprimeD1StackRationalOperation.aux .template then stopped.rational k else [])=emptyRational width:=by
    rw [emptyRational_explicit]
    funext k
    by_cases hk:k=SemiprimeD1StackRationalOperation.aux .template
    · subst k
      simp only [ite_true]
      exact beforeCleanup_template site w sx xn xd sy yn yd width
    · simp only [hk,ite_false]
  rw [hf]
  change bank {putReg w (destination site) (word (operation site) sx xn xd sy yn yd width) with rational:=emptyRational width}=_
  rw [←hr]
  rfl
/-- Own actual byte/trace bound includes every retained external word during physical helper cleanup. -/
def timeBound (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) :Nat:=
  4000*(mass (bank w)+prefixTime site w sx xn xd sy yn yd width+1)
/-- Complete INTERNAL fixed-site execution: all intermediate values are acquired by real calls, all actual helper fields are cleared. -/
theorem operation_run (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hls:w.registers (operand site false,false)=sx::xn) (hld:w.registers (operand site false,true)=xd)
    (hrs:w.registers (operand site true,false)=sy::yn) (hrd:w.registers (operand site true,true)=yd) :
    ∃q ≤ timeBound site w sx xn xd sy yn yd width,Runs program q (.operation site (.copyInput false false)) (bank w)
      (.operation site .done) (bank (putReg w (destination site) (word (operation site) sx xn xd sy yn yd width))):=by
  have hp:=prefix_run site w sx xn xd sy yn yd width hr hs hls hld hrs hrd
  obtain ⟨q,hq,hqrun⟩:=rational_after_trace site (prefixTime site w sx xn xd sy yn yd width)
    (.operation site (.copyInput false false)) w (beforeCleanup site w sx xn xd sy yn yd width) hp
  rw [cleanup_result site w sx xn xd sy yn yd width hr] at hqrun
  exact ⟨q,hq,hqrun⟩
/-- Actual helper byte result is the exact original fitted operation, retaining its fixed operand orientation. -/
theorem operation_run_legacy (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hls:w.registers (operand site false,false)=sx::xn) (hld:w.registers (operand site false,true)=xd)
    (hrs:w.registers (operand site true,false)=sy::yn) (hrd:w.registers (operand site true,true)=yd) :
    ∃q ≤ timeBound site w sx xn xd sy yn yd width,Runs program q (.operation site (.copyInput false false)) (bank w)
      (.operation site .done) (bank (putReg w (destination site)
        (SemiprimeRationalBits.executeOperation (SemiprimeD1StackRationalOperation.operation (operation site))
          ⟨⟨sx,xn⟩,xd⟩ ⟨⟨sy,yn⟩,yd⟩ width).word)):=by
  have h:=operation_run site w sx xn xd sy yn yd width hr hs hls hld hrs hrd
  rw [word_legacy] at h
  exact h
end RiemannGaussian.SemiprimeD1StackRecoveryAffineOperation

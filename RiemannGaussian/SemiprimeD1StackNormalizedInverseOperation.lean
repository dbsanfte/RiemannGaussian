/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOperationOutput
import RiemannGaussian.SemiprimeD1StackNormalizedInverseCleanup
import RiemannGaussian.SemiprimeD1StackNormalizedInverseReadBuffers
/-! # Whole real inverse arithmetic call, all normalization/fits and actual private cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseOperation
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseCalls SemiprimeD1StackNormalizedInverseOperationInput
open SemiprimeD1StackNormalizedInverseOperationOutput SemiprimeD1StackNormalizedInverseCleanup
open SemiprimeD1StackNormalizedInverseReadBuffers SemiprimeD1StackProcedureTrace
/-- Exact same-source prefix clock, through actual result copies and sign pop/push. -/
def prefixTime (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) :Nat:=
  inputsTime (sx::xn) xd (sy::yn) yd+
    (SemiprimeD1StackRationalOperationExecution.runBound (operation site) sx xn xd sy yn yd width+1)+
    ((w.registers (destination site,false)).length+1+(w.registers (destination site,true)).length+1)+
    saveTime (word (operation site) sx xn xd sy yn yd width)
/-- Actual stopped R36 bank and acquired result before all35 physical drains. -/
def beforeCleanup (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) :Words:=
  saved {w with rational:=SemiprimeD1StackRationalOperationExecution.result (operation site) sx xn xd sy yn yd width}
    site (word (operation site) sx xn xd sy yn yd width)
/-- The four actual input copies finish BEFORE any aliased accumulator/destination is drained. -/
theorem prefix_run (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hls:w.registers (operand site false,false)=sx::xn) (hld:w.registers (operand site false,true)=xd)
    (hrs:w.registers (operand site true,false)=sy::yn) (hrd:w.registers (operand site true,true)=yd) :
    Runs program (prefixTime site w sx xn xd sy yn yd width) (.operation site (.copyInput false false)) (store w)
      (.operation site (.clear 0)) (store (beforeCleanup site w sx xn xd sy yn yd width)):=by
  let ready:Words:={w with rational:=SemiprimeD1StackRationalOperation.input (sx::xn) xd (sy::yn) yd width}
  let stopped:Words:={w with rational:=SemiprimeD1StackRationalOperationExecution.result (operation site) sx xn xd sy yn yd width}
  have h0:=inputs_run site w width (sx::xn) xd (sy::yn) yd hr hs hls hld hrs hrd
  have h1:=rational_call site ready sx xn xd sy yn yd width rfl
  have h2:=erase_run site stopped
  have hshape:=word_shape (operation site) sx xn xd sy yn yd width
  have h3:=save_run site stopped (word (operation site) sx xn xd sy yn yd width) hs hshape.1 hshape.2.1 hshape.2.2
  exact PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
/-- The actual original template survives sign consumption and every R36 instruction. -/
theorem beforeCleanup_template (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) :
    (beforeCleanup site w sx xn xd sy yn yd width).rational (R.aux .template)=width:=by
  change Function.update (SemiprimeD1StackRationalOperationExecution.result (operation site) sx xn xd sy yn yd width)
    SemiprimeD1StackRationalOperation.signOutput [] (R.aux .template)=width
  rw [Function.update_of_ne (by decide)]
  exact SemiprimeD1StackRationalOperationOriginal.template_retained (operation site) sx xn xd sy yn yd width
/-- Cleanup returns all35 real arithmetic fields to their honest empty state, retaining every foreign word. -/
theorem cleanup_result (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hr:w.rational=emptyRational width) :
    cleared (fun i:Fin 35=>rational (rationalRole i)) (store (beforeCleanup site w sx xn xd sy yn yd width)) 35=
      store (putReg w (destination site) (word (operation site) sx xn xd sy yn yd width)):=by
  let stopped:=beforeCleanup site w sx xn xd sy yn yd width
  rw [rational_cleared stopped]
  have hf:(fun k=>if k=R.aux .template then stopped.rational k else [])=emptyRational width:=by
    funext k
    by_cases hk:k=R.aux .template
    · subst k
      simp only [ite_true,emptyRational]
      exact beforeCleanup_template site w sx xn xd sy yn yd width
    · simp only [hk,ite_false,emptyRational]
  rw [hf]
  change store {putReg w (destination site) (word (operation site) sx xn xd sy yn yd width) with rational:=emptyRational width}=_
  rw [←hr]
  rfl
/-- Own actual elapsed bound includes every retained foreign word during all35 cleanup loops. -/
def timeBound (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool) :Nat:=
  2100*(mass (store w)+prefixTime site w sx xn xd sy yn yd width+1)+1
/-- The complete internal helper ends BEFORE its real return, with its physically acquired TRUE marker. -/
theorem operation_run (site:Site) (w:Words) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd width:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[]) (hv:w.auxiliary .valid=[])
    (hls:w.registers (operand site false,false)=sx::xn) (hld:w.registers (operand site false,true)=xd)
    (hrs:w.registers (operand site true,false)=sy::yn) (hrd:w.registers (operand site true,true)=yd) :
    ∃q≤timeBound site w sx xn xd sy yn yd width,
      Runs program q (.operation site (.copyInput false false)) (store w) (.operation site .return)
        (store (success (putReg w (destination site) (word (operation site) sx xn xd sy yn yd width)))):=by
  have hp:=prefix_run site w sx xn xd sy yn yd width hr hs hls hld hrs hrd
  obtain ⟨q,hq,hqrun⟩:=rational_after_trace site (prefixTime site w sx xn xd sy yn yd width)
    (.operation site (.copyInput false false)) (store w) (store (beforeCleanup site w sx xn xd sy yn yd width)) hp
  rw [cleanup_result site w sx xn xd sy yn yd width hr] at hqrun
  let acquired:=putReg w (destination site) (word (operation site) sx xn xd sy yn yd width)
  have h1:=PTrace.push_run (.operation site .success) (.operation site .return) (aux .valid) true (store acquired) rfl
  change Runs program 1 _ _ _ (Function.update (store acquired) (aux .valid) (true::acquired.auxiliary .valid)) at h1
  rw [update_success acquired hv] at h1
  exact ⟨q+1,Nat.add_le_add_right hq 1,PTrace.join hqrun h1⟩
end RiemannGaussian.SemiprimeD1StackNormalizedInverseOperation

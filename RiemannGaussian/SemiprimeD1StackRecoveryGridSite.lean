/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridOperation
import RiemannGaussian.SemiprimeD1StackRecoveryGridRegisters
/-! # Literal actual rational-site calls with real continuation cells -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridSite
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridRegisters SemiprimeD1StackRecoveryGridOperationInput
open SemiprimeD1StackProcedureTrace
/-- Proof-side exact rational result of one fixed actual site, never a source operand. -/
def answer (site:Site) (w:Words) (width:List Bool) :SemiprimeRationalBits.RationalWord:=
  (SemiprimeRationalBits.executeOperation (SemiprimeD1StackRationalOperation.operation (operation site))
    (getReg w (operand site false)) (getReg w (operand site true)) width).word
/-- Actual acquired cache effect; all35 operation-private words are again empty. -/
def result (site:Site) (w:Words) (width:List Bool) :Words:=putReg w (destination site) (answer site w width)
/-- A nonempty actual signed register is exactly its parsed Boolean sign and actual magnitude tail. -/
theorem signed_getReg (w:Words) (r:Reg) (h:w.registers (r,false)≠[]) :
    w.registers (r,false)=signed (getReg w r):=by
  unfold getReg signed
  cases he:w.registers (r,false) with
  | nil=>exact (h he).elim
  | cons b bs=>rfl
/-- Own actual arithmetic call bound includes both real call and real return. -/
def runBound (site:Site) (w:Words) (width:List Bool) :Nat:=
  let l:=getReg w (operand site false)
  let r:=getReg w (operand site true)
  SemiprimeD1StackRecoveryGridOperation.timeBound site w l.numerator.negative l.numerator.magnitude l.denominator
    r.numerator.negative r.numerator.magnitude r.denominator width+2
/-- The caller pays actual operand acquisition, whole R36 execution, complete cleanup and actual return. -/
theorem site_call (site:Site) (pc next:Label) (w:Words) (width:List Bool)
    (hcode:program pc=.call (.operation site (.copyInput false false)) next)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hl:w.registers (operand site false,false)≠[]) (hh:w.registers (operand site true,false)≠[]) :
    ∃q≤runBound site w width,Runs program q pc (bank w) next (bank (result site w width)):=by
  let l:=getReg w (operand site false)
  let r:=getReg w (operand site true)
  obtain ⟨q,hq,h⟩:=SemiprimeD1StackRecoveryGridOperation.operation_run_legacy site w
    l.numerator.negative l.numerator.magnitude l.denominator r.numerator.negative r.numerator.magnitude r.denominator width
    hr hs (signed_getReg w _ hl) rfl (signed_getReg w _ hh) rfl
  have hret:program (.operation site .done)=.ret:=rfl
  have hc:=PTrace.local_call pc (.operation site (.copyInput false false)) (.operation site .done) next
    hcode hret q (bank w) (bank (result site w width)) h
  exact ⟨q+2,Nat.add_le_add_right hq 2,hc⟩
/-- Every actually written rational cache has its physical sign byte, even when W=0. -/
theorem written_nonempty (site:Site) (w:Words) (width:List Bool) :
    (result site w width).registers (destination site,false)≠[]:=by
  rw [show (result site w width).registers (destination site,false)=signed (answer site w width) from
    (putReg_fields w _ _).1]
  exact List.cons_ne_nil _ _
/-- An actual site preserves nonemptiness of every already acquired signed cache. -/
theorem nonempty_preserved (site:Site) (w:Words) (width:List Bool) (r:Reg) (h:w.registers (r,false)≠[]) :
    (result site w width).registers (r,false)≠[]:=by
  by_cases he:r=destination site
  · subst r;exact written_nonempty site w width
  · rw [show (result site w width).registers (r,false)=w.registers (r,false) from putReg_other w (destination site) r (answer site w width) false he]
    exact h
/-- Real-site arithmetic leaves the complete clean R36 bank unchanged after all35 drains. -/
theorem rational_retained (site:Site) (w:Words) (width:List Bool) :(result site w width).rational=w.rational:=rfl
/-- Real-site arithmetic retains every source/counter/framing word, including actual W and q. -/
theorem auxiliary_retained (site:Site) (w:Words) (width:List Bool) :(result site w width).auxiliary=w.auxiliary:=rfl
end RiemannGaussian.SemiprimeD1StackRecoveryGridSite

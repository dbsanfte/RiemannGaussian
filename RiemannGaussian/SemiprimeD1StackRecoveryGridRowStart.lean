/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridGeometry
import RiemannGaussian.SemiprimeD1StackRecoveryGridNode
/-! # Actual row-marker consumption, true geometry and copied signed index -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridRowStart
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackProcedureTrace
namespace Geometry
export SemiprimeD1StackRecoveryGridGeometry (result geometry_run)
end Geometry
/-- Actual row starts by consuming its physical TRUE marker, not by testing a supplied row index/count. -/
def popped (w:Words) (n:Nat) :Words:={w with auxiliary:=Function.update w.auxiliary .todo (List.replicate n true)}
/-- Complete true geometry acquired for the actual current binary q after the row marker is consumed. -/
def result (w:Words) (a:Nat) (q:List Bool) (n:Nat) :Words:=
  Geometry.result (popped w n) (List.replicate a true) q
/-- Own actual row-entry geometry/point-drain clock. -/
def runBound (a:Nat) (q:List Bool) :Nat:=1+
  (SemiprimeD1StackPhaseGeometryComponents.runBound (List.replicate a true) q+1+
    (SemiprimeD1StackPhaseGeometryArithmetic.magnitude a q).length+1)
/-- One genuine row-marker pop followed by real true-geometry acquisition and actual shared-point cleanup. -/
theorem row_start_run (w:Words) (a n:Nat) (q:List Bool)
    (ht:w.auxiliary .todo=List.replicate (n+1) true)
    (ha:w.auxiliary .originalA=List.replicate a true) (hq:w.auxiliary .q=q)
    (hg:∀k,w.geometry k=[]) (hr:∀k,w.rational (SemiprimeD1StackRationalOperation.adderStack k)=[]) :
    ∃t≤runBound a q,Runs program t (.local .row) (bank w) (.local .center) (bank (result w a q n)):=by
  have h0:=PTrace.pop_run (.local .row) (.local .scalarInverse) (.local .abort) (.local .rowGeometry)
    (aux .todo) (bank w) (true::List.replicate n true) rfl (by change w.auxiliary .todo=true::List.replicate n true;simpa only [List.replicate_succ] using ht)
  rw [update_auxiliary] at h0
  change Runs program 1 _ _ (.local .rowGeometry) (bank (popped w n)) at h0
  have hi:∀k,bank (popped w n) (geometryStack k)=SemiprimeD1StackPhaseGeometry.input (List.replicate a true) q k:=by
    intro k
    rcases k with k|k
    · cases k <;> exact hr _
    · cases k
      · exact ha
      · exact hq
      · exact hg _
      · exact hg _
      · exact hg _
      · exact hg _
      · exact hg _
      · exact hg _
      · exact hg _
      · exact hg _
  obtain ⟨t,htime,h1⟩:=Geometry.geometry_run .row (popped w n) (List.replicate a true) q hi (hr .output)
  refine ⟨1+t,?_,PTrace.join h0 h1⟩
  unfold runBound
  simpa only [List.length_replicate] using Nat.add_le_add_left htime 1
/-- Actual singleton center-test bit, retained after the physical peek. -/
theorem center_run (w:Words) (b:Bool) (hb:w.geometry .zero=[b]) :
    Runs program 1 (.local .center) (bank w)
      (if b then .local (.clearTransient false 0) else .local .equalQ) (bank w):=by
  have h:=PTrace.peek_run (.local .center) (.local .abort) (.local .equalQ) (.local (.clearTransient false 0))
    (geometryAux .zero) (bank w) [b] rfl hb
  cases b <;> exact h
/-- Exact physical signed integer word acquired from the current q buffer. -/
def index (q:List Bool) :SemiprimeRationalBits.RationalWord:=⟨⟨false,q⟩,[true]⟩
/-- Paid row index acquisition, with no fit against rational W and no unary expansion of q. -/
theorem index_run (w:Words) (q:List Bool) (hq:w.auxiliary .q=q)
    (hs:w.auxiliary .copyScratch=[]) (hn:w.registers (.index,false)=[]) (hd:w.registers (.index,true)=[]) :
    Runs program (5*q.length+4+2) (.local .index) (bank w) (.local .levels) (bank (putReg w .index (index q))):=by
  let copied:Words:={w with registers:=Function.update w.registers (.index,false) q}
  have h0:=PTrace.copy_call .index (.local .index) (.local .indexSign) rfl (bank w) q [] hq hn hs
  change Runs program _ _ _ _ (Function.update (bank w) (reg .index false) (q++[])) at h0
  rw [List.append_nil,update_registers _ (.index,false)] at h0
  have h1:=PTrace.push_run (.local .indexSign) (.local .indexDen) (reg .index false) false (bank copied) rfl
  change Runs program 1 _ _ _ (Function.update (bank copied) (reg .index false) (false::q)) at h1
  rw [update_registers _ (.index,false)] at h1
  let signed:Words:={copied with registers:=Function.update copied.registers (.index,false) (false::q)}
  have h2:=PTrace.push_run (.local .indexDen) (.local .levels) (reg .index true) true (bank signed) rfl
  change Runs program 1 _ _ _ (Function.update (bank signed) (reg .index true) (true::w.registers (.index,true))) at h2
  rw [hd,update_registers _ (.index,true)] at h2
  have h:=PTrace.join (PTrace.join h0 h1) h2
  dsimp only [copied,signed] at h
  rw [Function.update_idem] at h
  change Runs program _ _ _ _ (bank (putReg w .index (index q))) at h
  exact h
/-- A true fixed-width current q gives exactly the legacy original signed index bytes. -/
theorem index_original (a n:Nat) (q:List Bool)
    (hl:q.length=a+2) (hv:SemiprimeBitArithmetic.bitValue q=n) (hn:n<2^(a+1)) :
    index q=(SemiprimeD1RecoveryGridBits.index a n).word:=by
  have hb:n<2^(a+2):=by
    have hp:2^(a+2)=2^(a+1)*2:=by rw [show a+2=(a+1)+1 by omega,pow_succ]
    rw [hp]
    omega
  have he:q=(SemiprimeEncodedRowSelection.digits (a+2) n).bits:=by
    apply SemiprimeD1StackAssignmentOrder.word_value_injective
    · rw [hl,SemiprimeEncodedRowSelection.digits_length]
    · rw [hv,SemiprimeEncodedRowSelection.digits_value _ _ hb]
  unfold index
  rw [he]
  rfl
end RiemannGaussian.SemiprimeD1StackRecoveryGridRowStart

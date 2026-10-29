/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridSite
import RiemannGaussian.SemiprimeD1StackRecoveryGridTransient
/-! # Actual final Ezero/argument arithmetic and complete physical cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridFinal
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridOperationInput SemiprimeD1StackRecoveryGridCleanup
open SemiprimeD1StackProcedureTrace
namespace Call
export SemiprimeD1StackRecoveryGridSite (result runBound site_call written_nonempty nonempty_preserved)
end Call
namespace Transient
export SemiprimeD1StackRecoveryGridTransient (result transient_run)
end Transient
/-- Actual grid-denominator inverse cache. -/
def inverseDen (w:Words) (width:List Bool) :Words:=Call.result .scalarInverse w width
/-- Actual Ezero scalar cache, after the denominator inverse. -/
def scalar (w:Words) (width:List Bool) :Words:=Call.result .scalar (inverseDen w width) width
/-- Actual negative-node cache; the three-site front block stops at the literal point entry. -/
def front (w:Words) (width:List Bool) :Words:=Call.result .negativeNode (scalar w width) width
/-- Own three-site front budget includes every actual call and real return. -/
def frontBound (w:Words) (width:List Bool) :Nat:=
  Call.runBound .scalarInverse w width+Call.runBound .scalar (inverseDen w width) width+
  Call.runBound .negativeNode (scalar w width) width
attribute [local irreducible] frontBound Call.runBound mass
/-- First three actual final sites, kept as an abstract physical block to avoid unfolding rational evaluators during composition. -/
theorem front_run (w:Words) (width:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hgn:w.registers (.gridNum,false)≠[]) (hgd:w.registers (.gridDen,false)≠[])
    (hn:w.registers (.node,false)≠[]) :
    ∃q≤frontBound w width,Runs program q (.local .scalarInverse) (bank w) (.local .point) (bank (front w width)):=by
  obtain ⟨t0,ht0,h0⟩:=Call.site_call .scalarInverse (.local .scalarInverse) (.local .scalar) w width rfl hr hs hgd hgd
  have hgn1:=Call.nonempty_preserved .scalarInverse w width .gridNum hgn
  have hrec1:=Call.written_nonempty .scalarInverse w width
  obtain ⟨t1,ht1,h1⟩:=Call.site_call .scalar (.local .scalar) (.local .negativeNode) (inverseDen w width) width rfl hr hs hgn1 hrec1
  have hn1:=Call.nonempty_preserved .scalarInverse w width .node hn
  have hn2:=Call.nonempty_preserved .scalar (inverseDen w width) width .node hn1
  obtain ⟨t2,ht2,h2⟩:=Call.site_call .negativeNode (.local .negativeNode) (.local .point) (scalar w width) width rfl hr hs hn2 hn2
  change Runs program t0 _ _ _ (bank (inverseDen w width)) at h0
  change Runs program t1 _ _ _ (bank (scalar w width)) at h1
  change Runs program t2 _ _ _ (bank (front w width)) at h2
  refine ⟨t0+t1+t2,?_,PTrace.join (PTrace.join h0 h1) h2⟩
  unfold frontBound
  omega
/-- Every acquired signed cache remains nonempty through the real front block. -/
theorem front_nonempty (w:Words) (width:List Bool) (r:Reg) (h:w.registers (r,false)≠[]) :
    (front w width).registers (r,false)≠[]:=
  Call.nonempty_preserved .negativeNode (scalar w width) width r
    (Call.nonempty_preserved .scalar (inverseDen w width) width r
      (Call.nonempty_preserved .scalarInverse w width r h))
/-- The actual third front operation acquires the signed negative node. -/
theorem front_negative (w:Words) (width:List Bool) :(front w width).registers (.negative,false)≠[]:=
  Call.written_nonempty .negativeNode (scalar w width) width
/-- Actual center-minus-node point, starting with the acquired negative-node cache. -/
def tailPoint (w:Words) (width:List Bool) :Words:=Call.result .point w width
/-- Actual alpha reciprocal. -/
def tailAlpha (w:Words) (width:List Bool) :Words:=Call.result .inverseAlpha (tailPoint w width) width
/-- Actual local argument, after all three tail operations. -/
def tailResult (w:Words) (width:List Bool) :Words:=Call.result .argument (tailAlpha w width) width
/-- Own three-site argument budget. -/
def tailBound (w:Words) (width:List Bool) :Nat:=
  Call.runBound .point w width+Call.runBound .inverseAlpha (tailPoint w width) width+
    Call.runBound .argument (tailAlpha w width) width
attribute [local irreducible] tailBound
/-- All three actual argument operations run on actual acquired caches and retain all external words. -/
theorem tail_run (w:Words) (width:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hc:w.registers (.center,false)≠[]) (ha:w.registers (.alpha,false)≠[])
    (hn:w.registers (.negative,false)≠[]) :
    ∃q≤tailBound w width,Runs program q (.local .point) (bank w)
      (.local (.clearTransient true 0)) (bank (tailResult w width)):=by
  obtain ⟨t0,ht0,h0⟩:=Call.site_call .point (.local .point) (.local .inverseAlpha) w width rfl hr hs hc hn
  have ha1:=Call.nonempty_preserved .point w width .alpha ha
  obtain ⟨t1,ht1,h1⟩:=Call.site_call .inverseAlpha (.local .inverseAlpha) (.local .argument) (tailPoint w width) width rfl hr hs ha1 ha1
  have hp1:=Call.written_nonempty .point w width
  have hp2:=Call.nonempty_preserved .inverseAlpha (tailPoint w width) width .numBase hp1
  have hr2:=Call.written_nonempty .inverseAlpha (tailPoint w width) width
  obtain ⟨t2,ht2,h2⟩:=Call.site_call .argument (.local .argument) (.local (.clearTransient true 0))
    (tailAlpha w width) width rfl hr hs hp2 hr2
  change Runs program t0 _ _ _ (bank (tailPoint w width)) at h0
  change Runs program t1 _ _ _ (bank (tailAlpha w width)) at h1
  change Runs program t2 _ _ _ (bank (tailResult w width)) at h2
  refine ⟨t0+t1+t2,?_,PTrace.join (PTrace.join h0 h1) h2⟩
  unfold tailBound
  omega
/-- Actual whole-six-site endpoint before the final sixteen drains. -/
def argument (w:Words) (width:List Bool) :Words:=tailResult (front w width) width
/-- Complete actual cleanup endpoint, with every transient field and actual q word cleared. -/
def clean (w:Words) :Words:=
  {Transient.result w with auxiliary:=Function.update w.auxiliary .q []}
/-- Own real sixteen-drain plus q-drain clock in actual physical input bytes. -/
def cleanupBound (w:Words) :Nat:=16*(mass (bank w)+1)+(w.auxiliary .q).length+1
attribute [local irreducible] clean cleanupBound
/-- Cleanup runs on an abstract actual bank so rational payload evaluators are never unfolded by the trace proof. -/
theorem cleanup_run (w:Words) :
    ∃q≤cleanupBound w,Runs program q (.local (.clearTransient true 0)) (bank w) (.local .done) (bank (clean w)):=by
  obtain ⟨p,hp,h0⟩:=Transient.transient_run true w
  have h1:=PTrace.drain_loop (.local .clearFinalQ) (.local .done) (aux .q) rfl
    (bank (Transient.result w)) (w.auxiliary .q) rfl
  rw [update_auxiliary] at h1
  have haux:(Transient.result w).auxiliary=w.auxiliary:=rfl
  rw [haux] at h1
  have he:({Transient.result w with auxiliary:=Function.update w.auxiliary .q []}:Words)=clean w:=by unfold clean;rfl
  rw [he] at h1
  refine ⟨p+((w.auxiliary .q).length+1),?_,PTrace.join h0 h1⟩
  unfold cleanupBound
  omega
/-- All six acquired final coefficients followed by the actual full cleanup. -/
def result (w:Words) (width:List Bool) :Words:=clean (argument w width)
/-- Whole own final clock, composed from the same two actual three-site traces and cleanup trace. -/
def runBound (w:Words) (width:List Bool) :Nat:=
  frontBound w width+tailBound (front w width) width+cleanupBound (argument w width)
attribute [local irreducible] result runBound
/-- Whole actual Ezero/local-argument finish; no supplied coefficient, operation answer or clock operand is used. -/
theorem final_run (w:Words) (width:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hgn:w.registers (.gridNum,false)≠[]) (hgd:w.registers (.gridDen,false)≠[])
    (hn:w.registers (.node,false)≠[]) (hc:w.registers (.center,false)≠[])
    (ha:w.registers (.alpha,false)≠[]) :
    ∃q≤runBound w width,Runs program q (.local .scalarInverse) (bank w) (.local .done) (bank (result w width)):=by
  obtain ⟨p,hp,h0⟩:=front_run w width hr hs hgn hgd hn
  obtain ⟨q,hq,h1⟩:=tail_run (front w width) width hr hs
    (front_nonempty w width .center hc) (front_nonempty w width .alpha ha) (front_negative w width)
  change Runs program q _ _ _ (bank (argument w width)) at h1
  obtain ⟨r,hrBound,h2⟩:=cleanup_run (argument w width)
  have he:clean (argument w width)=result w width:=by unfold result;rfl
  rw [he] at h2
  refine ⟨p+q+r,?_,PTrace.join (PTrace.join h0 h1) h2⟩
  unfold runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridFinal

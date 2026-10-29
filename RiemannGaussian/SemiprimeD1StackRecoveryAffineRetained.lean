/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineGeometry
/-! # Whole actual retained-q acquisition, restoring every Grid104 word
The true geometry source, real marker subtraction/product, paid result copy and
complete cleanup execute on the reached Grid bank. No q answer is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineRetained
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackRecoveryAffineCalls
open SemiprimeD1StackProcedureTrace
namespace Geom
export SemiprimeD1StackRecoveryAffineGeometry (result geometry_run order_bytes)
end Geom
namespace Meta
export SemiprimeD1StackRecoveryAffineMultiplicity (words multiplicity_run runBound)
end Meta
namespace Clear
export SemiprimeD1StackRecoveryAffineCleanup (geometry_run geometry_cleared)
end Clear
/-- Actual scanned order, interpreted only for the same-source invariant. -/
def order (a:Nat) (t:List Bool):Nat:=SemiprimeD1StackRecoveryGridRow.order a t
/-- Physical originalt copy into the borrowed actual geometry index. -/
def asked (w:Words) (t:List Bool):Words:={w with auxiliary:=Function.update w.auxiliary .q t}
/-- Exact actual true geometry bank after its shared-point cleanup. -/
def geometric (w:Words) (a:Nat) (t:List Bool):Words:=Geom.result (asked w t) (List.replicate a true) t
/-- Exact actual unary retained-q product after real u-order and h multiplication. -/
def multiplied (w:Words) (a h u:Nat) (t:List Bool):Words:=
  Meta.words (geometric w a t) [] [] (List.replicate (h*(u-order a t)) true) []
/-- Actual preserving result copy retains q in its one additional readonly output word. -/
def saved (w:Words) (a h u:Nat) (t:List Bool):Words:=
  {multiplied w a h u t with added:=Function.update w.added .retainedQ (List.replicate (h*(u-order a t)) true)}
/-- All four actual unary-product work words are EMPTY after the paid product drain. -/
def productCleared (w:Words) (a h u:Nat) (t:List Bool):Words:=
  {saved w a h u t with product:=SemiprimeD1StackUnaryProduct.contents [] [] [] []}
/-- All ten geometry roles, including displaced shadows, are physically clear. -/
def geometryCleared (w:Words) (a h u:Nat) (t:List Bool):Words:=
  {productCleared w a h u t with geometry:=fun _=>[]}
/-- Actual final originalt scratch drain restores its original EMPTY value. -/
def result (w:Words) (a h u:Nat) (t:List Bool):Words:=
  {geometryCleared w a h u t with auxiliary:=Function.update (geometryCleared w a h u t).auxiliary .q []}
/-- This whole source retains EVERY original104 word and changes only its actual new q output. -/
theorem result_eq (w:Words) (a h u:Nat) (t:List Bool)
    (hg:∀slot,w.geometry slot=[]) (hp:w.product=SemiprimeD1StackUnaryProduct.contents [] [] [] [])
    (hq:w.auxiliary .q=[]) (ho:w.auxiliary .orderTodo=[]):
    result w a h u t={w with added:=Function.update w.added .retainedQ (List.replicate (h*(u-order a t)) true)}:=by
  have haux:Function.update (Function.update (Function.update w.auxiliary .q t) .orderTodo []) .q []=w.auxiliary:=by
    funext slot
    cases slot <;> simp only [Function.update_apply] <;> simp_all
  have hgeom:w.geometry=(fun _=>[] ) :=funext hg
  dsimp only [result,geometryCleared,productCleared,saved,multiplied,Meta.words,geometric,Geom.result,asked]
  rw [haux,←hp,←hgeom]
/-- Own whole q-acquisition budget sums the SAME actual source/copy/scan/drain clocks. -/
def runBound (w:Words) (a h u:Nat) (t:List Bool):Nat:=
  (5*t.length+4)+(SemiprimeD1StackPhaseGeometryComponents.runBound (List.replicate a true) t+1+
    (SemiprimeD1StackPhaseGeometryArithmetic.magnitude a t).length+1)+Meta.runBound h u (order a t)+
    (5*(h*(u-order a t))+4)+(h*(u-order a t)+1)+
    10*(SemiprimeD1StackRecoveryGridCleanup.mass (SemiprimeD1StackRecoveryGridView.bank (productCleared w a h u t).toWords)+1)+(t.length+1)
/-- The original parameters, actual height and EMPTY work bank suffice; no multiplicity value or geometry answer is an input. -/
theorem retained_run (w:Words) (a h u:Nat) (t:List Bool)
    (ha:w.auxiliary .originalA=List.replicate a true) (hu:w.auxiliary .originalU=List.replicate u true)
    (ht:w.auxiliary .originalT=t) (hh:w.division .quotient=List.replicate h true)
    (hg:∀slot,w.geometry slot=[]) (hr:∀slot,w.rational (SemiprimeD1StackRationalOperation.adderStack slot)=[])
    (hp:w.product=SemiprimeD1StackUnaryProduct.contents [] [] [] [])
    (hq:w.auxiliary .q=[]) (ho:w.auxiliary .orderTodo=[]) (hs:w.auxiliary .copyScratch=[]) (hz:w.added .retainedQ=[]):
    ∃q≤runBound w a h u t,Runs program q (.local .ready) (bank w) (.local .copySlopes)
      (bank {w with added:=Function.update w.added .retainedQ (List.replicate (h*(u-order a t)) true)}):=by
  have h0:=PTrace.copy_call .originalT (.local .ready) (.local .geometry) rfl (bank w) t [] ht hq hs
  change Runs program (5*t.length+4) _ _ _ (Function.update (bank w) (oldAux .q) (t++[])) at h0
  rw [List.append_nil,update_oldAux] at h0
  change Runs program (5*t.length+4) _ _ _ (bank (asked w t)) at h0
  have hi:∀slot,bank (asked w t) (geometry slot)=SemiprimeD1StackPhaseGeometry.input (List.replicate a true) t slot:=by
    intro slot
    rcases slot with slot|slot
    · cases slot <;> exact hr _
    · cases slot
      · exact ha
      · rfl
      · exact hg _
      · exact hg _
      · exact hg _
      · exact hg _
      · exact hg _
      · exact hg _
      · exact hg _
      · exact hg _
  obtain ⟨p,hpBound,h1⟩:=Geom.geometry_run (asked w t) (List.replicate a true) t hi (hr .output)
  change Runs program p _ _ _ (bank (geometric w a t)) at h1
  have hord:(geometric w a t).geometry .order=List.replicate (order a t) true:=Geom.order_bytes (asked w t) a t
  have ho0:(geometric w a t).auxiliary .orderTodo=[]:=ho
  have hprod:(geometric w a t).product=SemiprimeD1StackUnaryProduct.contents [] [] [] []:=hp
  have hupdate:Function.update (geometric w a t).auxiliary .orderTodo []=(geometric w a t).auxiliary:=Function.update_eq_self_iff.mpr ho0.symm
  have hin:Meta.words (geometric w a t) [] [] [] []=geometric w a t:=by unfold Meta.words;rw [←hprod,hupdate]
  obtain ⟨q,hqBound,h2⟩:=Meta.multiplicity_run (geometric w a t) h u (order a t) hu hord hh hs
  rw [hin] at h2
  change Runs program q _ _ _ (bank (multiplied w a h u t)) at h2
  have h3:=PTrace.copy_call .retained (.local .retained) (.local .clearProduct) rfl
    (bank (multiplied w a h u t)) (List.replicate (h*(u-order a t)) true) [] rfl hz hs
  change Runs program _ _ _ _ (Function.update (bank (multiplied w a h u t)) (aux .retainedQ) (List.replicate (h*(u-order a t)) true++[])) at h3
  rw [List.append_nil,update_added] at h3
  change Runs program _ _ _ _ (bank (saved w a h u t)) at h3
  have h4:=PTrace.drain_loop (.local .clearProduct) (.local (.clearGeometry 0)) (product .product) rfl
    (bank (saved w a h u t)) (List.replicate (h*(u-order a t)) true) rfl
  rw [update_product] at h4
  have hpf:Function.update (saved w a h u t).product .product []=SemiprimeD1StackUnaryProduct.contents [] [] [] []:=by
    funext slot
    cases slot <;> rfl
  rw [hpf] at h4
  change Runs program _ _ _ _ (bank (productCleared w a h u t)) at h4
  obtain ⟨s,hsBound,h5⟩:=Clear.geometry_run (productCleared w a h u t)
  rw [Clear.geometry_cleared] at h5
  change Runs program s _ _ _ (bank (geometryCleared w a h u t)) at h5
  have h6:=PTrace.drain_loop (.local .clearQ) (.local .copySlopes) (oldAux .q) rfl
    (bank (geometryCleared w a h u t)) t rfl
  rw [update_oldAux] at h6
  change Runs program (t.length+1) _ _ _ (bank (result w a h u t)) at h6
  rw [result_eq w a h u t hg hp hq ho] at h6
  have hrun:=PTrace.join (PTrace.join (PTrace.join (PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3) h4) h5) h6
  simp only [List.length_replicate] at hrun hpBound
  refine ⟨(5*t.length+4)+p+q+(5*(h*(u-order a t))+4)+(h*(u-order a t)+1)+s+(t.length+1),?_,hrun⟩
  unfold runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineRetained

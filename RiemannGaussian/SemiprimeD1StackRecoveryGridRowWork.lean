/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridMultiplicity
import RiemannGaussian.SemiprimeD1StackRecoveryGridRowBases
import RiemannGaussian.SemiprimeD1StackRecoveryGridRowSlopes
import RiemannGaussian.SemiprimeD1StackRecoveryGridRowCleanup
/-! # Complete actual non-skipped original-grid row body
The actual geometry order, retained height and u words determine multiplicity
inside this same source. Both actual power loops, all repeated slope frames,
both oriented folds and every physical cleanup execute before advance.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridRowWork
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridOperationInput SemiprimeD1StackRecoveryGridRegisters
open SemiprimeD1StackProcedureTrace
namespace Meta
export SemiprimeD1StackRecoveryGridMultiplicity (words multiplicity_run runBound)
end Meta
namespace Bases
export SemiprimeD1StackRecoveryGridRowBases (result runBound bases_run numerator_nonempty denominator_nonempty numeratorPower powersResult powersBound powers_run)
end Bases
namespace Slopes
export SemiprimeD1StackRecoveryGridRowSlopes (reciprocal slope slope_run slopeBound repeated repeat_run repeatBound folded fold_run foldBound)
end Slopes
namespace Cleanup
export SemiprimeD1StackRecoveryGridRowCleanup (result runBound cleanup_run)
end Cleanup
namespace Call
export SemiprimeD1StackRecoveryGridSite (nonempty_preserved signed_getReg written_nonempty)
end Call
/-- Actual metadata result, after physical level subtraction/product and restoration of every work field. -/
def metadata (w:Words) (h u order:Nat) :Words:=
  {w with product:=SemiprimeD1StackUnaryProduct.contents [] [] [] (List.replicate (h*(u-order)) true)}
/-- Whole actual multiplicity source from its genuine empty product/work boundary. -/
theorem metadata_run (w:Words) (h u order:Nat)
    (hu:w.auxiliary .originalU=List.replicate u true) (ho:w.geometry .order=List.replicate order true)
    (hh:w.division .quotient=List.replicate h true) (hs:w.auxiliary .copyScratch=[])
    (hp:w.product=SemiprimeD1StackUnaryProduct.contents [] [] [] []) (hz:w.auxiliary .orderTodo=[]) :
    ∃q≤Meta.runBound h u order,Runs program q (.local .levels) (bank w) (.local .negative) (bank (metadata w h u order)):=by
  have he:Function.update w.auxiliary .orderTodo []=w.auxiliary:=Function.update_eq_self_iff.mpr hz.symm
  have hi:Meta.words w [] [] [] []=w:=by
    unfold Meta.words
    rw [←hp,he]
  obtain ⟨q,hq,h0⟩:=Meta.multiplicity_run w h u order hu ho hh hs
  rw [hi] at h0
  have hout:Meta.words w [] [] (List.replicate (h*(u-order)) true) []=metadata w h u order:=by
    unfold Meta.words metadata
    rw [he]
  rw [hout] at h0
  exact ⟨q,hq,h0⟩
/-- A physically acquired signed cache remains nonempty after any actual rational cache replacement. -/
theorem put_nonempty (w:Words) (r:Reg) (x:SemiprimeRationalBits.RationalWord) (q:Reg)
    (h:w.registers (q,false)≠[]) :(putReg w r x).registers (q,false)≠[]:=by
  by_cases he:q=r
  · subst q
    rw [(putReg_fields w r x).1]
    exact List.cons_ne_nil _ _
  · rw [putReg_other w r q x false he]
    exact h
/-- The three real base operations retain nonemptiness of every already acquired signed cache. -/
theorem bases_nonempty (w:Words) (width:List Bool) (r:Reg) (h:w.registers (r,false)≠[]) :
    (Bases.result w width).registers (r,false)≠[]:=
  Call.nonempty_preserved .denominatorBase (SemiprimeD1StackRecoveryGridRowBases.numerator w width) width r
    (Call.nonempty_preserved .numeratorBase (SemiprimeD1StackRecoveryGridRowBases.negative w width) width r
      (Call.nonempty_preserved .negativeIndex w width r h))
/-- Both real power replacements retain all previously acquired signed cache shapes. -/
theorem powers_nonempty (w:Words) (width:List Bool) (m:Nat) (r:Reg) (h:w.registers (r,false)≠[]) :
    (Bases.powersResult w width m).registers (r,false)≠[]:=
  put_nonempty (Bases.numeratorPower w width m) .denPower _ r (put_nonempty w .numPower _ r h)
/-- Exact actual base-cache state after multiplicity and the three difference operations. -/
def bases (w:Words) (width:List Bool) (h u order:Nat) :Words:=Bases.result (metadata w h u order) width
/-- Exact actual state after both complete power-source calls. -/
def powers (w:Words) (width:List Bool) (h u order:Nat) :Words:=Bases.powersResult (bases w width h u order) width (h*(u-order))
/-- Exact actual slope state after reciprocal and alpha multiplication. -/
def slope (w:Words) (width:List Bool) (h u order:Nat) :Words:=Slopes.slope (powers w width h u order) width
/-- Exact framed repeated slope occurrences acquired from the actual computed m markers. -/
def framed (w:Words) (width:List Bool) (h u order:Nat) :Words:=
  Slopes.repeated (slope w width h u order) (getReg (slope w width h u order) .slope) (h*(u-order))
/-- Both actual oriented right-fold products. -/
def folded (w:Words) (width:List Bool) (h u order:Nat) :Words:=Slopes.folded (framed w width h u order) width
/-- All physical row work, product and geometry fields are cleared before advance. -/
def result (w:Words) (width:List Bool) (h u order:Nat) :Words:=Cleanup.result (folded w width h u order)
/-- Abstract physical slope/repetition/fold endpoint starting at the actual reciprocal entry. -/
def tailSlope (w:Words) (width:List Bool) :Words:=Slopes.slope w width
/-- Actual repeated slope bytes from the physically retained m markers. -/
def tailFramed (w:Words) (width:List Bool) (m:Nat) :Words:=
  Slopes.repeated (tailSlope w width) (getReg (tailSlope w width) .slope) m
/-- Actual oriented row folds before all physical cleanup. -/
def tailFolded (w:Words) (width:List Bool) (m:Nat) :Words:=Slopes.folded (tailFramed w width m) width
/-- Actual cleaned tail endpoint. -/
def tailResult (w:Words) (width:List Bool) (m:Nat) :Words:=Cleanup.result (tailFolded w width m)
/-- Own actual slope/frame/fold/cleanup clock on an abstract acquired power bank. -/
def tailBound (w:Words) (width:List Bool) (m:Nat) :Nat:=Slopes.slopeBound w width+
  Slopes.repeatBound (getReg (tailSlope w width) .slope) m+
  Slopes.foldBound (tailFramed w width m) width+Cleanup.runBound (tailFolded w width m)
attribute [local irreducible] tailBound tailResult Slopes.slopeBound Slopes.foldBound Cleanup.runBound
/-- All actual slope arithmetic, each occurrence frame, both right folds and physical cleanup execute on the acquired power bank. -/
theorem tail_run (w:Words) (width:List Bool) (m:Nat)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hm:w.product .product=List.replicate m true) (hrep:w.auxiliary .repeatTodo=[]) (hframe:w.auxiliary .frameScratch=[])
    (hdb:w.registers (.denBase,false)≠[]) (ha:w.registers (.alpha,false)≠[])
    (hnp:w.registers (.numPower,false)≠[]) (hdp:w.registers (.denPower,false)≠[])
    (hgn:w.registers (.gridNum,false)≠[]) (hgd:w.registers (.gridDen,false)≠[]) :
    ∃q≤tailBound w width m,Runs program q (.local .reciprocal) (bank w) (.local .advance) (bank (tailResult w width m)):=by
  obtain ⟨p,hp,h0⟩:=Slopes.slope_run w width hr hs hdb ha
  change Runs program p _ _ _ (bank (tailSlope w width)) at h0
  have hslope:(tailSlope w width).registers (.slope,false)≠[]:=Call.written_nonempty .slope (Slopes.reciprocal w width) width
  have h1:=Slopes.repeat_run (tailSlope w width) (getReg (tailSlope w width) .slope) m hm hrep hs hframe
    (Call.signed_getReg _ .slope hslope) rfl
  change Runs program (Slopes.repeatBound (getReg (tailSlope w width) .slope) m) _ _ _ (bank (tailFramed w width m)) at h1
  have preserve (r:Reg) (hcache:w.registers (r,false)≠[]) :(tailFramed w width m).registers (r,false)≠[]:=
    Call.nonempty_preserved .slope (Slopes.reciprocal w width) width r (Call.nonempty_preserved .reciprocal w width r hcache)
  obtain ⟨q,hq,h2⟩:=Slopes.fold_run (tailFramed w width m) width hr hs
    (preserve .numPower hnp) (preserve .gridNum hgn) (preserve .denPower hdp) (preserve .gridDen hgd)
  change Runs program q _ _ _ (bank (tailFolded w width m)) at h2
  obtain ⟨r,hrBound,h3⟩:=Cleanup.cleanup_run (tailFolded w width m)
  have he:Cleanup.result (tailFolded w width m)=tailResult w width m:=by unfold tailResult;rfl
  rw [he] at h3
  refine ⟨p+Slopes.repeatBound (getReg (tailSlope w width) .slope) m+q+r,?_,PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3⟩
  unfold tailBound
  omega
/-- Own whole row clock composes the same actual metadata, differences, powers and physical tail traces. -/
def runBound (w:Words) (width:List Bool) (h u order:Nat) :Nat:=
  Meta.runBound h u order+Bases.runBound (metadata w h u order) width+
  Bases.powersBound (bases w width h u order) width (h*(u-order))+tailBound (powers w width h u order) width (h*(u-order))
attribute [local irreducible] runBound result Meta.runBound Bases.runBound Bases.powersBound
/-- Whole actual non-skipped row from acquired metadata to actual next-row entry; no supplied m, slope, power, answer or operation stream is present. -/
theorem row_work_run (w:Words) (width:List Bool) (h u order:Nat)
    (hu:w.auxiliary .originalU=List.replicate u true) (ho:w.geometry .order=List.replicate order true)
    (hh:w.division .quotient=List.replicate h true) (hs:w.auxiliary .copyScratch=[])
    (hp:w.product=SemiprimeD1StackUnaryProduct.contents [] [] [] []) (hz:w.auxiliary .orderTodo=[])
    (hr:w.rational=emptyRational width) (hpow:w.auxiliary .powerTodo=[])
    (hrep:w.auxiliary .repeatTodo=[]) (hframe:w.auxiliary .frameScratch=[])
    (hi:w.registers (.index,false)≠[]) (hc:w.registers (.center,false)≠[]) (hn:w.registers (.node,false)≠[])
    (ha:w.registers (.alpha,false)≠[]) (hgn:w.registers (.gridNum,false)≠[]) (hgd:w.registers (.gridDen,false)≠[]) :
    ∃q≤runBound w width h u order,Runs program q (.local .levels) (bank w) (.local .advance) (bank (result w width h u order)):=by
  obtain ⟨t0,ht0,h0⟩:=metadata_run w h u order hu ho hh hs hp hz
  obtain ⟨t1,ht1,h1⟩:=Bases.bases_run (metadata w h u order) width hr hs hi hc hn
  change Runs program t1 _ _ _ (bank (bases w width h u order)) at h1
  obtain ⟨t2,ht2,h2⟩:=Bases.powers_run (bases w width h u order) width (h*(u-order)) hr hs hpow rfl
    (Bases.numerator_nonempty (metadata w h u order) width) (Bases.denominator_nonempty (metadata w h u order) width)
  change Runs program t2 _ _ _ (bank (powers w width h u order)) at h2
  have hdBase: (powers w width h u order).registers (.denBase,false)≠[]:=
    powers_nonempty (bases w width h u order) width (h*(u-order)) .denBase (Bases.denominator_nonempty _ width)
  have haPower:(powers w width h u order).registers (.alpha,false)≠[]:=
    powers_nonempty (bases w width h u order) width (h*(u-order)) .alpha (bases_nonempty (metadata w h u order) width .alpha ha)
  have hnp0:(Bases.numeratorPower (bases w width h u order) width (h*(u-order))).registers (.numPower,false)≠[]:=by
    unfold Bases.numeratorPower
    rw [(putReg_fields _ .numPower _).1]
    exact List.cons_ne_nil _ _
  have hnp1:(powers w width h u order).registers (.numPower,false)≠[]:=put_nonempty _ .denPower _ .numPower hnp0
  have hdp1:(powers w width h u order).registers (.denPower,false)≠[]:=by
    unfold powers Bases.powersResult
    rw [(putReg_fields _ .denPower _).1]
    exact List.cons_ne_nil _ _
  have hgn1:=powers_nonempty (bases w width h u order) width (h*(u-order)) .gridNum
    (bases_nonempty (metadata w h u order) width .gridNum hgn)
  have hgd1:=powers_nonempty (bases w width h u order) width (h*(u-order)) .gridDen
    (bases_nonempty (metadata w h u order) width .gridDen hgd)
  obtain ⟨t3,ht3,h3⟩:=tail_run (powers w width h u order) width (h*(u-order)) hr hs rfl hrep hframe
    hdBase haPower hnp1 hdp1 hgn1 hgd1
  have he:tailResult (powers w width h u order) width (h*(u-order))=result w width h u order:=by
    unfold tailResult result tailFolded folded tailFramed framed tailSlope slope
    rfl
  rw [he] at h3
  refine ⟨t0+t1+t2+t3,?_,PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3⟩
  unfold runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridRowWork

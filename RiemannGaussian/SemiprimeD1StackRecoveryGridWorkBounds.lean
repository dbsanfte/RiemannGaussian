/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridStageBounds
import RiemannGaussian.SemiprimeD1StackRecoveryGridRowWork
/-! # Own whole row-body clock from semantic fitted widths and actual emitted bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridWorkBounds
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
namespace Caps
export SemiprimeD1StackRecoveryGridWordCaps (Registers Data auxiliary_data)
export SemiprimeD1StackRecoveryGridBoundaryCaps (metadata_data powers_registers powers_data)
end Caps
namespace S
export SemiprimeD1StackRecoveryGridStageBounds (siteCap powerCap bases_caps bases_le powers_le slopes_caps slopes_le folds_caps folds_le cleanup_le)
end S
namespace W
export SemiprimeD1StackRecoveryGridRowWork (metadata bases powers tailSlope tailFramed tailFolded tailBound runBound)
end W
namespace Slopes
export SemiprimeD1StackRecoveryGridRowSlopes (slope repeated repeatBound)
end Slopes
/-- Physical Frame/tag row length, including every zero/sign/terminator byte. -/
theorem rows_length (x:SemiprimeRationalBits.RationalWord) (m:Nat) (tail:List Bool) :
    (SemiprimeD1StackRecoveryGridRepeats.rows x m tail).length=m*(2*(x.numerator.magnitude.length+x.denominator.length)+5)+tail.length:=by
  induction m generalizing tail with
  | zero=>simp only [SemiprimeD1StackRecoveryGridRepeats.rows,Nat.zero_mul,Nat.zero_add]
  | succ m ih=>
    rw [SemiprimeD1StackRecoveryGridRepeats.rows,ih,SemiprimeD1StackRecoveryGridByteBounds.slopeRow_length]
    ring
/-- The actual slope cache is normalized and twice fitted, including W0. -/
theorem slope_width (w:Words) (width:List Bool) :
    (getReg (Slopes.slope w width) .slope).numerator.magnitude.length=width.length ∧
    (getReg (Slopes.slope w width) .slope).denominator.length=width.length:=by
  unfold Slopes.slope SemiprimeD1StackRecoveryGridSite.result
  change (getReg (putReg _ .slope _) .slope).numerator.magnitude.length=_ ∧ (getReg (putReg _ .slope _) .slope).denominator.length=_
  rw [SemiprimeD1StackRecoveryGridRegisters.getReg_putReg]
  exact SemiprimeD1StackRecoveryGridStateCaps.answer_width .slope _ width
/-- Actual repeated frames enlarge only slopes; accumulated tails are retained and charged once in the word cap. -/
theorem framed_data (w:Words) (width:List Bool) (m B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hr:Caps.Registers w B) (hd:Caps.Data w L)
    (hm:m*(4*width.length+5)≤ L) :
    Caps.Registers (W.tailFramed w width m) B ∧Caps.Data (W.tailFramed w width m) (2*L):=by
  obtain ⟨hr0,hd0⟩:=S.slopes_caps w width B L hW hBL hr hd
  have hx:=slope_width w width
  change (getReg (W.tailSlope w width) .slope).numerator.magnitude.length=width.length ∧ (getReg (W.tailSlope w width) .slope).denominator.length=width.length at hx
  have ht:=hd0 (aux .slopes)
  change ((W.tailSlope w width).auxiliary .slopes).length≤ L at ht
  have hlen:(SemiprimeD1StackRecoveryGridRepeats.rows (getReg (W.tailSlope w width) .slope) m
      ((W.tailSlope w width).auxiliary .slopes)).length≤2*L:=by
    rw [rows_length,hx.1,hx.2]
    have he:2*(width.length+width.length)+5=4*width.length+5:=by omega
    rw [he]
    omega
  refine ⟨hr0,?_⟩
  apply Caps.auxiliary_data _ .slopes _ (2*L) (fun k=>(hd0 k).trans (by omega)) hlen
/-- Real marker-copy and each pair of actual slope frames are explicitly paid. -/
theorem repeats_le (w:Words) (width:List Bool) (m:Nat) :
    Slopes.repeatBound (getReg (W.tailSlope w width) .slope) m≤100*(m+1)*(width.length+1):=by
  have hx:=slope_width w width
  change (getReg (W.tailSlope w width) .slope).numerator.magnitude.length=width.length ∧ (getReg (W.tailSlope w width) .slope).denominator.length=width.length at hx
  unfold Slopes.repeatBound signed
  rw [List.length_cons,hx.1,hx.2]
  nlinarith
attribute [local irreducible] Slopes.repeatBound S.siteCap S.powerCap
/-- Same actual reciprocal/frame/fold/cleanup tail, with all private EOF drains and real returns. -/
theorem tail_le (w:Words) (width:List Bool) (m B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hr:Caps.Registers w B) (hd:Caps.Data w L)
    (hm:m*(4*width.length+5)≤ L) :
    W.tailBound w width m≤2*S.siteCap B L+100*(m+1)*(width.length+1)+2*S.siteCap B (2*L)+3000*(2*L+1):=by
  have h0:=S.slopes_le w width B L hW hBL hr hd
  have h1:=repeats_le w width m
  obtain ⟨hr0,hd0⟩:=framed_data w width m B L hW hBL hr hd hm
  have h2:=S.folds_le (W.tailFramed w width m) width B (2*L) hW (by omega) hr0 hd0
  obtain ⟨_,hd1⟩:=S.folds_caps (W.tailFramed w width m) width B (2*L) hW (by omega) hr0 hd0
  have h3:=S.cleanup_le (W.tailFolded w width m) (2*L) hd1
  unfold W.tailBound
  omega
/-- Own body cap follows the same actual metadata, three differences, two powers and physical framed tail. -/
theorem work_le (w:Words) (width:List Bool) (h u order B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hr:Caps.Registers w B) (hd:Caps.Data w L)
    (hm:h*(u-order)+1≤ L) (hbytes:h*(u-order)*(4*width.length+5)≤ L) :
    W.runBound w width h u order≤100*(h+u+order+1)^2+5*S.siteCap B L+
      2*S.powerCap (h*(u-order)) B L+100*(h*(u-order)+1)*(width.length+1)+2*S.siteCap B (2*L)+3000*(2*L+1):=by
  have h0:=SemiprimeD1StackRecoveryGridMultiplicity.runBound_le h u order
  have hmd:Caps.Data (W.metadata w h u order) L:=Caps.metadata_data w (h*(u-order)) L hd (by omega)
  have h1:=S.bases_le (W.metadata w h u order) width B L hW hBL hr hmd
  obtain ⟨hr1,hd1⟩:=S.bases_caps (W.metadata w h u order) width B L hW hBL hr hmd
  have h2:=S.powers_le (W.bases w width h u order) width (h*(u-order)) B L hW hBL hm hr1 hd1
  have hr2:=Caps.powers_registers (W.bases w width h u order) width (h*(u-order)) B hr1 hW
  have hd2:=Caps.powers_data (W.bases w width h u order) width (h*(u-order)) L hd1 (by omega)
  have h3:=tail_le (W.powers w width h u order) width (h*(u-order)) B L hW hBL hr2 hd2 hbytes
  unfold W.runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridWorkBounds

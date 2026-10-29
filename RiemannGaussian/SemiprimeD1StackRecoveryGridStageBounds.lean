/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridOperationBounds
import RiemannGaussian.SemiprimeD1StackRecoveryGridPowerBounds
import RiemannGaussian.SemiprimeD1StackRecoveryGridBoundaryCaps
import RiemannGaussian.SemiprimeD1StackRecoveryGridRowSlopes
/-! # Same-trace grid stage caps from semantic register/foreign-word bounds -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridStageBounds
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
namespace Caps
export SemiprimeD1StackRecoveryGridWordCaps (Registers Data mass_le put_registers put_data power_width)
export SemiprimeD1StackRecoveryGridStateCaps (site_registers site_data)
end Caps
namespace Call
export SemiprimeD1StackRecoveryGridSite (result runBound)
end Call
namespace Bases
export SemiprimeD1StackRecoveryGridRowBases (negative numerator result runBound numeratorPower powersResult powersBound)
end Bases
namespace Slopes
export SemiprimeD1StackRecoveryGridRowSlopes (reciprocal slope slopeBound numerator folded foldBound)
end Slopes
/-- Uniform actual whole-operation/call/return cap at a genuine boundary. -/
def siteCap (B L:Nat) :Nat:=10^36*(104*L+B^6+1)
/-- Uniform actual whole acquired-count power-source cap. -/
def powerCap (m B L:Nat) :Nat:=10^40*(m+2)*(L+B^6+1)
/-- The parsed physical signed word retains its actual tail/denominator byte bounds. -/
theorem parsed_width (w:Words) (r:Reg) (B:Nat) (hr:Caps.Registers w B) :
    (getReg w r).numerator.magnitude.length≤ B ∧(getReg w r).denominator.length≤ B:=by
  constructor
  · change (w.registers (r,false)).tail.length≤ B
    rw [List.length_tail]
    exact (Nat.sub_le _ _).trans (hr r false)
  · exact hr r true
/-- Included R36 is paid from its actual five source words; all foreign bytes enter only the own cleanup cap. -/
theorem site_le (site:Site) (w:Words) (width:List Bool) (B L:Nat)
    (hB:1≤ B) (hW:width.length≤ B) (hr:Caps.Registers w B) (hd:Caps.Data w L) :
    Call.runBound site w width≤ siteCap B L:=by
  have h:=SemiprimeD1StackRecoveryGridOperationBounds.site_le site w width B hB hW hr
  have hm:=Caps.mass_le w L hd
  exact h.trans (Nat.mul_le_mul_left _ (by omega))
attribute [local irreducible] Call.runBound siteCap powerCap
/-- All three actual difference-base outputs preserve semantic source-word caps. -/
theorem bases_caps (w:Words) (width:List Bool) (B L:Nat) (hW:width.length+2≤ B) (hBL:B≤ L)
    (hr:Caps.Registers w B) (hd:Caps.Data w L) :Caps.Registers (Bases.result w width) B ∧Caps.Data (Bases.result w width) L:=by
  have hr0:=Caps.site_registers .negativeIndex w width B hr (by omega)
  have hd0:=Caps.site_data .negativeIndex w width L hd (by omega)
  have hr1:=Caps.site_registers .numeratorBase (Bases.negative w width) width B hr0 (by omega)
  have hd1:=Caps.site_data .numeratorBase (Bases.negative w width) width L hd0 (by omega)
  exact ⟨Caps.site_registers .denominatorBase (Bases.numerator w width) width B hr1 (by omega),
    Caps.site_data .denominatorBase (Bases.numerator w width) width L hd1 (by omega)⟩
/-- Actual three-site row-base clock is a sum of the same three actual bounded calls. -/
theorem bases_le (w:Words) (width:List Bool) (B L:Nat) (hW:width.length+2≤ B) (hBL:B≤ L)
    (hr:Caps.Registers w B) (hd:Caps.Data w L) :Bases.runBound w width≤3*siteCap B L:=by
  have h0:=site_le .negativeIndex w width B L (by omega) (by omega) hr hd
  have hr0:=Caps.site_registers .negativeIndex w width B hr (by omega)
  have hd0:=Caps.site_data .negativeIndex w width L hd (by omega)
  have h1:=site_le .numeratorBase (Bases.negative w width) width B L (by omega) (by omega) hr0 hd0
  have hr1:=Caps.site_registers .numeratorBase (Bases.negative w width) width B hr0 (by omega)
  have hd1:=Caps.site_data .numeratorBase (Bases.negative w width) width L hd0 (by omega)
  have h2:=site_le .denominatorBase (Bases.numerator w width) width B L (by omega) (by omega) hr1 hd1
  unfold Bases.runBound
  omega
/-- Both actual copied-m power calls have the same cap, including m0 literal one and both real returns. -/
theorem powers_le (w:Words) (width:List Bool) (m B L:Nat) (hW:width.length+2≤ B) (hBL:B≤ L) (hm:m+1≤ L)
    (hr:Caps.Registers w B) (hd:Caps.Data w L) :Bases.powersBound w width m≤2*powerCap m B L:=by
  have hx:=parsed_width w .numBase B hr
  have h0:=SemiprimeD1StackRecoveryGridPowerBounds.source_le .numerator w width (getReg w .numBase) m B L hW hBL hx.1 hx.2 hm hr hd
  have hn:=Caps.power_width width (getReg w .numBase) m B hW
  have hr1:=Caps.put_registers w .numPower _ B hr hn.1 hn.2
  have hd1:=Caps.put_data w .numPower _ L hd (hn.1.trans hBL) (hn.2.trans hBL)
  have hy:=parsed_width (Bases.numeratorPower w width m) .denBase B hr1
  have h1:=SemiprimeD1StackRecoveryGridPowerBounds.source_le .denominator (Bases.numeratorPower w width m) width
    (getReg (Bases.numeratorPower w width m) .denBase) m B L hW hBL hy.1 hy.2 hm hr1 hd1
  unfold Bases.powersBound powerCap
  omega
/-- Both actual slope-cache writes preserve all semantic register and foreign-word caps. -/
theorem slopes_caps (w:Words) (width:List Bool) (B L:Nat) (hW:width.length+2≤ B) (hBL:B≤ L)
    (hr:Caps.Registers w B) (hd:Caps.Data w L) :Caps.Registers (Slopes.slope w width) B ∧Caps.Data (Slopes.slope w width) L:=by
  have hr0:=Caps.site_registers .reciprocal w width B hr (by omega)
  have hd0:=Caps.site_data .reciprocal w width L hd (by omega)
  exact ⟨Caps.site_registers .slope (Slopes.reciprocal w width) width B hr0 (by omega),
    Caps.site_data .slope (Slopes.reciprocal w width) width L hd0 (by omega)⟩
/-- The actual reciprocal/slope stage is two same-source operation calls. -/
theorem slopes_le (w:Words) (width:List Bool) (B L:Nat) (hW:width.length+2≤ B) (hBL:B≤ L)
    (hr:Caps.Registers w B) (hd:Caps.Data w L) :Slopes.slopeBound w width≤2*siteCap B L:=by
  have h0:=site_le .reciprocal w width B L (by omega) (by omega) hr hd
  have hr0:=Caps.site_registers .reciprocal w width B hr (by omega)
  have hd0:=Caps.site_data .reciprocal w width L hd (by omega)
  have h1:=site_le .slope (Slopes.reciprocal w width) width B L (by omega) (by omega) hr0 hd0
  unfold Slopes.slopeBound
  omega
/-- Both oriented row folds preserve semantic cache and foreign-data caps. -/
theorem folds_caps (w:Words) (width:List Bool) (B L:Nat) (hW:width.length+2≤ B) (hBL:B≤ L)
    (hr:Caps.Registers w B) (hd:Caps.Data w L) :Caps.Registers (Slopes.folded w width) B ∧Caps.Data (Slopes.folded w width) L:=by
  have hr0:=Caps.site_registers .numeratorFold w width B hr (by omega)
  have hd0:=Caps.site_data .numeratorFold w width L hd (by omega)
  exact ⟨Caps.site_registers .denominatorFold (Slopes.numerator w width) width B hr0 (by omega),
    Caps.site_data .denominatorFold (Slopes.numerator w width) width L hd0 (by omega)⟩
/-- Both right-fold multiplications have the same actual per-site cap. -/
theorem folds_le (w:Words) (width:List Bool) (B L:Nat) (hW:width.length+2≤ B) (hBL:B≤ L)
    (hr:Caps.Registers w B) (hd:Caps.Data w L) :Slopes.foldBound w width≤2*siteCap B L:=by
  have h0:=site_le .numeratorFold w width B L (by omega) (by omega) hr hd
  have hr0:=Caps.site_registers .numeratorFold w width B hr (by omega)
  have hd0:=Caps.site_data .numeratorFold w width L hd (by omega)
  have h1:=site_le .denominatorFold (Slopes.numerator w width) width B L (by omega) (by omega) hr0 hd0
  unfold Slopes.foldBound
  omega
/-- All27 physical row cleanup roles and EOF branches retain a linear cap in actual boundary words. -/
theorem cleanup_le (w:Words) (L:Nat) (hd:Caps.Data w L) :SemiprimeD1StackRecoveryGridRowCleanup.runBound w≤3000*(L+1):=by
  have hm0:=Caps.mass_le w L hd
  have hp:=SemiprimeD1StackRecoveryGridBoundaryCaps.row_product_data w L hd
  have hm1:=Caps.mass_le (SemiprimeD1StackRecoveryGridRowCleanup.productCleared w) L hp
  have hprod:=hd (productStack .product)
  change (w.product .product).length≤L at hprod
  unfold SemiprimeD1StackRecoveryGridRowCleanup.runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridStageBounds

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridStageBounds
import RiemannGaussian.SemiprimeD1StackRecoveryGridFinal
/-! # Same-trace scalar/argument finish cap from semantic word widths -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridFinalBounds
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
namespace Caps
export SemiprimeD1StackRecoveryGridWordCaps (Registers Data mass_le)
export SemiprimeD1StackRecoveryGridStateCaps (site_registers site_data)
end Caps
namespace Call
export SemiprimeD1StackRecoveryGridSite (runBound)
end Call
namespace Stage
export SemiprimeD1StackRecoveryGridStageBounds (siteCap site_le)
end Stage
namespace F
export SemiprimeD1StackRecoveryGridFinal (inverseDen scalar front frontBound tailPoint tailAlpha tailResult tailBound argument cleanupBound runBound)
end F
attribute [local irreducible] Call.runBound Stage.siteCap
/-- All first three actual final-cache writes preserve both semantic register and data caps. -/
theorem front_caps (w:Words) (width:List Bool) (B L:Nat) (hW:width.length+2≤ B) (hBL:B≤ L)
    (hr:Caps.Registers w B) (hd:Caps.Data w L) :Caps.Registers (F.front w width) B ∧Caps.Data (F.front w width) L:=by
  have hr0:=Caps.site_registers .scalarInverse w width B hr (by omega)
  have hd0:=Caps.site_data .scalarInverse w width L hd (by omega)
  have hr1:=Caps.site_registers .scalar (F.inverseDen w width) width B hr0 (by omega)
  have hd1:=Caps.site_data .scalar (F.inverseDen w width) width L hd0 (by omega)
  exact ⟨Caps.site_registers .negativeNode (F.scalar w width) width B hr1 (by omega),
    Caps.site_data .negativeNode (F.scalar w width) width L hd1 (by omega)⟩
/-- Own actual front finish clock is the same three bounded real site calls. -/
theorem front_le (w:Words) (width:List Bool) (B L:Nat) (hW:width.length+2≤ B) (hBL:B≤ L)
    (hr:Caps.Registers w B) (hd:Caps.Data w L) :F.frontBound w width≤3*Stage.siteCap B L:=by
  have h0:=Stage.site_le .scalarInverse w width B L (by omega) (by omega) hr hd
  have hr0:=Caps.site_registers .scalarInverse w width B hr (by omega)
  have hd0:=Caps.site_data .scalarInverse w width L hd (by omega)
  have h1:=Stage.site_le .scalar (F.inverseDen w width) width B L (by omega) (by omega) hr0 hd0
  have hr1:=Caps.site_registers .scalar (F.inverseDen w width) width B hr0 (by omega)
  have hd1:=Caps.site_data .scalar (F.inverseDen w width) width L hd0 (by omega)
  have h2:=Stage.site_le .negativeNode (F.scalar w width) width B L (by omega) (by omega) hr1 hd1
  unfold F.frontBound
  omega
/-- All three actual local-argument writes preserve the same semantic cache widths. -/
theorem tail_caps (w:Words) (width:List Bool) (B L:Nat) (hW:width.length+2≤ B) (hBL:B≤ L)
    (hr:Caps.Registers w B) (hd:Caps.Data w L) :Caps.Registers (F.tailResult w width) B ∧Caps.Data (F.tailResult w width) L:=by
  have hr0:=Caps.site_registers .point w width B hr (by omega)
  have hd0:=Caps.site_data .point w width L hd (by omega)
  have hr1:=Caps.site_registers .inverseAlpha (F.tailPoint w width) width B hr0 (by omega)
  have hd1:=Caps.site_data .inverseAlpha (F.tailPoint w width) width L hd0 (by omega)
  exact ⟨Caps.site_registers .argument (F.tailAlpha w width) width B hr1 (by omega),
    Caps.site_data .argument (F.tailAlpha w width) width L hd1 (by omega)⟩
/-- Own actual local-argument clock is three bounded real site calls. -/
theorem tail_le (w:Words) (width:List Bool) (B L:Nat) (hW:width.length+2≤ B) (hBL:B≤ L)
    (hr:Caps.Registers w B) (hd:Caps.Data w L) :F.tailBound w width≤3*Stage.siteCap B L:=by
  have h0:=Stage.site_le .point w width B L (by omega) (by omega) hr hd
  have hr0:=Caps.site_registers .point w width B hr (by omega)
  have hd0:=Caps.site_data .point w width L hd (by omega)
  have h1:=Stage.site_le .inverseAlpha (F.tailPoint w width) width B L (by omega) (by omega) hr0 hd0
  have hr1:=Caps.site_registers .inverseAlpha (F.tailPoint w width) width B hr0 (by omega)
  have hd1:=Caps.site_data .inverseAlpha (F.tailPoint w width) width L hd0 (by omega)
  have h2:=Stage.site_le .argument (F.tailAlpha w width) width B L (by omega) (by omega) hr1 hd1
  unfold F.tailBound
  omega
/-- Every transient/q byte and EOF branch is counted after the actual final arithmetic. -/
theorem cleanup_le (w:Words) (L:Nat) (hd:Caps.Data w L) :F.cleanupBound w≤2000*(L+1):=by
  have hm:=Caps.mass_le w L hd
  have hq:=hd (aux .q)
  change (w.auxiliary .q).length≤ L at hq
  unfold F.cleanupBound
  omega
/-- Whole same-program final finish has six actual arithmetic calls and all physical cleanup. -/
theorem finish_le (w:Words) (width:List Bool) (B L:Nat) (hW:width.length+2≤ B) (hBL:B≤ L)
    (hr:Caps.Registers w B) (hd:Caps.Data w L) :F.runBound w width≤6*Stage.siteCap B L+2000*(L+1):=by
  have h0:=front_le w width B L hW hBL hr hd
  obtain ⟨hr0,hd0⟩:=front_caps w width B L hW hBL hr hd
  have h1:=tail_le (F.front w width) width B L hW hBL hr0 hd0
  obtain ⟨_,hd1⟩:=tail_caps (F.front w width) width B L hW hBL hr0 hd0
  have h2:=cleanup_le (F.argument w width) L hd1
  unfold F.runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridFinalBounds

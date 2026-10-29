/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridWordCaps
import RiemannGaussian.SemiprimeD1StackRecoveryGridGeometry
import RiemannGaussian.SemiprimeD1StackRecoveryGridSite
/-! # Actual arithmetic/geometry boundary word-cap preservation -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridStateCaps
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
namespace Caps
export SemiprimeD1StackRecoveryGridWordCaps (Registers Data put_registers put_data)
end Caps
namespace Site
export SemiprimeD1StackRecoveryGridSite (answer result)
end Site
namespace Geometry
export SemiprimeD1StackRecoveryGridGeometry (result)
end Geometry
/-- Both actual site outputs have exactly W bytes; the sign is one separate actual byte. -/
theorem answer_width (site:SemiprimeD1StackRecoveryGrid.Site) (w:Words) (width:List Bool) :
    (Site.answer site w width).numerator.magnitude.length=width.length ∧(Site.answer site w width).denominator.length=width.length:=
  SemiprimeD1StackRecoveryGridByteBounds.operation_lengths _ _ _ width
/-- Actual whole-operation cache writes retain a semantic register-width cap. -/
theorem site_registers (site:SemiprimeD1StackRecoveryGrid.Site) (w:Words) (width:List Bool) (B:Nat)
    (hw:Caps.Registers w B) (hW:width.length+1≤ B) :Caps.Registers (Site.result site w width) B:=by
  have h:=answer_width site w width
  exact Caps.put_registers w _ _ B hw (by omega) (by omega)
/-- Actual whole-operation cache writes leave foreign data words untouched and preserve their physical cap. -/
theorem site_data (site:SemiprimeD1StackRecoveryGrid.Site) (w:Words) (width:List Bool) (L:Nat)
    (hw:Caps.Data w L) (hW:width.length+1≤ L) :Caps.Data (Site.result site w width) L:=by
  have h:=answer_width site w width
  exact Caps.put_data w _ _ L hw (by omega) (by omega)
/-- SAME closed actual fourteen-role source bounds every acquired geometry word; no legacy metadata-work clock is used. -/
theorem geometry_word (a q:List Bool) (k:G.Stack) :
    (SemiprimeD1StackPhaseGeometryComponents.result a q k).length≤20000*(a.length+q.length+1):=by
  obtain ⟨s,_,hr⟩:=SemiprimeD1StackPhaseGeometryExecution.source_run a q
  have hc:=SemiprimeD1StackPhaseGeometryBounds.prefix_cells a q s (SemiprimeD1StackPhaseGeometryExecution.done a q) hr
  have hs:(SemiprimeD1StackPhaseGeometryComponents.result a q k).length≤
      ∑j:G.Stack,(SemiprimeD1StackPhaseGeometryComponents.result a q j).length:=
    Finset.single_le_sum (f:=fun j:G.Stack=>(SemiprimeD1StackPhaseGeometryComponents.result a q j).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
  change (∑j:G.Stack,(SemiprimeD1StackPhaseGeometryComponents.result a q j).length)+0≤_ at hc
  omega
/-- Real geometry output/drain does not alter rational cache registers. -/
theorem geometry_registers (w:Words) (a q:List Bool) (B:Nat) (hw:Caps.Registers w B) :Caps.Registers (Geometry.result w a q) B:=hw
/-- Exactly the acquired physical geometry words change; both displaced original shadows and all other100 roles retain their actual caps. -/
theorem geometry_data (w:Words) (a q:List Bool) (L:Nat) (hw:Caps.Data w L)
    (hg:20000*(a.length+q.length+1)≤ L) :Caps.Data (Geometry.result w a q) L:=by
  intro k
  rcases k with k|k
  · exact hw (rationalStack k)
  · rcases k with k|k
    · change (if k=.exponent ∨k=.index then w.geometry k else SemiprimeD1StackPhaseGeometryComponents.result a q (.inr k)).length≤ L
      split
      · exact hw (geometryAux k)
      · exact (geometry_word a q (.inr k)).trans hg
    · rcases k with k|k
      · exact hw (divisionStack k)
      · rcases k with k|k
        · exact hw (productStack k)
        · rcases k with k|k
          · exact hw (reg k.1 k.2)
          · exact hw (aux k)
end RiemannGaussian.SemiprimeD1StackRecoveryGridStateCaps

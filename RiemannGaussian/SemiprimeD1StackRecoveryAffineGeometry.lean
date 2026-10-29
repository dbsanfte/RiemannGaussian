/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCleanup
import RiemannGaussian.SemiprimeD1StackRecoveryAffineMultiplicity
/-! # True physical geometry and shared-point cleanup before retained-q acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineGeometry
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackRecoveryAffineCalls
open SemiprimeD1StackProcedureTrace
/-- Only actual true geometry fields are retained after physically draining the shared raw point output. -/
def result (w:Words) (a t:List Bool):Words:={w with geometry:=(geometryResult w a t).geometry}
/-- Actual G14 source and actual point drain restore the entire real R36 bank, including its readonly width. -/
theorem geometry_run (w:Words) (a t:List Bool)
    (hi:∀slot,bank w (geometry slot)=SemiprimeD1StackPhaseGeometry.input a t slot)
    (ho:w.rational (SemiprimeD1StackRationalOperation.adderStack .output)=[]):
    ∃q≤SemiprimeD1StackPhaseGeometryComponents.runBound a t+1+
      (SemiprimeD1StackPhaseGeometryArithmetic.magnitude a.length t).length+1,
      Runs program q (.local .geometry) (bank w) (.local .levels) (bank (result w a t)):=by
  obtain ⟨q,hq,h0⟩:=geometry_call w a t hi
  have h1:=PTrace.drain_loop (.local .clearPoint) (.local .levels)
    (grid (SemiprimeD1StackRecoveryGrid.rippleStack .output)) rfl (bank (geometryResult w a t))
    (SemiprimeD1StackPhaseGeometryArithmetic.magnitude a.length t) rfl
  change Runs program _ _ _ _ (Function.update (bank (geometryResult w a t))
    (rational (SemiprimeD1StackRationalOperation.adderStack .output)) []) at h1
  rw [update_rational] at h1
  have he:({geometryResult w a t with rational:=Function.update (geometryResult w a t).rational (SemiprimeD1StackRationalOperation.adderStack .output) []}:Words)=result w a t:=by
    dsimp only [geometryResult,result]
    rw [Function.update_idem,←ho,Function.update_eq_self]
  rw [he] at h1
  exact ⟨q+((SemiprimeD1StackPhaseGeometryArithmetic.magnitude a.length t).length+1),by omega,PTrace.join h0 h1⟩
/-- The actual order word is exactly the physically scanned magnitude valuation, before any original numeric interpretation. -/
theorem order_bytes (w:Words) (a:Nat) (t:List Bool):
    (result w (List.replicate a true) t).geometry .order=
      List.replicate (SemiprimeD1StackRecoveryGridRow.order a t) true:=by
  change List.replicate (SemiprimeD1StackPhaseGeometryArithmetic.valuation
    (SemiprimeD1StackPhaseGeometryArithmetic.magnitude (List.replicate a true).length t)) true=_
  rw [List.length_replicate]
  rfl
/-- Original selected-node bounds identify true physical retained-q arithmetic, including center0 and order=a. -/
theorem retained_original (a M u:Nat) (selected:Fin (2^(a+1))) (t:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    SemiprimeD1TaperedLoss.height M u*(u-SemiprimeD1StackRecoveryGridRow.order a t)=
      SemiprimeD1JetRecoveryGrid.nodeMultiplicity a (SemiprimeD1TaperedLoss.height M u) u selected.val:=by
  have h:=SemiprimeD1StackRecoveryGridOriginalStep.multiplicity_original a M u selected.val selected.val t ht selected.isLt
  have hv:=SemiprimeD1RecoveryWeightRun.multiplicityRun_value a (SemiprimeD1TaperedLoss.height M u) u selected.val selected.val selected.isLt
  exact h.trans hv
end RiemannGaussian.SemiprimeD1StackRecoveryAffineGeometry

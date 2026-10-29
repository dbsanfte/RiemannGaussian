/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridCleanup
/-! # Actual geometry calls and physical shared-ripple cleanup in Grid104 -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridGeometry
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridCleanup SemiprimeD1StackRecoveryGridInventory
open SemiprimeD1StackProcedureTrace
/-- Geometry-only stopped view: every acquired true field is retained independently of fitted coefficients. -/
def result (w:Words) (a q:List Bool) :Words:=
  {w with geometry:=(geometryResult w a q).geometry}
/-- The two literal whole-grid geometry call sites. -/
def entry :ClearSite→Label
  | .initial=>.local .initialGeometry | .row=>.local .rowGeometry
/-- The shared physical point-word cleanup immediately following the actual geometry call. -/
def clear :ClearSite→Label
  | .initial=>.local .initialClearPoint | .row=>.local .rowClearPoint
/-- Actual continuation after all point bytes have been popped. -/
def after :ClearSite→Label
  | .initial=>.local (.decrement .initial) | .row=>.local .center
/-- The real geometry call and whole point drain preserve all original104 words outside acquired geometry fields. -/
theorem geometry_run (part:ClearSite) (w:Words) (a q:List Bool)
    (hi:∀k,bank w (geometryStack k)=SemiprimeD1StackPhaseGeometry.input a q k)
    (ho:w.rational (SemiprimeD1StackRationalOperation.adderStack .output)=[]) :
    ∃t≤SemiprimeD1StackPhaseGeometryComponents.runBound a q+1+
      (SemiprimeD1StackPhaseGeometryArithmetic.magnitude a.length q).length+1,
      Runs program t (entry part) (bank w) (after part) (bank (result w a q)):=by
  have hc:program (entry part)=.call (.geometry .start) (clear part):=by cases part <;> rfl
  obtain ⟨t,ht,h0⟩:=geometry_call w a q (entry part) (clear part) hc hi
  have hd:program (clear part)=.base (.pop (rippleStack .output) (after part) (clear part) (clear part)):=by cases part <;> rfl
  have h1:=PTrace.drain_loop (clear part) (after part) (rippleStack .output) hd (bank (geometryResult w a q))
    (SemiprimeD1StackPhaseGeometryArithmetic.magnitude a.length q) rfl
  change Runs program _ _ _ _ (Function.update (bank (geometryResult w a q))
    (rationalStack (SemiprimeD1StackRationalOperation.adderStack .output)) []) at h1
  rw [update_rational] at h1
  have he:({geometryResult w a q with rational:=Function.update (geometryResult w a q).rational (SemiprimeD1StackRationalOperation.adderStack .output) []}:Words)=result w a q:=by
    dsimp only [geometryResult,result]
    rw [Function.update_idem,←ho,Function.update_eq_self]
  rw [he] at h1
  exact ⟨t+((SemiprimeD1StackPhaseGeometryArithmetic.magnitude a.length q).length+1),by omega,PTrace.join h0 h1⟩
/-- All ten allocated geometry roles, including both displaced empty shadows, are covered by actual cleanup. -/
theorem geometry_cleared (w:Words) :
    cleared (fun i:Fin 10=>geometryAux (geometryRole i)) (bank w) 10=
      bank {w with geometry:=fun _=>[]}:=by
  classical
  funext k
  rw [cleared_full]
  rcases k with k|k
  · simp only [roles,List.mem_map,List.mem_finRange,true_and]
    have hn:¬∃i:Fin 10,geometryAux (geometryRole i)=Sum.inl k:=by rintro ⟨i,hi⟩;cases hi
    simp only [hn,ite_false]
    rfl
  · rcases k with k|k
    · obtain ⟨i,hi⟩:=geometryRole_complete k
      have hm:geometryAux k∈roles (fun i:Fin 10=>geometryAux (geometryRole i)):=by
        apply List.mem_map.mpr
        exact ⟨i,List.mem_finRange i,congrArg geometryAux hi⟩
      exact ite_eq_left hm
    · have hn:¬Sum.inr (Sum.inr k)∈roles (fun i:Fin 10=>geometryAux (geometryRole i)):=by
        simp only [roles,List.mem_map,List.mem_finRange,true_and]
        rintro ⟨i,hi⟩
        cases hi
      simp only [hn,ite_false]
      rfl
end RiemannGaussian.SemiprimeD1StackRecoveryGridGeometry

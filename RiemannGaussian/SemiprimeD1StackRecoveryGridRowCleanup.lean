/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridTransient
import RiemannGaussian.SemiprimeD1StackRecoveryGridGeometry
/-! # Complete actual row cleanup before the decreasing-grid continuation -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridRowCleanup
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridCleanup SemiprimeD1StackProcedureTrace
namespace Transient
export SemiprimeD1StackRecoveryGridTransient (result transient_run)
end Transient
/-- Actual product drain follows all sixteen actual transient-cache drains. -/
def productCleared (w:Words) :Words:=
  {Transient.result w with product:=Function.update w.product .product []}
/-- Entire acquired true-geometry bank, including displaced shadows, is then physically cleared. -/
def result (w:Words) :Words:={productCleared w with geometry:=fun _=>[]}
/-- Own actual row cleanup clock charges actual words at both successive physical cleanup boundaries. -/
def runBound (w:Words) :Nat:=
  16*(mass (bank w)+1)+(w.product .product).length+1+10*(mass (bank (productCleared w))+1)
attribute [local irreducible] result runBound mass
/-- All27 actual transient/product/geometry roles and every EOF branch execute before the actual next-row test. -/
theorem cleanup_run (w:Words) :
    ∃q≤runBound w,Runs program q (.local (.clearTransient false 0)) (bank w) (.local .advance) (bank (result w)):=by
  obtain ⟨p,hp,h0⟩:=Transient.transient_run false w
  have h1:=PTrace.drain_loop (.local .clearMultiplicity) (.local (.clearGeometry .row 0)) (productStack .product) rfl
    (bank (Transient.result w)) (w.product .product) rfl
  rw [update_product] at h1
  change Runs program _ _ _ _ (bank (productCleared w)) at h1
  obtain ⟨q,hq,h2⟩:=geometry_cleanup .row (bank (productCleared w))
  rw [SemiprimeD1StackRecoveryGridGeometry.geometry_cleared] at h2
  change Runs program q _ _ (.local .advance) _ at h2
  have he:({productCleared w with geometry:=fun _=>[]}:Words)=result w:=by unfold result;rfl
  rw [he] at h2
  refine ⟨p+((w.product .product).length+1)+q,?_,PTrace.join (PTrace.join h0 h1) h2⟩
  unfold runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridRowCleanup

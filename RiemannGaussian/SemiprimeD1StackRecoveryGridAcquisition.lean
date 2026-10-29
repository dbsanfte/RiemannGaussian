/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridSetup
import RiemannGaussian.SemiprimeD1StackRecoveryGridHeight
import RiemannGaussian.SemiprimeD1StackRecoveryGridNode
import RiemannGaussian.SemiprimeD1StackRecoveryGridGeometry
/-! # Actual original-input grid acquisition through true geometry
Every grid dimension, height, node word and geometry field below is acquired
inside the same fixed five-tape program, not supplied to the rational fold.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridAcquisition
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackProcedureTrace
namespace Setup
export SemiprimeD1StackRecoveryGridSetup (grown setup_run runBound)
end Setup
namespace Height
export SemiprimeD1StackRecoveryGridHeight (words height_run)
end Height
namespace Node
export SemiprimeD1StackRecoveryGridNode (node_run runBound fit_index)
end Node
namespace Geometry
export SemiprimeD1StackRecoveryGridGeometry (result geometry_run)
end Geometry
/-- Actual height source endpoint within the whole retained original-input bank. -/
def height (a M u:Nat) (t width:List Bool) :Words:=
  Height.words (Setup.grown a (List.replicate M true) (List.replicate u true) t width) [] []
    (List.replicate ((3*M+u-1)/u) true) []
/-- Actual fitted binary node cache; the index template is physically acquired from a. -/
def node (a M u:Nat) (t width:List Bool) :Words:=
  let w:=height a M u t width
  {w with registers:=Function.update (Function.update w.registers (.node,false) (false::SemiprimeD1StackWordFitExecution.result t (List.replicate (a+2) false))) (.node,true) [true]}
/-- The original binary t is physically copied into the first true geometry input. -/
def queried (a M u:Nat) (t width:List Bool) :Words:=
  let w:=node a M u t width
  {w with auxiliary:=Function.update w.auxiliary .q t}
/-- Complete originally acquired true geometry at the actual next decrement instruction. -/
def result (a M u:Nat) (t width:List Bool) :Words:=
  Geometry.result (queried a M u t width) (List.replicate a true) t
/-- Own whole acquisition-prefix clock, including all physical copies, doublings, division, fitting, geometry and point cleanup. -/
def runBound (a M u:Nat) (t _width:List Bool) :Nat:=
  Setup.runBound a+1000*(M+u+1)+Node.runBound t (List.replicate (a+2) false)+(5*t.length+4)+
    (SemiprimeD1StackPhaseGeometryComponents.runBound (List.replicate a true) t+1+
      (SemiprimeD1StackPhaseGeometryArithmetic.magnitude a t).length+1)
/-- True whole original-input acquisition; no native geometry, grid size, height or digit getter occurs in its front door. -/
theorem acquisition_run (a M u:Nat) (t width:List Bool) :
    ∃q≤runBound a M u t width,Runs program q (.local .start)
      (input (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
      (.local (.decrement .initial)) (bank (result a M u t width)):=by
  let w:=Setup.grown a (List.replicate M true) (List.replicate u true) t width
  have h0:=Setup.setup_run a (List.replicate M true) (List.replicate u true) t width
  have hw:Height.words w [] [] [] []=w:=by
    unfold Height.words
    congr 1
    funext k
    cases k <;> rfl
  obtain ⟨q,hq,h1⟩:=Height.height_run w M u rfl rfl rfl
  rw [hw] at h1
  change Runs program q _ _ _ (bank (height a M u t width)) at h1
  have h2:=Node.node_run (height a M u t width) t (List.replicate (a+2) false)
    rfl rfl rfl rfl rfl rfl rfl rfl
  change Runs program (Node.runBound t (List.replicate (a+2) false)) _ _ _ (bank (node a M u t width)) at h2
  have h3:=PTrace.copy_call .originalT (.local .originalT) (.local .initialGeometry) rfl
    (bank (node a M u t width)) t [] rfl rfl rfl
  change Runs program (5*t.length+4) _ _ _ (Function.update _ (aux .q) (t++[])) at h3
  rw [List.append_nil,update_auxiliary] at h3
  change Runs program (5*t.length+4) _ _ _ (bank (queried a M u t width)) at h3
  have hi:∀k,bank (queried a M u t width) (geometryStack k)=
      SemiprimeD1StackPhaseGeometry.input (List.replicate a true) t k:=by
    intro k
    rcases k with k|k <;> cases k <;> rfl
  obtain ⟨s,hs,h4⟩:=Geometry.geometry_run .initial (queried a M u t width) (List.replicate a true) t hi rfl
  have h:=PTrace.join (PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3) h4
  refine ⟨Setup.runBound a+q+Node.runBound t (List.replicate (a+2) false)+(5*t.length+4)+s,?_,h⟩
  unfold runBound
  simp only [List.length_replicate] at hs
  omega
/-- The acquired original-node bytes agree exactly with the legacy index, including sign and high zero padding. -/
theorem node_original (a M u q:Nat) (t width:List Bool)
    (hv:SemiprimeBitArithmetic.bitValue t=q) (hq:q<2^(a+1)) :
    getReg (node a M u t width) .node=(SemiprimeD1RecoveryGridBits.index a q).word:=by
  have he:=Node.fit_index a q t hv hq
  change (⟨⟨false,SemiprimeD1StackWordFitExecution.result t (List.replicate (a+2) false)⟩,[true]⟩:
    SemiprimeRationalBits.RationalWord)=_
  rw [he]
  rfl
end RiemannGaussian.SemiprimeD1StackRecoveryGridAcquisition

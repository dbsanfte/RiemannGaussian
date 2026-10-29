/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridAcquisition
import RiemannGaussian.SemiprimeD1StackRecoveryGridDecrement
import RiemannGaussian.SemiprimeD1StackRecoveryGridPowerSource
/-! # Original five-tape source through the actual first descending-grid row
All true dimensions, initial geometry, binary q=N−1 and both fitted center/alpha
words are physically acquired before the fixed row loop starts.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridFront
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridOperationInput SemiprimeD1StackRecoveryGridCleanup
open SemiprimeD1StackRecoveryGridRegisters SemiprimeD1StackProcedureTrace
namespace Acquire
export SemiprimeD1StackRecoveryGridAcquisition (result runBound acquisition_run)
end Acquire
namespace Dec
export SemiprimeD1StackRecoveryGridDecrement (difference decrement_run runBound difference_value)
end Dec
namespace Power
export SemiprimeD1StackRecoveryGridPowerSource (power_source_run runBound)
end Power
/-- Actual binary true grid size emitted by the frozen geometry call, independent of fitted rational W. -/
def sizeWord (a:Nat) :List Bool:=SemiprimeD1StackPhaseGeometryArithmetic.powerWord (a+1)
/-- Actual acquired q=N−1 following real subtraction of one from true alpha. -/
def decremented (a M u:Nat) (t width:List Bool) :Words:=
  {Acquire.result a M u t width with auxiliary:=Function.update (Acquire.result a M u t width).auxiliary .q (Dec.difference (sizeWord a))}
/-- Physical cleanup includes both displaced geometry shadows and retains the actual a/q aliases. -/
def clean (a M u:Nat) (t width:List Bool) :Words:=
  {decremented a M u t width with geometry:=fun _=>[]}
/-- Actual fitted center power, including literal one at a0/W0. -/
def centered (a M u:Nat) (t width:List Bool) :Words:=
  putReg (clean a M u t width) .center (SemiprimeD1RecoveryPowerBits.power width SemiprimeD1RecoveryGridBits.twoWord a).word
/-- Complete real first-row bank, with actual alpha power and all source/grid fields retained. -/
def result (a M u:Nat) (t width:List Bool) :Words:=
  putReg (centered a M u t width) .alpha (SemiprimeD1RecoveryPowerBits.power width SemiprimeD1RecoveryGridBits.twoWord (a+1)).word
/-- Complete real rational bank remains clean at the acquired-geometry boundary. -/
theorem acquired_rational (a M u:Nat) (t width:List Bool) :
    (Acquire.result a M u t width).rational=emptyRational width:=by
  rw [SemiprimeD1StackRecoveryGridOperation.emptyRational_explicit]
  funext k
  change Function.update (fun _=>[]) (SemiprimeD1StackRationalOperation.aux .template) width k=_
  by_cases hk:k=SemiprimeD1StackRationalOperation.aux .template
  · subst k;rfl
  · simp only [Function.update_of_ne hk,ite_eq_right hk]
/-- Actual geometry alpha is genuinely positive for every a, including a0. -/
theorem size_positive (a:Nat) :0<SemiprimeBitArithmetic.bitValue (sizeWord a):=by
  rw [sizeWord,SemiprimeD1StackPhaseGeometryArithmetic.powerWord_value]
  exact pow_pos (by decide) _
/-- Own composed prefix clock, including SAME acquired geometry, actual decrement/cleanup and both complete actual power sources. -/
def runBound (a M u:Nat) (t width:List Bool) :Nat:=
  Acquire.runBound a M u t width+Dec.runBound (sizeWord a) t+
  10*(mass (bank (decremented a M u t width))+1)+
  Power.runBound .center (clean a M u t width) width SemiprimeD1RecoveryGridBits.twoWord a+
  Power.runBound .alpha (centered a M u t width) width SemiprimeD1RecoveryGridBits.twoWord a
attribute [local irreducible] runBound Acquire.runBound Dec.runBound Power.runBound mass
/-- Whole honest five-tape source reaches the actual first-row entry with all original geometry/height/center/alpha acquired internally. -/
theorem front_run (a M u:Nat) (t width:List Bool) :
    ∃q≤runBound a M u t width,Runs program q (.local .start)
      (input (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
      (.local .row) (bank (result a M u t width)):=by
  obtain ⟨p,hp,h0⟩:=Acquire.acquisition_run a M u t width
  have hr:=acquired_rational a M u t width
  have hRipple:∀k,(Acquire.result a M u t width).rational (SemiprimeD1StackRationalOperation.adderStack k)=[]:=by
    intro k;rw [hr];cases k <;> rfl
  have hx:bank (Acquire.result a M u t width) (copySource (.qOperand .initial))=sizeWord a:=by
    change SemiprimeD1StackPhaseGeometryArithmetic.powerWord ((List.replicate a true).length+1)=sizeWord a
    rw [List.length_replicate]
    rfl
  have h1:=Dec.decrement_run .initial (Acquire.result a M u t width) (sizeWord a) t hx rfl hRipple rfl (size_positive a)
  change Runs program (Dec.runBound (sizeWord a) t) _ _ (.local (.clearGeometry .initial 0)) (bank (decremented a M u t width)) at h1
  obtain ⟨q,hq,h2⟩:=geometry_cleanup .initial (bank (decremented a M u t width))
  rw [SemiprimeD1StackRecoveryGridGeometry.geometry_cleared] at h2
  change Runs program q _ _ (.local (.powerCount .center)) (bank (clean a M u t width)) at h2
  obtain ⟨r,hrBound,h3⟩:=Power.power_source_run .center (clean a M u t width) width SemiprimeD1RecoveryGridBits.twoWord a
    hr rfl rfl rfl rfl rfl
  change Runs program r _ _ (.local (.powerCount .alpha)) (bank (centered a M u t width)) at h3
  obtain ⟨s,hs,h4⟩:=Power.power_source_run .alpha (centered a M u t width) width SemiprimeD1RecoveryGridBits.twoWord a
    hr rfl rfl rfl rfl rfl
  change Runs program s _ _ (.local .row) (bank (result a M u t width)) at h4
  refine ⟨p+Dec.runBound (sizeWord a) t+q+r+s,?_,PTrace.join (PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3) h4⟩
  unfold runBound
  omega
/-- The actual first q is true N−1; it never uses fitted center/alpha coefficient words. -/
theorem q_value (a M u:Nat) (t width:List Bool) :
    SemiprimeBitArithmetic.bitValue ((result a M u t width).auxiliary .q)=2^(a+1)-1:=by
  change SemiprimeBitArithmetic.bitValue (Dec.difference (sizeWord a))=_
  rw [Dec.difference_value _ (size_positive a),sizeWord,SemiprimeD1StackPhaseGeometryArithmetic.powerWord_value]
/-- Every decreasing q retains the fixed acquired a+2 binary width, including q0. -/
theorem q_width (a M u:Nat) (t width:List Bool) :((result a M u t width).auxiliary .q).length=a+2:=by
  change (Dec.difference (sizeWord a)).length=_
  rw [Dec.difference,(SemiprimeBitDivision.subBits_counts _ _ false).2.2.2.2]
  rw [sizeWord,SemiprimeD1StackPhaseGeometryArithmetic.powerWord_length]
  simp only [List.length_cons,List.length_nil]
  omega
/-- Both materialized grid enumeration and index-template cells remain physically present at the true row entry. -/
theorem todo_retained (a M u:Nat) (t width:List Bool) :
    (result a M u t width).auxiliary .todo=List.replicate (2^(a+1)) true ∧
    (result a M u t width).auxiliary .indexTemplate=List.replicate (a+2) false:=⟨rfl,rfl⟩
end RiemannGaussian.SemiprimeD1StackRecoveryGridFront

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalPhaseBudget
import RiemannGaussian.SemiprimeD1PhysicalRecursiveReport

/-! # Original-data local envelope for the actual recursive frame
The envelope has no recursive solved-value or advised-cost input. Literal child
constructors remain explicit for their subsequent uniform resource substitution.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace RiemannGaussian.SemiprimeD1PhysicalFrameBudget
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1PhysicalRecursiveClock
open SemiprimeD1PhysicalRecursiveReport SemiprimeD1PhysicalPhaseBudget
open SemiprimeD1JetAffineCoefficient (JetRun)
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Actual-data local budget independent of recursive child solutions or fuel.
Repeated child constructors/source/menu/header reports remain explicit. -/
def budget (s : ℕ) (parent : Call) : ℕ :=
  let lam:=SemiprimeD1PackingReady.logarithm s
  let M:=edgeCount parent.net
  if activeTest s lam parent.depth M then
    let a:=SemiprimeD1Schedule.exponent lam parent.depth
    let u:=SemiprimeD1Schedule.levels lam parent.depth
    let P:=SemiprimeD1ModeRate.workingPrecision M u a 0 parent.ctx.precision
    (((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map (phaseBudget parent a u)).sum)+
      parent.ctx.rank*SemiprimeD1PhysicalRecoveryLocalBudget.budget a M parent.ctx.precision parent.ctx.rank P+
      (SemiprimeD1RecoveryWeightRun.geometry a 0).work+
      20*(s+lam+parent.depth+M+a+u+P+parent.ctx.rank+SemiprimeD1WireKernelOriginal.size a+1)
  else (SemiprimeD1TensorNetwork.leaf parent.ctx parent.net).clock+s+lam+parent.depth+M+8

/-- The actual erased structural successor has an original-data local envelope;
no source, child, shape, fit or callback-work supplier is a premise. -/
theorem frame_clock (s fuel : ℕ) (parent : Call) :
    (frame s parent (eraseClock (SemiprimeD1PhysicalRecursiveCounter.run s fuel (parent.depth+1)))).clock ≤
      budget s parent := by
  dsimp only [frame,budget]
  split
  · rename_i ha
    let lam:=SemiprimeD1PackingReady.logarithm s
    let a:=SemiprimeD1Schedule.exponent lam parent.depth
    let u:=SemiprimeD1Schedule.levels lam parent.depth
    let next:=eraseClock (SemiprimeD1PhysicalRecursiveCounter.run s fuel (parent.depth+1))
    have hu : u ≤ edgeCount parent.net := ((activeTest_correct _ _ _ _).mp ha).2.2
    have hp : (((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map
        (phase next parent.ctx parent.net a u)).map PhaseRun.clock).sum ≤
        ((List.finRange (SemiprimeD1WireKernelOriginal.size a)).map (phaseBudget parent a u)).sum := by
      simp only [List.map_map,Function.comp_def]
      apply List.sum_le_sum
      intro t ht
      exact phase_local_clock s fuel parent a u t
    have hr:=SemiprimeD1PhysicalRecoveryLocalBudget.recoveries_clock next parent.ctx parent.net a u hu
    dsimp only at hr
    change _+_+_+_ ≤ _+_+_+_
    simp only [List.length_map,List.length_finRange]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hp hr) _) _
  · exact le_rfl

/-- Local contribution is bounded only on the REAL remaining-fuel states.
The zero-fuel inactive-test premise is a schedule guard, not a leaf-size answer. -/
theorem localWork_bound (s fuel : ℕ) (parent : Call)
    (hz : fuel=0 → activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth (edgeCount parent.net)=false) :
    localWork s fuel parent ≤ budget s parent := by
  cases fuel with
  | zero =>
    simp only [localWork,budget,hz rfl,Bool.false_eq_true,ite_false]
    omega
  | succ fuel => exact frame_clock s fuel parent

/-- Actual successor report is bounded by its closed original-data local frame
plus the actual recursive reports in the literal child inventory. -/
theorem run_clock (s fuel : ℕ) (parent : Call) :
    (SemiprimeD1PhysicalRecursiveCounter.run s (fuel+1) parent.depth parent.ctx parent.net).clock ≤
      budget s parent+((children s parent).map (fun c =>
        (SemiprimeD1PhysicalRecursiveCounter.run s fuel c.depth c.ctx c.net).clock)).sum := by
  rw [SemiprimeD1PhysicalRecursiveReport.run_clock]
  exact Nat.add_le_add_right (frame_clock s fuel parent) _

end RiemannGaussian.SemiprimeD1PhysicalFrameBudget

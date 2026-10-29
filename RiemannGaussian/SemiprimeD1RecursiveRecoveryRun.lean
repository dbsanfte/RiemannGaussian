/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveRecovery

/-! # Actual active recursive output from the actual retained-phase postcondition
The sole conditional semantic premise concerns phases of THIS concrete run's
predecessor. Schedule inequalities, scalar recovery, canonical shape and final
word equality are derived; there is no public solver/child-value oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 140000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RecursiveRecoveryRun
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveRecovery SemiprimeD1JetInterpretation
open SemiprimeD1JetAffineCoefficient (JetRun)

/-- Dense actual old-coordinate recovery words equal the parent leaf in the current quotient. -/
theorem recovery_words_correct (next : Context→Network→JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (hpos : ctx.Positive) (hu : 0<u) (huM : u≤edgeCount net) (hua : u≤a)
    (hphase : PhaseCorrect next ctx net a u) :
    interpret ctx ((List.range ctx.rank).map (fun k =>
      (recoverCoordinate ctx a (edgeCount net) u
        (SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision)
        (retained next ctx net a u) k).bits))=
      interpret ctx (leaf ctx net).words := by
  apply (interpret_eq_iff ctx _ _ hpos).mpr
  intro k hk
  simp only [SemiprimeD1JetRingBits.coefficient,List.getElem?_map,List.getElem?_range hk,
    Option.map_some,Option.getD_some]
  exact recoverCoordinate_correct next ctx net a u hpos hu huM hua hphase k hk

/-- Actual active branch stores the exact recovered coordinate words from the
actual predecessor's once-retained original-grid phase array. -/
theorem run_active_words (s fuel depth : ℕ) (ctx : Context) (net : Network)
    (hguard : activeTest s (SemiprimeD1PackingReady.logarithm s) depth (edgeCount net)=true) :
    let lam:=SemiprimeD1PackingReady.logarithm s
    let a:=SemiprimeD1Schedule.exponent lam depth
    let u:=SemiprimeD1Schedule.levels lam depth
    (run s (fuel+1) depth ctx net).words=
      (List.range ctx.rank).map (fun k =>
        (recoverCoordinate ctx a (edgeCount net) u
          (SemiprimeD1ModeRate.workingPrecision (edgeCount net) u a 0 ctx.precision)
          (retained (run s fuel (depth+1)) ctx net a u) k).bits) := by
  dsimp only
  rw [run,ite_eq_left hguard]
  simp only [List.map_map,Function.comp_def]
  rfl

/-- Actual executed schedule tests derive every numerical inequality needed by D.5. -/
theorem active_recovery_guards (s depth : ℕ) (net : Network)
    (hguard : activeTest s (SemiprimeD1PackingReady.logarithm s) depth (edgeCount net)=true) :
    let lam:=SemiprimeD1PackingReady.logarithm s
    let a:=SemiprimeD1Schedule.exponent lam depth
    let u:=SemiprimeD1Schedule.levels lam depth
    0<u ∧ u≤edgeCount net ∧ u≤a := by
  dsimp only
  have ha:=(activeTest_correct s (SemiprimeD1PackingReady.logarithm s) depth (edgeCount net)).mp hguard
  refine ⟨?_,ha.2.2,SemiprimeD1RecursivePhaseControl.schedule_levels_le_exponent _ _⟩
  have hmin:=ha.2.1
  unfold SemiprimeD1PrecisionEnvelope.minimumLevels at hmin
  omega

/-- Conditional active-run correctness has ONE semantic premise: the ACTUAL
retained phase blocks of THIS run's predecessor satisfy PhaseCorrect.
No arbitrary child, degree, integrality, weight, shape or Fits supplier occurs. -/
theorem run_active_correct (s fuel depth : ℕ) (ctx : Context) (net : Network)
    (hpos : ctx.Positive)
    (hguard : activeTest s (SemiprimeD1PackingReady.logarithm s) depth (edgeCount net)=true)
    (hphase : PhaseCorrect (run s fuel (depth+1)) ctx net
      (SemiprimeD1Schedule.exponent (SemiprimeD1PackingReady.logarithm s) depth)
      (SemiprimeD1Schedule.levels (SemiprimeD1PackingReady.logarithm s) depth)) :
    interpret ctx (run s (fuel+1) depth ctx net).words=interpret ctx (leaf ctx net).words := by
  rw [run_active_words s fuel depth ctx net hguard]
  have hg:=active_recovery_guards s depth net hguard
  exact recovery_words_correct (run s fuel (depth+1)) ctx net _ _ hpos hg.1 hg.2.1 hg.2.2 hphase

/-- Intrinsic actual run/leaf canonicality upgrades active-run residue correctness
to literal word equality, with no canonical-output or width advice. -/
theorem run_active_words_eq_leaf (s fuel depth : ℕ) (ctx : Context) (net : Network)
    (hpos : ctx.Positive)
    (hguard : activeTest s (SemiprimeD1PackingReady.logarithm s) depth (edgeCount net)=true)
    (hphase : PhaseCorrect (run s fuel (depth+1)) ctx net
      (SemiprimeD1Schedule.exponent (SemiprimeD1PackingReady.logarithm s) depth)
      (SemiprimeD1Schedule.levels (SemiprimeD1PackingReady.logarithm s) depth)) :
    (run s (fuel+1) depth ctx net).words=(leaf ctx net).words := by
  have hr:=run_good s (fuel+1) depth ctx net
  have hl:=SemiprimeD1LeafCounterBounds.run_good (edgeCount net) ctx (vertices net)
  exact interpret_injective ctx _ _ hpos hr.1 hl.1
    (fun w hw => (hr.2 w hw).1) (fun w hw => (hl.2 w hw).1)
    (fun w hw => (hr.2 w hw).2) (fun w hw => (hl.2 w hw).2)
    (run_active_correct s fuel depth ctx net hpos hguard hphase)
end RiemannGaussian.SemiprimeD1RecursiveRecoveryRun

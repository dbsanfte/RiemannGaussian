/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursivePhaseCorrectness
import RiemannGaussian.SemiprimeD1NetworkAcquiredQueries

/-! # Correctness of the concrete finite recursive controller
The acquired original-network D.16 theorem closes the phase postcondition.
Fuel induction then proves the actual controller, including its literal leaf
fallbacks, equals the original finite network contraction. No child solver,
coefficient, entry, width or collision answer is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 160000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RecursiveCorrectness
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1JetInterpretation SemiprimeD1JetAffineCoefficient
open SemiprimeD1WireKernelOriginal SemiprimeD1HermiteNodes
open SemiprimeD1RecursivePhaseControl SemiprimeD1RecursivePhaseCorrectness
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Positive actual retained multiplicity forces positive acquired scalar precision. -/
theorem source_precision_positive (ctx : Context) (net : Network) (a u : ℕ) (i : Fin a)
    (hq : 0 < SemiprimeD1ModeRate.jetHeight (edgeCount net) u * (u-i.val)) :
    0 < (SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64
      a u i.val ctx.precision (arity net.rows) (owner net.rows)).precision := by
  rw [SemiprimeD1RecursivePhaseBounds.source_precision]
  have hh : 0 < SemiprimeD1ModeRate.jetHeight (edgeCount net) u :=
    Nat.pos_of_mul_pos_right hq
  unfold SemiprimeD1ModeRate.workingPrecision
  positivity

/-- The actual acquired original-network contraction supplies the exact phase
query at every retained point, with all valuation and precision guards derived. -/
theorem queryAt_actual (ctx : Context) (net : Network) (a u : ℕ)
    (hpos : ctx.Positive) (hw : WellFormed net) (hg : Good ctx net) (hua : u ≤ a)
    (t : Fin (size a))
    (ht : t.val ∈ active a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u) :
    QueryAt ctx net a u t (phaseIndex net a u t hua ht) := by
  let i := phaseIndex net a u t hua ht
  let source := SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64
    a u i.val ctx.precision (arity net.rows) (owner net.rows)
  let q := SemiprimeD1ModeRate.jetHeight (edgeCount net) u * (u-i.val)
  have hq : 0 < q := by
    dsimp only [q,i]
    rw [phaseIndex_multiplicity]
    exact SemiprimeD1HermiteNodes.active_positive _ _ _ _ ht
  have hp : 0 < source.precision := source_precision_positive ctx net a u i hq
  have hguard := active_guard net a u t hua ht
  have hpoint : point a t.val ≠ 0 := by
    simpa only [SemiprimeD1RecoveryWeightRun.geometry_point] using hguard.2.2
  have hi : padicValInt 2 (point a t.val) = i.val := (order_value a t).symm
  exact SemiprimeD1NetworkAcquiredQueries.network_query_contraction net hw ctx hg
    q source.precision 64 a u i (SemiprimeD1FreshJetBits.acquireFresh ctx q source.precision)
    t rfl hpos hq hp hpoint hi

/-- Actual child correctness closes every phase postcondition without any
additional block or coefficient supplier. -/
theorem phase_correct (next : Context → Network → JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (hpos : ctx.Positive) (hw : WellFormed net) (hg : Good ctx net)
    (hua : u ≤ a) (hnext : NextCorrect next) :
    SemiprimeD1RecursiveRecovery.PhaseCorrect next ctx net a u := by
  exact phaseCorrect_of_query next ctx net a u hpos hg hua hnext
    (fun t ht => queryAt_actual ctx net a u hpos hw hg hua t ht)

/-- Every actual fuel/depth execution returns the original literal network
contraction. Fuel zero and failed guards execute their actual exhaustive leaf. -/
theorem run_correct (s fuel depth : ℕ) (ctx : Context) (net : Network)
    (hpos : ctx.Positive) (hw : WellFormed net) (hg : Good ctx net) :
    interpret ctx (run s fuel depth ctx net).words = interpret ctx (leaf ctx net).words := by
  induction fuel generalizing depth ctx net with
  | zero => rw [run_zero_words]
  | succ fuel ih =>
    by_cases ha : activeTest s (SemiprimeD1PackingReady.logarithm s) depth (edgeCount net) = true
    · apply SemiprimeD1RecursiveRecoveryRun.run_active_correct s fuel depth ctx net hpos ha
      exact phase_correct (run s fuel (depth+1)) ctx net _ _ hpos hw hg
        (schedule_levels_le_exponent _ _)
        (fun c child hc hwc hgc => ih (depth+1) c child hc hwc hgc)
    · rw [run_inactive_words s fuel depth ctx net (Bool.eq_false_of_not_eq_true ha)]

/-- Canonical actual word output agrees literally with the canonical leaf,
not only after interpretation in the original quotient. -/
theorem run_words_eq_leaf (s fuel depth : ℕ) (ctx : Context) (net : Network)
    (hpos : ctx.Positive) (hw : WellFormed net) (hg : Good ctx net) :
    (run s fuel depth ctx net).words = (leaf ctx net).words := by
  have hr := run_good s fuel depth ctx net
  have hl := SemiprimeD1LeafCounterBounds.run_good (edgeCount net) ctx (vertices net)
  exact interpret_injective ctx _ _ hpos hr.1 hl.1
    (fun w hw => (hr.2 w hw).1) (fun w hw => (hl.2 w hw).1)
    (fun w hw => (hr.2 w hw).2) (fun w hw => (hl.2 w hw).2)
    (run_correct s fuel depth ctx net hpos hw hg)

end RiemannGaussian.SemiprimeD1RecursiveCorrectness

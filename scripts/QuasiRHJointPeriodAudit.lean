/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.LocalPhysical
import OAI.NumberTheory.DirichletL.Detector.PhysicalPoisson
import OAI.NumberTheory.DirichletL.Detector.RadialIdentity
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual joint numerator support and the remaining nonzero frequencies

A repeated physical prime power forces divisibility of its Gauss numerator.
If the spectral ideal also contains that prime, the actual ideal row is zero
there, so the joint row vanishes pointwise. This keeps imprimitive Gauss rows
and all their nonunit support, rather than invoking squarefree orthogonality.

For the canonical nonempty calibration, under its actual coprimality
hypothesis, the exact smooth physical cutoff is entirely the existing
nonzero-frequency Poisson sum. Empty or arbitrary trivial calibration is
not covered. Zero complete-period mean is not a short-window estimate and
does not imply zero hypothetical-zero source.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
set_option warningAsError true
noncomputable section
open scoped BigOperators Classical ContDiff

namespace OpenAIReview.JointPeriod
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.CanonicalRowCompletion
open OAI.ConcretePrimeRowBridge OAI.SevenEighths.ProbePhysical
open OAI.SevenEighths.ProbePrimePower OAI.GaussianShiftedPartition
open OAI.EisensteinSchwartzPoisson
local notation "O" => OAI.ActualEisensteinCubic.O

/-- A repeated physical prime power annihilates every spectral row
containing the same prime, pointwise at every actual numerator. -/
theorem repeated_physical_prime_overlap_zero (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (n : ℕ) (B : Ideal O) (m : O) :
    idealRowHom m ((Ideal.span {p})*B) *
      sexticGauss (p^(n+2)) (pow_ne_zero _ hp.ne_zero) (-m) = 0 := by
  by_cases hm : m ∈ (Ideal.span {p} : Ideal O)
  · have hz : Ideal.Quotient.mk (Ideal.span {p}) m = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hm
    rw [map_mul, idealRowHom_prime _ _ hg, hz,
      (actualSextic (Ideal.span {p}) hg).map_zero, zero_mul, zero_mul]
  · have hdiv : ¬p^(n+1) ∣ -m := by
      intro hd
      have hpd : p ∣ -m := (dvd_pow_self p (by omega : n+1 ≠ 0)).trans hd
      exact hm (Ideal.mem_span_singleton.mpr (dvd_neg.mp hpd))
    have hzero := primePowerGauss_zero_off_support p hp.ne_zero
      (actualSextic (Ideal.span {p}) hg ^ (n+2)) (n+1) (-m) hdiv
    have he := sexticGauss_prime_power p hp hg (n+1) (-m)
    have hz : sexticGauss (p^(n+2)) (pow_ne_zero _ hp.ne_zero) (-m) = 0 := by
      exact he.trans hzero
    rw [hz, mul_zero]

/-- All finite numerator weights and all calibration values preserve the
pointwise annihilation. This is a support identity, not a signed estimate. -/
theorem weighted_repeated_physical_overlap_zero (C : CalibrationData)
    (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (n : ℕ) (B : Ideal O)
    (F : Finset O) (w : O → ℂ) :
    (∑ m ∈ F, w m * C.residueMonoid m *
      (idealRowHom m ((Ideal.span {p})*B) *
        sexticGauss (p^(n+2)) (pow_ne_zero _ hp.ne_zero) (-m))) = 0 := by
  simp only [repeated_physical_prime_overlap_zero p hp hg n B, mul_zero, Finset.sum_const_zero]

/-- The literal complete calibrated common-period sum at zero frequency
vanishes for the canonical NONEMPTY calibration and its actual coprimality. -/
theorem calibrated_common_period_zero
    (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal) (hSne : S.Nonempty)
    (a s : O) (ha : a ≠ 0) (hs : s ≠ 0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (a*s)) :
    actualPhysicalFourier (calibrationForSet S hS) a s ha hs 0 = 0 := by
  rw [actualPhysicalFourier_eq,
    actualCongruenceCoefficient_zero_frequency S hS hSne a s ha hs hcop, mul_zero]

/-- The actual smooth cutoff covariance equals its nonzero-frequency
Poisson terms exactly; no common-period zero has been converted into decay. -/
theorem physical_cutoff_eq_nonzero_frequencies
    (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal) (hSne : S.Nonempty)
    (a s : O) (ha : a ≠ 0) (hs : s ≠ 0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (a*s))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K : ℝ) (hK : 0<K) :
    let C := calibrationForSet S hS
    (∑' m : O, calibratedNumerator C a m * sexticGauss s hs (-m) *
      W (elementNorm m/K)) =
      ((K/elementNorm (C.generator*a) : ℝ) : ℂ) *
        ∑' H : OAI.SevenEighths.ProbePhysical.NonzeroFrequency,
          actualCongruenceCoefficient C a s ha H.val *
            paperRadialFourier W
              (K*elementNorm H.val/elementNorm ((C.generator*a)*s)) := by
  dsimp only
  rw [physical_row_poisson (calibrationForSet S hS) a s ha hs W hWc hWs K hK]
  congr 1
  symm
  apply (Subtype.val_injective : Function.Injective
    (fun H : OAI.SevenEighths.ProbePhysical.NonzeroFrequency => H.val)).tsum_eq
    (f := fun H : O => actualCongruenceCoefficient (calibrationForSet S hS) a s ha H *
      paperRadialFourier W
        (K*elementNorm H/elementNorm (((calibrationForSet S hS).generator*a)*s)))
  intro H hH
  have hn : H ≠ 0 := by
    intro hz
    subst H
    exact hH (by dsimp only; rw [actualCongruenceCoefficient_zero_frequency S hS hSne a s ha hs hcop,
      zero_mul])
  exact ⟨⟨H,hn⟩,rfl⟩

end OpenAIReview.JointPeriod

#lint+ in OpenAIReview.JointPeriod

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty actual joint-period audit."
  logInfo m!"Actual joint-period audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-joint-covariance"
  IO.FS.writeFile ".lake/arithmetic-operator-joint-covariance/axioms.json"
    (Json.mkObj [("scope",toJson "actual repeated-physical-prime pointwise annihilation and calibrated nonzero-frequency cutoff identity; no annular saving or zero-source bound"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty

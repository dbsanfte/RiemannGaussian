/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovUniformExponent

/-!
# The critical high-moment exponent with every positive epsilon

A nonempty bounded set of permissible exponents has infimum equal to the
critical exponent: the proved uniform improvement rules out a positive
gap. Consequently, for every k>=2,u>=k and epsilon>0, the actual original
J_((u+1)k,k)(X) is at most C*X^(2k(u+1)-k(k+1)/2+epsilon) for all X>=X0.
No homogeneous moment budget remains as a premise in this terminal theorem.

This covers the displayed high-order range and every positive epsilon;
it does not assert epsilon=0 or the corresponding result for all smaller
moment orders. Constants and thresholds, including their dependence on
k,u,epsilon, are unevaluated. Quantitative joint resonance control, the
zeta growth estimate and a new VK zero-free region still need proof.
-/

namespace RiemannGaussian.VinogradovCriticalExponent
noncomputable section
open VinogradovMeanValue VinogradovUniformExponent

/-- Uniform improvement above a lower endpoint forces admissible exponents arbitrarily close to that endpoint. -/
theorem exists_admissible_near_endpoint {critical : ℝ} {A : ℝ → Prop}
    (hne : ∃ lam : ℝ, critical ≤ lam ∧ A lam)
    (himprove : ∀ defect : ℝ, 0 < defect → ∃ eps : ℝ, 0 < eps ∧ eps ≤ defect / 2 ∧
      ∀ lam : ℝ, defect ≤ lam - critical → A lam → A (lam - eps))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ lam : ℝ, critical ≤ lam ∧ A lam ∧ lam < critical + eta := by
  let S : Set ℝ := {lam | critical ≤ lam ∧ A lam}
  have hS : S.Nonempty := hne
  have hbelow : BddBelow S := ⟨critical, fun lam h => h.1⟩
  have hcrit : critical ≤ sInf S := le_csInf hS (fun lam h => h.1)
  have hinf : sInf S = critical := by
    apply le_antisymm _ hcrit
    by_contra! hgap
    let defect := (sInf S - critical) / 2
    have hdefect : 0 < defect := by unfold defect; linarith
    obtain ⟨eps, heps, hepsbound, hstep⟩ := himprove defect hdefect
    obtain ⟨lam, hlamS, hlam⟩ := exists_lt_of_csInf_lt hS (show sInf S < sInf S + eps / 2 by linarith)
    have hinflam : sInf S ≤ lam := csInf_le hbelow hlamS
    have hdeflam : defect ≤ lam - critical := by unfold defect; linarith
    have hnext := hstep lam hdeflam hlamS.2
    have hnextS : lam - eps ∈ S := by
      refine ⟨?_, hnext⟩
      dsimp only [defect] at hepsbound
      linarith
    have hcontra := csInf_le hbelow hnextS
    linarith
  obtain ⟨lam, hlamS, hlam⟩ := exists_lt_of_csInf_lt hS (show sInf S < critical + eta by rw [hinf]; linarith)
  exact ⟨lam, hlamS.1, hlamS.2, hlam⟩

/-- The original Vinogradov mean value has the critical exponent with every positive epsilon, for each degree at least two and u at least that degree. -/
theorem exists_global_critical_exponent (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      meanValue ((u + 1) * k) k X ≤ C * (X : ℝ) ^
        (2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps) := by
  let critical := 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2
  let A : ℝ → Prop := fun lam => ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    meanValue ((u + 1) * k) k X ≤ C * (X : ℝ) ^ lam
  have hne : ∃ lam : ℝ, critical ≤ lam ∧ A lam :=
    ⟨_, (VinogradovNegativeProfile.first_exponent_gt_critical hk).le,
      VinogradovFirstExponent.exists_global_first_exponent k u hk hu⟩
  have himprove : ∀ defect : ℝ, 0 < defect → ∃ eps : ℝ, 0 < eps ∧ eps ≤ defect / 2 ∧
      ∀ lam : ℝ, defect ≤ lam - critical → A lam → A (lam - eps) := by
    intro defect hdefect
    obtain ⟨epsilon, hepsilon, hebound, hstep⟩ := exists_uniform_exponent_improvement k u hk hu defect hdefect
    refine ⟨epsilon, hepsilon, hebound, ?_⟩
    intro lam hlam hA
    apply hstep lam _ hA
    dsimp only [critical] at hlam
    linarith
  obtain ⟨lam, hlamlow, hlamA, hlam⟩ := exists_admissible_near_endpoint hne himprove heps
  obtain ⟨C, hC, X₀, hJ⟩ := hlamA
  refine ⟨C, hC, max X₀ 1, ?_⟩
  intro X hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (le_max_right X₀ 1).trans hX
  exact (hJ X ((le_max_left _ _).trans hX)).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX1 hlam.le) hC.le)

end
end RiemannGaussian.VinogradovCriticalExponent

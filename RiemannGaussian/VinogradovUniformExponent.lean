/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovUniformSaving
import RiemannGaussian.VinogradovExponentBootstrap

/-!
# A global exponent improvement uniform above a fixed defect

For every fixed positive lower defect, one positive epsilon improves every
proved source exponent above that defect. Epsilon is chosen before the
actual source exponent, homogeneous constant and quotient threshold.
Power cutoffs pay every original prime-packet and rounded-quotient condition;
collision-preserving monotonicity reaches all sufficiently large endpoints.
The proof supplies eventual constants and thresholds, not numerical values.
-/

namespace RiemannGaussian.VinogradovUniformExponent
noncomputable section
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovConditioningPowerSaving
open VinogradovFirstExponent VinogradovExponentBootstrap VinogradovUniformSaving

/-- A fixed positive distance above critical gives one positive global exponent improvement uniformly over every admissible source exponent. -/
theorem exists_uniform_exponent_improvement (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (defect : ℝ) (hdefect0 : 0 < defect) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ defect / 2 ∧ ∀ lam : ℝ,
      defect ≤ lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 →
      (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ X : ℕ, N₀ ≤ X →
        meanValue ((u + 1) * k) k X ≤ C * (X : ℝ) ^ lam) →
      ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        meanValue ((u + 1) * k) k X ≤ C * (X : ℝ) ^ (lam - eps) := by
  obtain ⟨beta, hbetalow, hbetadefect, hbeta, S, hS, hglobal⟩ :=
    exists_uniform_global_profile_saving k u hk hu defect hdefect0
  let Q := S + 1
  have hQ : 1 ≤ Q := by unfold Q; omega
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  let eps := -beta / (Q : ℝ)
  have heps : 0 < eps := div_pos (neg_pos.mpr hbeta) hQ0
  have hepsdefect : eps ≤ defect / 2 := (div_le_iff₀ hQ0).mpr (by nlinarith)
  refine ⟨eps, heps, hepsdefect, ?_⟩
  intro lam hdefect hJ
  have hlam1 : 1 < lam := by
    have hc := critical_exponent_gt_one hk hu
    linarith
  obtain ⟨C₀, hC₀, N₀, hJ⟩ := hJ
  let C := max 1 (C₀ * (2 : ℝ) ^ lam)
  have hC : 1 ≤ C := le_max_left _ _
  have hbudget : ∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
      meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam := by
    intro p e X hp hX hN
    have he := VinogradovImprovedNormalization.rounded_actual_meanValue hC₀.le
      (by linarith : 0 ≤ lam) hp hX hN hJ
    exact he.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  obtain ⟨B, hB, hglobal⟩ := hglobal C hC
  let mu := lam + beta / (Q : ℝ)
  have hmu0 : 0 < mu := by
    have hdiv : -(1 / 2 : ℝ) ≤ beta / (Q : ℝ) := (le_div_iff₀ hQ0).mpr (by nlinarith)
    unfold mu
    linarith
  have hmu_eq : lam - eps = mu := by dsimp only [mu, eps]; ring
  let R := 2 * (Q * (k * (k - 1))) + 1
  have hR : 2 * (Q * (k * (k - 1))) < R := by unfold R; omega
  have hRpos : 0 < R := by unfold R; omega
  obtain ⟨D, hD⟩ := exists_nat_ge (max (2 : ℝ) (max ((2 ^ R : ℕ) : ℝ)
    (max ((4 * k ^ 4 : ℕ) : ℝ) (max (N₀ : ℝ) ((C * iterationConstant k u) ^ 2)))))
  have hD2 : 2 ≤ D := by exact_mod_cast (le_max_left _ _).trans hD
  have hDi := (le_max_right _ _).trans hD
  have hpacket : 2 ^ R ≤ D := by exact_mod_cast (le_max_left _ _).trans hDi
  have hDj := (le_max_right _ _).trans hDi
  have hsize : 4 * k ^ 4 ≤ D := by exact_mod_cast (le_max_left _ _).trans hDj
  have hDl := (le_max_right _ _).trans hDj
  have hN : N₀ ≤ D := by exact_mod_cast (le_max_left _ _).trans hDl
  have hprime : (C * iterationConstant k u) ^ 2 ≤ (D : ℝ) := (le_max_right _ _).trans hDl
  let C₁ : ℝ := (2 * (R : ℝ)) ^ 2 * B * ((2 ^ R : ℕ) : ℝ) ^ (-beta)
  have hC₁ : 0 < C₁ := by
    have hRR : (0 : ℝ) < R := by exact_mod_cast hRpos
    unfold C₁
    positivity
  have hcut (M : ℕ) (hDM : D < M) :
      meanValue ((u + 1) * k) k ((2 ^ R * M) ^ Q) ≤
        C₁ * (((2 ^ R * M) ^ Q : ℕ) : ℝ) ^ mu := by
    have hM : 1 < M := by omega
    have hpacketX := VinogradovInitialIteration.packet_budget_at_power_cutoff M R k S
      hM (hpacket.trans hDM.le) (by simpa only [Q, Nat.add_comm 1 S] using hR)
    have hsizeX : 4 * k ^ 4 ≤ (2 ^ R * M) ^ Q := by
      have he : M ≤ 2 ^ R * M := Nat.le_mul_of_pos_left _ (by positivity)
      exact hsize.trans (hDM.le.trans (he.trans (Nat.le_pow (by omega))))
    obtain ⟨hXdepth, hquot⟩ := power_cutoff_quotient (2 ^ R) M S (by positivity) (by omega)
    have he := hglobal lam N₀ hdefect hbudget M R ((2 ^ R * M) ^ Q) (by omega) hRpos
      (by simpa only [Q, Nat.add_comm 1 S] using hpacketX) hsizeX hXdepth
      (hN.trans (hDM.le.trans hquot)) (hprime.trans (by exact_mod_cast hDM.le))
    have hid := power_cutoff_scale_identity Q (by omega) (A := ((2 ^ R : ℕ) : ℝ))
      (M := (M : ℝ)) (by positivity) (by exact_mod_cast (by omega : 0 < M)) lam beta
    simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hid he ⊢
    apply he.trans_eq
    calc
      _ = ((2 * (R : ℝ)) ^ 2 * B) *
          ((((2 : ℝ) ^ R * M) ^ Q) ^ lam * (M : ℝ) ^ beta) := by ring
      _ = _ := by rw [hid]; dsimp only [C₁, mu]; push_cast; ring
  rw [hmu_eq]
  refine ⟨C₁ * ((2 ^ Q : ℕ) : ℝ) ^ mu, by positivity,
    (2 ^ R * D) ^ Q + 1, ?_⟩
  intro X hX
  obtain ⟨M, hDM, hXY, hYX⟩ := exists_nearby_power_cutoff (2 ^ R) Q D X
    (by positivity) (by omega) (by omega) (by omega)
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((2 ^ R * M) ^ Q : ℕ))
    (by exact_mod_cast hYX : (((2 ^ R * M) ^ Q : ℕ) : ℝ) ≤ ((2 ^ Q * X : ℕ) : ℝ)) hmu0.le
  apply (meanValue_mono ((u + 1) * k) k hXY).trans ((hcut M hDM).trans _)
  calc
    _ ≤ C₁ * ((2 ^ Q * X : ℕ) : ℝ) ^ mu := mul_le_mul_of_nonneg_left hpow hC₁.le
    _ = _ := by rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]; ring

end
end RiemannGaussian.VinogradovUniformExponent

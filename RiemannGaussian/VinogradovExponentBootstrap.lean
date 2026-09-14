/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovProfileSaving

/-!
# A general improvement of every admissible global moment exponent

A proved eventual homogeneous exponent strictly above critical gives a
negative conditioned profile and a global prime-power saving. Genuine
power cutoffs pay every separating-packet, prime and quotient threshold.
An exact power identity and frequency-preserving monotonicity extend the
saving to every sufficiently large original endpoint. The improved exponent
can be chosen strictly above critical, keeping the recurrence applicable.

In particular, the original global mean value has an unconditional exponent
strictly smaller than k(2u+1)-1/(3k). Constants, improvements and terminal
thresholds are existential and not numerically evaluated. Pointwise strict
improvement alone does not establish convergence to the critical exponent:
a uniform improvement near the infimum still needs proof. No new VK or RH
zero-free region is asserted.
-/

namespace RiemannGaussian.VinogradovExponentBootstrap
noncomputable section
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovConditioningPowerSaving
open VinogradovFirstExponent VinogradovProfileSaving

/-- Convert any signed prime-power factor exactly at a genuine growing power cutoff. -/
theorem power_cutoff_scale_identity (Q : ℕ) (hQ : 0 < Q) {A M : ℝ}
    (hA : 0 < A) (hM : 0 < M) (lam beta : ℝ) :
    ((A * M) ^ Q) ^ lam * M ^ beta =
      A ^ (-beta) * ((A * M) ^ Q) ^ (lam + beta / (Q : ℝ)) := by
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hX : 0 < (A * M) ^ Q := pow_pos (mul_pos hA hM) _
  simp only [Real.rpow_def_of_pos hX, Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hM,
    ← Real.exp_add, Real.log_pow, Real.log_mul hA.ne' hM.ne']
  congr 1
  field_simp
  ring

/-- One extra power pays the actual deepest padded quotient uniformly on the chosen cutoffs. -/
theorem power_cutoff_quotient (A M S : ℕ) (hA : 0 < A) (hM : 0 < M) :
    (A * M) ^ S ≤ (A * M) ^ (S + 1) ∧ M ≤ (A * M) ^ (S + 1) / (A * M) ^ S + 1 := by
  have hbase : 0 < A * M := Nat.mul_pos hA hM
  have hquot : (A * M) ^ (S + 1) / (A * M) ^ S = A * M := by
    rw [pow_succ, Nat.mul_div_cancel_left _ (Nat.pow_pos hbase)]
  refine ⟨Nat.pow_le_pow_right (by omega) (by omega), ?_⟩
  rw [hquot]
  have he : M ≤ A * M := Nat.le_mul_of_pos_left _ hA
  omega

/-- The critical exponent is already greater than one throughout the actual degree and moment-order range. -/
theorem critical_exponent_gt_one {k u : ℕ} (hk : 2 ≤ k) (hu : k ≤ u) :
    1 < 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have huR : (k : ℝ) ≤ u := by exact_mod_cast hu
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by positivity) (show 0 ≤ (u : ℝ) - k by linarith)]

/-- Every proved eventual homogeneous exponent strictly above critical admits a strictly smaller proved eventual exponent for the original global mean value. -/
theorem exists_smaller_global_exponent (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    {lam : ℝ}
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 < lam)
    (hJ : ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ X : ℕ, N₀ ≤ X →
      meanValue ((u + 1) * k) k X ≤ C * (X : ℝ) ^ lam) :
    ∃ mu : ℝ, 0 < mu ∧ mu < lam ∧ ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ,
      ∀ X : ℕ, X₀ ≤ X → meanValue ((u + 1) * k) k X ≤ C * (X : ℝ) ^ mu := by
  have hlam1 : 1 < lam := (critical_exponent_gt_one hk hu).trans hlam
  obtain ⟨C₀, hC₀, N₀, hJ⟩ := hJ
  let C := max 1 (C₀ * (2 : ℝ) ^ lam)
  have hC : 1 ≤ C := le_max_left _ _
  have hbudget : ∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
      meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam := by
    intro p e X hp hX hN
    have he := VinogradovImprovedNormalization.rounded_actual_meanValue hC₀.le
      (by linarith : 0 ≤ lam) hp hX hN hJ
    exact he.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  obtain ⟨beta, hbetalow, hbeta, S, hS, B, hB, hglobal⟩ :=
    exists_global_profile_saving hk hu hC hlam hbudget
  let Q := S + 1
  have hQ : 1 ≤ Q := by unfold Q; omega
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  let mu := lam + beta / (Q : ℝ)
  have hmu0 : 0 < mu := by
    have hdiv : -(1 / 2 : ℝ) ≤ beta / (Q : ℝ) := (le_div_iff₀ hQ0).mpr (by nlinarith)
    unfold mu
    linarith
  have hmulam : mu < lam := by
    have hdiv : beta / (Q : ℝ) < 0 := div_neg_of_neg_of_pos hbeta hQ0
    unfold mu
    linarith
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
    have he := hglobal M R ((2 ^ R * M) ^ Q) (by omega) hRpos
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
  refine ⟨mu, hmu0, hmulam, C₁ * ((2 ^ Q : ℕ) : ℝ) ^ mu, by positivity,
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

/-- The improved exponent can remain strictly inside the critical range, so the same normalized recurrence stays applicable. -/
theorem exists_smaller_admissible_exponent (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    {lam : ℝ}
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 < lam)
    (hJ : ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ X : ℕ, N₀ ≤ X →
      meanValue ((u + 1) * k) k X ≤ C * (X : ℝ) ^ lam) :
    ∃ mu : ℝ,
      2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 < mu ∧ mu < lam ∧
      ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        meanValue ((u + 1) * k) k X ≤ C * (X : ℝ) ^ mu := by
  obtain ⟨mu, hmu0, hmulam, C, hC, N₀, hbound⟩ := exists_smaller_global_exponent k u hk hu hlam hJ
  let critical := 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2
  let mu' := max mu ((critical + lam) / 2)
  have hlow : critical < mu' := lt_of_lt_of_le (by dsimp only [critical]; linarith) (le_max_right _ _)
  have hhigh : mu' < lam := max_lt hmulam (by dsimp only [critical]; linarith)
  refine ⟨mu', hlow, hhigh, C, hC, max N₀ 1, ?_⟩
  intro X hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (le_max_right N₀ 1).trans hX
  exact (hbound X ((le_max_left _ _).trans hX)).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX1 (le_max_left _ _)) hC.le)

/-- The original global moment has an unconditional admissible exponent strictly smaller than the repository's first proved improvement. -/
theorem exists_beyond_first_exponent (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) :
    ∃ mu : ℝ,
      2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 < mu ∧
      mu < (((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ))) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        meanValue ((u + 1) * k) k X ≤ C * (X : ℝ) ^ mu :=
  exists_smaller_admissible_exponent k u hk hu (VinogradovNegativeProfile.first_exponent_gt_critical hk)
    (exists_global_first_exponent k u hk hu)

end
end RiemannGaussian.VinogradovExponentBootstrap

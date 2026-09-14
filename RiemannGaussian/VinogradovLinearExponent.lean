/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovLinearSaving

/-!
# One all-endpoint exponent improvement with a linear constant cost

For each fixed positive critical defect, one exponent decrement and one
constant multiplier work for every supplied global moment bound up to the
elementary exponent. All positive integer endpoints are covered, including
the small endpoints, with no source-dependent threshold. The multiplier
and decrement are chosen before the source exponent and source constant.
-/

namespace RiemannGaussian.VinogradovLinearExponent
noncomputable section
open scoped BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovRemainderScaling
open VinogradovConditioningPowerSaving VinogradovSingularConditioning
open VinogradovNormalizedIteration VinogradovCongruencingScaling
open VinogradovNonsingularConditioning VinogradovProfileIteration
open VinogradovFirstExponent VinogradovExponentBootstrap
open VinogradovDefectRemainder
open VinogradovConstantPreservation
open VinogradovLinearProfile
open VinogradovLinearSaving

/-- The global exponent improves with one multiplier and one starting threshold
chosen before the original source constant or source exponent. -/
theorem exists_linear_eventual_improvement (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (defect : ℝ) (hdefect0 : 0 < defect) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ defect / 2 ∧ ∃ A : ℝ, 1 ≤ A ∧ ∃ X₀ : ℕ,
      ∀ lam : ℝ,
      defect ≤ lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 →
      lam ≤ ((k * (2 * u + 1) : ℕ) : ℝ) → ∀ C : ℝ, 1 ≤ C →
      (∀ X : ℕ, 1 ≤ X → meanValue ((u + 1) * k) k X ≤ C * (X : ℝ) ^ lam) →
      ∀ X : ℕ, X₀ ≤ X → meanValue ((u + 1) * k) k X ≤
        (A * C) * (X : ℝ) ^ (lam - eps) := by
  obtain ⟨beta, hbetalow, hbetadefect, hbeta, S, hS, B, hB, hglobal⟩ :=
    exists_linear_global_profile_saving k u hk hu defect hdefect0
  let Q := S + 1
  have hQ : 1 ≤ Q := by unfold Q; omega
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  let eps := -beta / (Q : ℝ)
  have heps : 0 < eps := div_pos (neg_pos.mpr hbeta) hQ0
  have hepsdefect : eps ≤ defect / 2 := (div_le_iff₀ hQ0).mpr (by nlinarith)
  let L : ℝ := ((k * (2 * u + 1) : ℕ) : ℝ)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  let F := (2 : ℝ) ^ L
  have hF : 1 ≤ F := Real.one_le_rpow (by norm_num) hL
  let R := 2 * (Q * (k * (k - 1))) + 1
  have hR : 2 * (Q * (k * (k - 1))) < R := by unfold R; omega
  have hRpos : 0 < R := by unfold R; omega
  obtain ⟨D, hD⟩ := exists_nat_ge (max (2 : ℝ) (max ((2 ^ R : ℕ) : ℝ)
    (max ((4 * k ^ 4 : ℕ) : ℝ) (iterationConstant k u ^ 2))))
  have hD2 : 2 ≤ D := by exact_mod_cast (le_max_left _ _).trans hD
  have hDi := (le_max_right _ _).trans hD
  have hpacket : 2 ^ R ≤ D := by exact_mod_cast (le_max_left _ _).trans hDi
  have hDj := (le_max_right _ _).trans hDi
  have hsize : 4 * k ^ 4 ≤ D := by exact_mod_cast (le_max_left _ _).trans hDj
  have hprime : iterationConstant k u ^ 2 ≤ (D : ℝ) := (le_max_right _ _).trans hDj
  let A₀ : ℝ := (2 * (R : ℝ)) ^ 2 * B * F * ((2 ^ R : ℕ) : ℝ) ^ (-beta)
  have hA₀ : 0 < A₀ := by
    have hRR : (0 : ℝ) < R := by exact_mod_cast hRpos
    dsimp only [A₀, F]
    positivity
  let A := max 1 (A₀ * ((2 ^ Q : ℕ) : ℝ) ^ L)
  refine ⟨eps, heps, hepsdefect, A, le_max_left _ _, (2 ^ R * D) ^ Q + 1, ?_⟩
  intro lam hdefect hlamhi C hC hJ
  have hlam1 : 1 < lam := by
    have hc := critical_exponent_gt_one hk hu
    linarith
  let C' := C * F
  have hC' : 1 ≤ C' := by dsimp only [C']; nlinarith only [hC, hF]
  have hbudget : ∀ p e X : ℕ, 0 < p → p ^ e ≤ X → 1 ≤ X / p ^ e + 1 →
      meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C' * ((X : ℝ) / (p : ℝ) ^ e) ^ lam := by
    intro p e X hp hX hN
    have he := VinogradovImprovedNormalization.rounded_actual_meanValue
      (zero_le_one.trans hC) (by linarith : 0 ≤ lam) hp hX hN hJ
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hlamhi) (zero_le_one.trans hC)
  let mu := lam + beta / (Q : ℝ)
  have hmu0 : 0 < mu := by
    have hdiv : -(1 / 2 : ℝ) ≤ beta / (Q : ℝ) := (le_div_iff₀ hQ0).mpr (by nlinarith)
    dsimp only [mu]
    linarith
  have hmuhi : mu ≤ L := by
    have hdiv : beta / (Q : ℝ) ≤ 0 := (div_neg_of_neg_of_pos hbeta hQ0).le
    dsimp only [mu, L]
    linarith only [hlamhi, hdiv]
  have hmu_eq : lam - eps = mu := by dsimp only [mu, eps]; ring
  have hcut (M : ℕ) (hDM : D < M) :
      meanValue ((u + 1) * k) k ((2 ^ R * M) ^ Q) ≤
        (A₀ * C) * (((2 ^ R * M) ^ Q : ℕ) : ℝ) ^ mu := by
    have hM : 1 < M := by omega
    have hpacketX := VinogradovInitialIteration.packet_budget_at_power_cutoff M R k S
      hM (hpacket.trans hDM.le) (by simpa only [Q, Nat.add_comm 1 S] using hR)
    have hsizeX : 4 * k ^ 4 ≤ (2 ^ R * M) ^ Q := by
      have he : M ≤ 2 ^ R * M := Nat.le_mul_of_pos_left _ (by positivity)
      exact hsize.trans (hDM.le.trans (he.trans (Nat.le_pow (by omega))))
    obtain ⟨hXdepth, _⟩ := power_cutoff_quotient (2 ^ R) M S (by positivity) (by omega)
    have he := hglobal C' hC' lam 1 hdefect hbudget M R ((2 ^ R * M) ^ Q) (by omega) hRpos
      (by simpa only [Q, Nat.add_comm 1 S] using hpacketX) hsizeX hXdepth
      (by exact Nat.succ_le_succ (Nat.zero_le _)) (hprime.trans (by exact_mod_cast hDM.le))
    have hid := power_cutoff_scale_identity Q (by omega) (A := ((2 ^ R : ℕ) : ℝ))
      (M := (M : ℝ)) (by positivity) (by exact_mod_cast (by omega : 0 < M)) lam beta
    simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hid he ⊢
    apply he.trans_eq
    calc
      _ = ((2 * (R : ℝ)) ^ 2 * (C' * B)) *
          ((((2 : ℝ) ^ R * M) ^ Q) ^ lam * (M : ℝ) ^ beta) := by ring
      _ = _ := by rw [hid]; dsimp only [A₀, mu, C']; push_cast; ring
  rw [hmu_eq]
  intro X hX
  obtain ⟨M, hDM, hXY, hYX⟩ := exists_nearby_power_cutoff (2 ^ R) Q D X
    (by positivity) (by omega) (by omega) (by omega)
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((2 ^ R * M) ^ Q : ℕ))
    (by exact_mod_cast hYX : (((2 ^ R * M) ^ Q : ℕ) : ℝ) ≤ ((2 ^ Q * X : ℕ) : ℝ)) hmu0.le
  apply (meanValue_mono ((u + 1) * k) k hXY).trans ((hcut M hDM).trans _)
  calc
    _ ≤ (A₀ * C) * ((2 ^ Q * X : ℕ) : ℝ) ^ mu := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (A₀ * ((2 ^ Q : ℕ) : ℝ) ^ mu) * C * (X : ℝ) ^ mu := by
      rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hC)
      apply le_trans _ (le_max_right _ _)
      apply mul_le_mul_of_nonneg_left _ hA₀.le
      exact Real.rpow_le_rpow_of_exponent_le (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := Q))) hmuhi

/-- A single linear constant multiplier improves the original global moment
at every positive integer endpoint, with no source-dependent starting cutoff. -/
theorem exists_linear_all_endpoint_improvement (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (defect : ℝ) (hdefect0 : 0 < defect) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ defect / 2 ∧ ∃ A : ℝ, 1 ≤ A ∧
      ∀ lam : ℝ,
      defect ≤ lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 →
      lam ≤ ((k * (2 * u + 1) : ℕ) : ℝ) → ∀ C : ℝ, 1 ≤ C →
      (∀ X : ℕ, 1 ≤ X → meanValue ((u + 1) * k) k X ≤ C * (X : ℝ) ^ lam) →
      ∀ X : ℕ, 1 ≤ X → meanValue ((u + 1) * k) k X ≤
        (A * C) * (X : ℝ) ^ (lam - eps) := by
  obtain ⟨eps, heps, hsmall, A, hA, X₀, h⟩ :=
    exists_linear_eventual_improvement k u hk hu defect hdefect0
  let B := max A (((max X₀ 1 : ℕ) : ℝ) ^ eps)
  refine ⟨eps, heps, hsmall, B, hA.trans (le_max_left _ _), ?_⟩
  intro lam hdefect hlamhi C hC hJ X hX
  by_cases hlarge : X₀ ≤ X
  · exact (h lam hdefect hlamhi C hC hJ X hlarge).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (zero_le_one.trans hC)) (by positivity))
  · have hXp : (0 : ℝ) < X := by exact_mod_cast hX
    have hpow : (X : ℝ) ^ eps ≤ B :=
      (Real.rpow_le_rpow hXp.le (by exact_mod_cast (show X ≤ max X₀ 1 by omega)) heps.le).trans
        (le_max_right _ _)
    apply (hJ X hX).trans
    calc
      _ = (C * (X : ℝ) ^ (lam - eps)) * (X : ℝ) ^ eps := by
        rw [mul_assoc, ← Real.rpow_add hXp]
        congr 2
        ring
      _ ≤ (C * (X : ℝ) ^ (lam - eps)) * B := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring

end
end RiemannGaussian.VinogradovLinearExponent

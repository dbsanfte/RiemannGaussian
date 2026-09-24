/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszZeroParityOrders

/-!
# Finite-prime phases down to N/200

The lower prime cutoff costs only a polynomial times u^k, uniformly in
height. The independent upper-completion exponent is unchanged when the
lower derivative endpoint is reduced. All moments remain on the original
physical prime set; no masked packet is completed here.
-/

namespace RiemannGaussian.ZetaRieszParityOrderPhase
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszWideOwnerAudit ZetaRieszPrimeCompletion ZetaRieszPrimeCompletionRate
open ZetaRieszCompletionProduct ZetaRieszPrimePairConvolution ZetaRieszAnnulusJoint
open ZetaExposedPrimeMoments ZetaRieszMatchedMiddle ZetaRieszWingReserve

/-- Independent completion including the N/200 small derivative leg. -/
theorem eventually_parity_weighted_error {u : ℝ} (hu : 1 / 2 ≤ u) (huU : u ≤ radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 200 * k → 40 * k ≤ 27 * N → ∀ y : ℝ,
      ‖(k : ℂ) * ((u : ℂ) ^ k * (finiteMoment (intermediatePrimes u N) k
        (3 / 2 + Complex.I * y) - ordinaryPrimeMoment k (3 / 2 + Complex.I * y)))‖ ≤
        (N + 1 : ℝ) ^ 3 * Real.exp (-(N : ℝ) / 25000) *
          ((∑' n, zetaPrimeExpWeight (1025 / 1024) n) +
            ∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n) := by
  have hu0 : 0 < u := by linarith
  have hue := huU.trans_lt radius_lt_source
  have hu1 : u < 1 := hue.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hlu : Real.log u ≤ -(11 / 16 : ℝ) := by
    simpa only [Real.log_exp] using (Real.log_lt_log hu0 hue).le
  filter_upwards [eventually_norm_physicalPrimeTail_of_rate hu0
    (show (0 : ℝ) ≤ 11 / 8 by norm_num) (by norm_num; exact hue)
    (show (0 : ℝ) < 27 / 55 by norm_num) (show (27 / 55 : ℝ) ≤ u by linarith)
    (show (1 : ℝ) < 1 + 1 / 262144 by norm_num) (by norm_num) (completion_rate hu huU),
    ZetaRieszSemiprimeSupport.eventually_quadratic_head_lt_physical hu0 hu1] with N hhi hNX
  intro k hklo hkhi y
  have hkc : (k : ℝ) ≤ N + 1 := by
    have h : k ≤ N := by omega
    have hc : (k : ℝ) ≤ N := by exact_mod_cast h
    linarith
  have hpow : u ^ k ≤ Real.exp (-(N : ℝ) / 25000) := by
    rw [← Real.exp_log hu0, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hlu (Nat.cast_nonneg (α := ℝ) k)
    have hc : (N : ℝ) ≤ 200 * k := by exact_mod_cast hklo
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hlow : ‖(u : ℂ) ^ k * smallPrimeMoment N k y‖ ≤
      (N + 1 : ℝ) ^ 2 * Real.exp (-(N : ℝ) / 25000) *
        ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    exact (mul_le_mul hpow (norm_smallPrimeMoment_le N k y) (norm_nonneg _)
      (Real.exp_pos _).le).trans_eq (by ring)
  have hhigh := hhi k (by
    have hc : 40 * (k : ℝ) ≤ 27 * N := by exact_mod_cast hkhi
    linarith) y
  rw [show -(1 / 25000 : ℝ) * N = -(N : ℝ) / 25000 by ring] at hhigh
  have hZ0 : 0 ≤ ∑' n, zetaPrimeExpWeight (1025 / 1024) n :=
    tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have hZ1 : 0 ≤ ∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n :=
    tsum_nonneg (fun _ => (Real.exp_pos _).le)
  rw [ordinaryPrimeMoment_eq_actual_split u N k y hNX]
  have he (a b c : ℂ) : a - (b + a + c) = -(b + c) := by ring
  rw [he, mul_neg, mul_neg, norm_neg, norm_mul, Complex.norm_natCast, mul_add]
  calc
    _ ≤ (k : ℝ) * (‖(u : ℂ) ^ k * smallPrimeMoment N k y‖ +
        ‖(u : ℂ) ^ k * physicalPrimeTail u N k y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (Nat.cast_nonneg _)
    _ ≤ (N + 1 : ℝ) * ((N + 1 : ℝ) ^ 2 * Real.exp (-(N : ℝ) / 25000) *
        (∑' n, zetaPrimeExpWeight (1025 / 1024) n) +
        Real.exp (-(N : ℝ) / 25000) * ∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n) := by
      exact mul_le_mul hkc (add_le_add hlow hhigh)
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ ≤ _ := by
      have h1 : 1 ≤ (N + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
      nlinarith [mul_le_mul_of_nonneg_left h1
        (show 0 ≤ (N + 1 : ℝ) * Real.exp (-(N : ℝ) / 25000) *
          (∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n) by positivity)]

/-- Every moving order in the checked wider range retains the exact
hypothetical-zero phase. -/
theorem tendsto_parity_weighted_finite (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling) (k : ℕ → ℕ)
    (hk : ∀ᶠ N : ℕ in atTop, N ≤ 200 * k N ∧ 40 * k N ≤ 27 * N) :
    Tendsto (fun N => weightedFinite (3 / 2 - rho.1.re) rho.1.im N (k N))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  let u := 3 / 2 - rho.1.re
  have hu : 1 / 2 ≤ u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hkt : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hk, eventually_ge_atTop (200 * b)] with N hkN hNb
    omega
  let Z := (∑' n, zetaPrimeExpWeight (1025 / 1024) n) +
    ∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    (Real.exp_pos (-(1 / 25000 : ℝ)))
    (Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 25000 : ℝ) < 0))).mul_const Z
  simp only [zero_mul] at ht
  have herr : Tendsto (fun N => (k N : ℂ) * ((u : ℂ) ^ k N *
      (finiteMoment (intermediatePrimes u N) (k N) (3 / 2 + Complex.I * rho.1.im) -
        ordinaryPrimeMoment (k N) (3 / 2 + Complex.I * rho.1.im)))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ =>
      (N + 1 : ℝ) ^ 3 * Real.exp (-(1 / 25000 : ℝ)) ^ N * Z) ?_ ht
    filter_upwards [eventually_parity_weighted_error hu huU, hk] with N hN hkN
    have he : Real.exp (-(1 / 25000 : ℝ)) ^ N = Real.exp (-(N : ℝ) / 25000) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    exact hN (k N) hkN.1 hkN.2 rho.1.im
  have h := ((ZetaRieszPrimeCompletionPhase.tendsto_weighted_complete rho hrho hexposed).comp hkt).add herr
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  dsimp only [Function.comp_def, weightedFinite]
  ring

theorem eventually_uniform_parity_phase (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 200 * k → 40 * k ≤ 27 * N →
      ‖weightedFinite (3 / 2 - rho.1.re) rho.1.im N k +
        (analyticZetaZeroMultiplicity rho : ℂ)‖ ≤ ε := by
  apply ZetaRieszInfinitePhysical.eventually_forall_of_all_selections
  intro f
  let k : ℕ → ℕ := fun N => if N ≤ 200 * f N ∧ 40 * f N ≤ 27 * N then f N else N / 2
  have hk : ∀ᶠ N : ℕ in atTop, N ≤ 200 * k N ∧ 40 * k N ≤ 27 * N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    by_cases hf : N ≤ 200 * f N ∧ 40 * f N ≤ 27 * N
    · simpa only [k, if_pos hf] using hf
    · simp only [k, if_neg hf]
      omega
  have h := ((tendsto_parity_weighted_finite rho hrho hexposed huU k hk).add_const
    (analyticZetaZeroMultiplicity rho : ℂ)).norm
  simp only [neg_add_cancel, norm_zero] at h
  filter_upwards [h.eventually (eventually_lt_nhds hε)] with N hN
  intro hlow hhigh
  simpa only [k, if_pos (And.intro hlow hhigh)] using hN.le

end
end RiemannGaussian.ZetaRieszParityOrderPhase

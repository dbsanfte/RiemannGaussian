/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusMultipleBound

/-!
# Uniform arithmetic decay for all mixed-prime multiple sectors

The original source normalization beats the entire finite-prefix cost
uniformly over every positive mixed-prime factor, with no restriction
on its size or growth. Genuine arithmetic sums and arbitrary finite
complex factor families inherit the bound. The full original source
remains in the literal complement; no bound on that complement is assumed.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Every selected multiple-sector moment is a genuinely convergent
arithmetic sum, including its complete product phase. -/
theorem hasSum_zetaMoebiusMultipleFilter (p : Polynomial ℂ) (D N : ℕ) {P : ℕ}
    (hP : 0 < P) (hP1 : P ≠ 1) (hmix : ¬IsPrimePow P) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaMoebiusMultipleCoefficient D P n * zetaPrimeFilterKernel p N s n)
      (zetaMoebiusMultipleFilter p D P N s) := by
  have ha : LSeries.abscissaOfAbsConv (zetaMoebiusMultipleCoefficient D P) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro y hy
    exact (LSeriesHasSum_zetaMoebiusMultipleResponse D hP hP1 hmix (by simpa using hy)).LSeriesSummable
  have he : zetaMoebiusMultipleResponse D P =ᶠ[𝓝 s]
      LSeries (zetaMoebiusMultipleCoefficient D P) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact (LSeriesHasSum_zetaMoebiusMultipleResponse D hP hP1 hmix hz).LSeries_eq.symm
  have hm (k : ℕ) : HasSum (fun n ↦ zetaMoebiusMultipleCoefficient D P n *
      ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * zetaPrimeFeature s n)
      (signedTaylorMoment k (zetaMoebiusMultipleResponse D P) s) := by
    rw [signedTaylorMoment_congr k he]
    exact hasSum_signedTaylorMoment_LSeries _ (by simp [zetaMoebiusMultipleCoefficient,
      zetaMoebiusLogTailCoefficient]) (lt_of_le_of_lt ha (by exact_mod_cast hs)) k
  have h := hasSum_sum (s := p.support) (fun k _ ↦ (hm (N + k)).mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Every finite complex factor family has the same cutoff budget times
its total absolute weight. The factors can be arbitrarily large, overlap,
and have arbitrary prime valuations; the exact weighted sum is retained. -/
theorem exists_zetaMoebiusMultipleFamily_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N : ℕ) (S : Finset ℕ) (w : ℕ → ℂ),
      (∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) →
      ‖∑ P ∈ S, w P * ∑' n, zetaMoebiusMultipleCoefficient D P n *
        zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ≤
        C * D * (∑ k ∈ p.support, ‖p.coeff k‖) * ∑ P ∈ S, ‖w P‖ := by
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusMultipleFilter_bound y hy
  refine ⟨C, hC, ?_⟩
  intro p D N S w hS
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ P ∈ S, ‖w P‖ * (C * D * ∑ k ∈ p.support, ‖p.coeff k‖) := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨hP0, hP1, hmix⟩ := hS P hP
      rw [(hasSum_zetaMoebiusMultipleFilter p D N hP0 hP1 hmix (by norm_num)).tsum_eq, norm_mul]
      exact mul_le_mul_of_nonneg_left (hb p D P N hP0) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The normalized estimate is uniform in every positive factor, with
no factor-growth condition. Its geometric ratio is strictly below one
at every hypothetical zero right of the critical line. -/
theorem exists_zetaRightHalfMoebiusMultiple_uniform_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N P : ℕ, 0 < P →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaMoebiusMultipleFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) P N
          (3 / 2 + I * rho.1.im)‖ ≤ C * (Real.sqrt (3 / 2 - rho.1.re)) ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let p := zetaRightHalfPoleJetFilter rho hrho
  let S : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq : 1 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu hu1).le
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusMultipleFilter_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho)
  refine ⟨C * u * S + 1, by positivity, ?_⟩
  intro N P hP
  let D := zetaMoebiusGeometricCutoff q N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg (zero_le_one.trans hq) N)
  have hpow : 1 ≤ q ^ N := one_le_pow₀ hq
  have hD2 : (D : ℝ) ≤ (q ^ N) ^ 2 := by nlinarith
  have hbound := hb p D P N hP
  change ‖(u : ℂ) ^ (N + 1) * zetaMoebiusMultipleFilter p D P N (3 / 2 + I * rho.1.im)‖ ≤ _
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * D * S) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ u ^ (N + 1) * (C * (q ^ N) ^ 2 * S) := by gcongr
    _ = (C * u * S) * (u * q ^ 2) ^ N := by
      rw [mul_pow, pow_succ, show (q ^ N) ^ 2 = (q ^ 2) ^ N by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      ring
    _ = (C * u * S) * (Real.sqrt u) ^ N := by rw [zetaMoebiusHeadGrowth_rate hu]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- Every moving positive factor has negligible response, independently
of its growth. The estimate is uniform before choosing that factor. -/
theorem tendsto_zetaRightHalfMoebiusMultiple_moving (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (P : ℕ → ℕ) (hP : ∀ᶠ N in atTop, 0 < P N) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusMultipleFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) (P N) N
        (3 / 2 + I * rho.1.im)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_zetaRightHalfMoebiusMultiple_uniform_bound rho hrho
  have hu : 0 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : 3 / 2 - rho.1.re < 1 := by linarith
  have hr : Real.sqrt (3 / 2 - rho.1.re) < 1 := by
    nlinarith [Real.sq_sqrt hu.le, Real.sqrt_nonneg (3 / 2 - rho.1.re)]
  apply squeeze_zero_norm' _
    (by simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg _) hr).const_mul C)
  filter_upwards [hP] with N hN
  exact hb N (P N) hN

/-- Independent decay of the entire actual arithmetic multiple sector,
for arbitrary moving mixed-prime factors without a growth restriction. -/
theorem tendsto_zetaRightHalfMoebiusMultiple_actualSum (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (P : ℕ → ℕ)
    (hP : ∀ᶠ N in atTop, 0 < P N ∧ P N ≠ 1 ∧ ¬IsPrimePow (P N)) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑' n,
      zetaMoebiusMultipleCoefficient
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) (P N) n *
        zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n)
      atTop (𝓝 0) := by
  apply (tendsto_zetaRightHalfMoebiusMultiple_moving rho hrho P (hP.mono (fun _ h ↦ h.1))).congr'
  filter_upwards [hP] with N hN
  rw [(hasSum_zetaMoebiusMultipleFilter _ _ N hN.1 hN.2.1 hN.2.2 (by norm_num)).tsum_eq]

/-- Every moving finite complex family is negligible when its total
absolute weight is at most the original cofinal divisor cutoff. Factors
and their number have no separate restriction. This includes signed
overlap corrections whenever their explicit total cost meets that budget. -/
theorem tendsto_zetaRightHalfMoebiusMultipleFamily_actualSum (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (S : ℕ → Finset ℕ) (w : ℕ → ℕ → ℂ)
    (hS : ∀ᶠ N in atTop, (∀ P ∈ S N, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) ∧
      (∑ P ∈ S N, ‖w N P‖) ≤
        zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑ P ∈ S N, w N P * ∑' n,
      zetaMoebiusMultipleCoefficient
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) P n *
        zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n)
      atTop (𝓝 0) := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let p := zetaRightHalfPoleJetFilter rho hrho
  let B : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq : 1 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu hu1).le
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hr : Real.sqrt u < 1 := by nlinarith [Real.sq_sqrt hu.le, Real.sqrt_nonneg u]
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusMultipleFamily_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho)
  apply squeeze_zero_norm' _
    (by
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg u) hr).const_mul (C * u * B))
  filter_upwards [hS] with N hN
  let D := zetaMoebiusGeometricCutoff q N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg (zero_le_one.trans hq) N)
  have hw : (∑ P ∈ S N, ‖w N P‖) ≤ q ^ N := hN.2.trans hD
  have hbound := hb p D N (S N) (w N) hN.1
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * D * B * ∑ P ∈ S N, ‖w N P‖) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ u ^ (N + 1) * (C * q ^ N * B * q ^ N) := by gcongr
    _ = (C * u * B) * (u * q ^ 2) ^ N := by
      rw [mul_pow, pow_succ, show (q ^ 2) ^ N = (q ^ N) ^ 2 by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      ring
    _ = (C * u * B) * (Real.sqrt u) ^ N := by rw [zetaMoebiusHeadGrowth_rate hu]

/-- The literal complementary products after deleting all multiples
of the selected factor. No independent bound is assumed for this sum. -/
def zetaMoebiusMultipleRemainderFilter (p : Polynomial ℂ) (D P N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, if ¬P ∣ n then zetaMoebiusLogTailCoefficient D n * zetaPrimeFilterKernel p N s n else 0

/-- The exact sector-plus-complement identity uses two genuinely
summable arithmetic series and preserves the full original tail. -/
theorem zetaMoebiusLogTailFilter_eq_multiple_add_remainder (p : Polynomial ℂ) (D N : ℕ)
    {P : ℕ} (hP : 0 < P) (hP1 : P ≠ 1) (hmix : ¬IsPrimePow P) {s : ℂ} (hs : 1 < s.re) :
    zetaMoebiusLogTailFilter p D N s = zetaMoebiusMultipleFilter p D P N s +
      zetaMoebiusMultipleRemainderFilter p D P N s := by
  have hRem : Summable (fun n ↦ if ¬P ∣ n then
      zetaMoebiusLogTailCoefficient D n * zetaPrimeFilterKernel p N s n else 0) := by
    have h := (hasSum_zetaMoebiusLogTailFilter_kernel p D N hs).summable.indicator {n | ¬P ∣ n}
    apply h.congr
    intro n
    by_cases hn : P ∣ n <;> simp [Set.indicator, hn]
  rw [← (hasSum_zetaMoebiusLogTailFilter_kernel p D N hs).tsum_eq,
    ← (hasSum_zetaMoebiusMultipleFilter p D N hP hP1 hmix hs).tsum_eq,
    zetaMoebiusMultipleRemainderFilter,
    ← (hasSum_zetaMoebiusMultipleFilter p D N hP hP1 hmix hs).summable.tsum_add hRem]
  apply tsum_congr
  intro n
  by_cases hn : P ∣ n <;> simp [zetaMoebiusMultipleCoefficient, hn]

/-- The whole negative multiplicity source survives in the literal
complement of every chosen moving mixed-prime multiple sector. The
independent source-beating inequality for that complement is still open. -/
theorem tendsto_zetaRightHalfMoebiusMultiple_remainder (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (P : ℕ → ℕ)
    (hP : ∀ᶠ N in atTop, 0 < P N ∧ P N ≠ 1 ∧ ¬IsPrimePow (P N)) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusMultipleRemainderFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) (P N) N
        (3 / 2 + I * rho.1.im)) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_zetaRightHalfPoleJetTail rho hrho).sub
    (tendsto_zetaRightHalfMoebiusMultiple_moving rho hrho P (hP.mono (fun _ h ↦ h.1)))
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [hP] with N hN
  rw [zetaMoebiusLogTailFilter_eq_multiple_add_remainder _ _ N hN.1 hN.2.1 hN.2.2 (by norm_num),
    mul_add, add_sub_cancel_left]

end
end RiemannGaussian

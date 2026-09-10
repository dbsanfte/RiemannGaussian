/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusFactorBound
import RiemannGaussian.ZetaPrimeFilterCalculus

/-!
# Independent arithmetic decay for growing coprime factor sectors

The literal factor-sector moments are genuinely convergent arithmetic
sums. Their source-normalized bounds tend to zero uniformly over all
positive factors with `P^2` below the original growing divisor cutoff.
For mixed-prime factors this removes an actual arithmetic sector, with
its complete phase, from the selected-zero source.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The original complete tail filter in its multiplicative-kernel form. -/
theorem hasSum_zetaMoebiusLogTailFilter_kernel (p : Polynomial ℂ) (D N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaMoebiusLogTailCoefficient D n * zetaPrimeFilterKernel p N s n)
      (zetaMoebiusLogTailFilter p D N s) := by
  apply (hasSum_zetaMoebiusLogTailFilter p D N hs).congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat]
  ring

/-- Every physical sector sum is genuinely summable, including factors
outside the mixed-prime case where the new response formula is used. -/
theorem summable_zetaMoebiusFactorSectorKernel (p : Polynomial ℂ) (D P N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ zetaMoebiusFactorSectorCoefficient D P n * zetaPrimeFilterKernel p N s n) := by
  have h := (hasSum_zetaMoebiusLogTailFilter_kernel p D N hs).summable.indicator
    {n | P ∣ n ∧ P.Coprime (n / P)}
  apply h.congr
  intro n
  rw [zetaMoebiusFactorSectorCoefficient_eq]
  by_cases hn : P ∣ n ∧ P.Coprime (n / P) <;> simp [Set.indicator, hn]

/-- The literal sector has absolute convergence throughout the Euler half-plane. -/
theorem abscissaOfAbsConv_zetaMoebiusFactorSector_le_one (D : ℕ) {P : ℕ}
    (hP : 0 < P) (hP1 : P ≠ 1) (hmix : ¬IsPrimePow P) :
    LSeries.abscissaOfAbsConv (zetaMoebiusFactorSectorCoefficient D P) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
  intro y hy
  exact (LSeriesHasSum_zetaMoebiusFactorResponse D hP hP1 hmix (by simpa using hy)).LSeriesSummable

/-- The filtered response is the actual convergent arithmetic sector,
with every original logarithmic moment and product phase retained. -/
theorem hasSum_zetaMoebiusFactorFilter (p : Polynomial ℂ) (D N : ℕ) {P : ℕ}
    (hP : 0 < P) (hP1 : P ≠ 1) (hmix : ¬IsPrimePow P) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaMoebiusFactorSectorCoefficient D P n * zetaPrimeFilterKernel p N s n)
      (zetaMoebiusFactorFilter p D P N s) := by
  have he : zetaMoebiusFactorResponse D P =ᶠ[𝓝 s]
      LSeries (zetaMoebiusFactorSectorCoefficient D P) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact (LSeriesHasSum_zetaMoebiusFactorResponse D hP hP1 hmix hz).LSeries_eq.symm
  have hm (k : ℕ) : HasSum (fun n ↦ zetaMoebiusFactorSectorCoefficient D P n *
      ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * zetaPrimeFeature s n)
      (signedTaylorMoment k (zetaMoebiusFactorResponse D P) s) := by
    rw [signedTaylorMoment_congr k he]
    exact hasSum_signedTaylorMoment_LSeries _ (zetaMoebiusFactorCoefficient_zero D P).2
      (lt_of_le_of_lt (abscissaOfAbsConv_zetaMoebiusFactorSector_le_one D hP hP1 hmix)
        (by exact_mod_cast hs)) k
  have h := hasSum_sum (s := p.support) (fun k _ ↦ (hm (N + k)).mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The entire complementary arithmetic sum, retaining every product
outside the selected coprime factor sector. -/
def zetaMoebiusFactorRemainderFilter (p : Polynomial ℂ) (D P N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, if ¬(P ∣ n ∧ P.Coprime (n / P)) then
    zetaMoebiusLogTailCoefficient D n * zetaPrimeFilterKernel p N s n else 0

/-- The complementary series is also genuinely summable for every factor. -/
theorem summable_zetaMoebiusFactorRemainderKernel (p : Polynomial ℂ) (D P N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ if ¬(P ∣ n ∧ P.Coprime (n / P)) then
      zetaMoebiusLogTailCoefficient D n * zetaPrimeFilterKernel p N s n else 0) := by
  have h := (hasSum_zetaMoebiusLogTailFilter_kernel p D N hs).summable.indicator
    {n | ¬(P ∣ n ∧ P.Coprime (n / P))}
  apply h.congr
  intro n
  by_cases hn : P ∣ n ∧ P.Coprime (n / P) <;> simp [Set.indicator, hn]

/-- The whole original tail splits exactly into the proved sector
response and its genuinely convergent signed complement. -/
theorem zetaMoebiusLogTailFilter_eq_factor_add_remainder (p : Polynomial ℂ) (D N : ℕ)
    {P : ℕ} (hP : 0 < P) (hP1 : P ≠ 1) (hmix : ¬IsPrimePow P) {s : ℂ} (hs : 1 < s.re) :
    zetaMoebiusLogTailFilter p D N s = zetaMoebiusFactorFilter p D P N s +
      zetaMoebiusFactorRemainderFilter p D P N s := by
  rw [← (hasSum_zetaMoebiusLogTailFilter_kernel p D N hs).tsum_eq,
    ← (hasSum_zetaMoebiusFactorFilter p D N hP hP1 hmix hs).tsum_eq,
    zetaMoebiusFactorRemainderFilter,
    ← (summable_zetaMoebiusFactorSectorKernel p D P N hs).tsum_add
      (summable_zetaMoebiusFactorRemainderKernel p D P N hs)]
  apply tsum_congr
  intro n
  rw [zetaMoebiusFactorSectorCoefficient_eq]
  by_cases hn : P ∣ n ∧ P.Coprime (n / P) <;> simp [hn]

/-- The actual source normalization beats the complete sector bound
uniformly over every positive factor with `P²` below the moving cutoff.
The Cauchy and finite-prefix constants are independent of `P` and `N`. -/
theorem exists_zetaRightHalfMoebiusFactor_uniform_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N P : ℕ, 1 ≤ P →
      P ^ 2 ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaMoebiusFactorFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) P N
          (3 / 2 + I * rho.1.im)‖ ≤ C * (Real.sqrt (Real.sqrt (3 / 2 - rho.1.re))) ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let p := zetaRightHalfPoleJetFilter rho hrho
  let S : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq : 1 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu hu1).le
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusFactorFilter_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho)
  refine ⟨3 * C * u * S + 1, by positivity, ?_⟩
  intro N P hP hcap
  let D := zetaMoebiusGeometricCutoff q N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg (zero_le_one.trans hq) N)
  have hc := mul_zetaMoebiusFactorComplexity_le_cube hP hcap
  have hbound := hb p D P N
  change ‖(u : ℂ) ^ (N + 1) * zetaMoebiusFactorFilter p D P N (3 / 2 + I * rho.1.im)‖ ≤ _
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * D * zetaMoebiusFactorComplexity P * S) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ u ^ (N + 1) * (3 * C * (D : ℝ) ^ 3 * S) := by
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hC.le) hS
      exact mul_le_mul_of_nonneg_left (by nlinarith [h]) (by positivity)
    _ ≤ u ^ (N + 1) * (3 * C * (q ^ N) ^ 3 * S) := by gcongr
    _ = (3 * C * u * S) * (u * q ^ 3) ^ N := by
      rw [mul_pow, pow_succ, show (q ^ N) ^ 3 = (q ^ 3) ^ N by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      ring
    _ = (3 * C * u * S) * (Real.sqrt (Real.sqrt u)) ^ N := by
      rw [zetaMoebiusHeadGrowth_cubic_rate hu]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- The whole sector response is negligible for every moving factor
within the proved range. The growth condition is on the actual factor,
not an assumed estimate for its arithmetic sum. -/
theorem tendsto_zetaRightHalfMoebiusFactor_moving (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (P : ℕ → ℕ)
    (hP : ∀ᶠ N in atTop, 1 ≤ P N ∧ (P N) ^ 2 ≤
      zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusFactorFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) (P N) N
        (3 / 2 + I * rho.1.im)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_zetaRightHalfMoebiusFactor_uniform_bound rho hrho
  have hu : 0 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : 3 / 2 - rho.1.re < 1 := by linarith
  have hs : Real.sqrt (3 / 2 - rho.1.re) < 1 := by
    nlinarith [Real.sq_sqrt hu.le, Real.sqrt_nonneg (3 / 2 - rho.1.re)]
  have hr : Real.sqrt (Real.sqrt (3 / 2 - rho.1.re)) < 1 := by
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg (3 / 2 - rho.1.re)),
      Real.sqrt_nonneg (Real.sqrt (3 / 2 - rho.1.re))]
  apply squeeze_zero_norm' _
    (by simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg _) hr).const_mul C)
  filter_upwards [hP] with N hN
  exact hb N (P N) hN.1 hN.2

/-- Independent decay of the literal signed arithmetic sector, even
with a growing factor. All series converge for every order, and the
response identification is used only where its mixed-prime conditions hold. -/
theorem tendsto_zetaRightHalfMoebiusFactor_actualSum (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (P : ℕ → ℕ)
    (hP : ∀ᶠ N in atTop, 0 < P N ∧ P N ≠ 1 ∧ ¬IsPrimePow (P N) ∧ (P N) ^ 2 ≤
      zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑' n,
      zetaMoebiusFactorSectorCoefficient
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) (P N) n *
        zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n)
      atTop (𝓝 0) := by
  apply (tendsto_zetaRightHalfMoebiusFactor_moving rho hrho P
    (hP.mono (fun _ h ↦ ⟨h.1, h.2.2.2⟩))).congr'
  filter_upwards [hP] with N hN
  rw [(hasSum_zetaMoebiusFactorFilter _ _ N hN.1 hN.2.1 hN.2.2.1 (by norm_num)).tsum_eq]

/-- Removing the independently decaying arithmetic sector leaves the
full negative multiplicity source in its literal complementary products.
The independent signed bound for that complement remains open. -/
theorem tendsto_zetaRightHalfMoebiusFactor_remainder (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (P : ℕ → ℕ)
    (hP : ∀ᶠ N in atTop, 0 < P N ∧ P N ≠ 1 ∧ ¬IsPrimePow (P N) ∧ (P N) ^ 2 ≤
      zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusFactorRemainderFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) (P N) N
        (3 / 2 + I * rho.1.im)) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_zetaRightHalfPoleJetTail rho hrho).sub
    (tendsto_zetaRightHalfMoebiusFactor_moving rho hrho P (hP.mono (fun _ h ↦ ⟨h.1, h.2.2.2⟩)))
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [hP] with N hN
  rw [zetaMoebiusLogTailFilter_eq_factor_add_remainder _ _ N hN.1 hN.2.1 hN.2.2.1 (by norm_num),
    mul_add, add_sub_cancel_left]

/-- Every fixed mixed-prime factor is automatically in the decay range.
No growth or unproved arithmetic estimate is assumed in this specialization
to the actual signed series. -/
theorem tendsto_zetaRightHalfMoebiusFactor_fixed_actualSum (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {P : ℕ} (hP : 0 < P) (hP1 : P ≠ 1)
    (hmix : ¬IsPrimePow P) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑' n,
      zetaMoebiusFactorSectorCoefficient
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) P n *
        zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n)
      atTop (𝓝 0) := by
  apply tendsto_zetaRightHalfMoebiusFactor_actualSum rho hrho (fun _ ↦ P)
  filter_upwards [(tendsto_zetaRightHalfPoleJetCutoff rho hrho).eventually_ge_atTop (P ^ 2)] with N hN
  exact ⟨hP, hP1, hmix, hN⟩

/-- The literal complement of any fixed mixed-prime factor retains the
whole source, with the cutoff condition discharged by its proved cofinality. -/
theorem tendsto_zetaRightHalfMoebiusFactor_fixed_remainder (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {P : ℕ} (hP : 0 < P) (hP1 : P ≠ 1)
    (hmix : ¬IsPrimePow P) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusFactorRemainderFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) P N
        (3 / 2 + I * rho.1.im)) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  apply tendsto_zetaRightHalfMoebiusFactor_remainder rho hrho (fun _ ↦ P)
  filter_upwards [(tendsto_zetaRightHalfPoleJetCutoff rho hrho).eventually_ge_atTop (P ^ 2)] with N hN
  exact ⟨hP, hP1, hmix, hN⟩

end
end RiemannGaussian

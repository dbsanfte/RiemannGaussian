/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MeromorphicPairPoleClearing
import RiemannGaussian.AnalyticDoublePoleMoments

/-!
# Global moment separation of the actual differential zeta responses

A common finite weight clears both complete divisors on an explicit
disc around the Euler center, excluding the selected zero. Cauchy's
estimate then gives a bounded prime contribution at the geometric
source scale, while the full response has a linear nonzero source.
The resulting composite moment retains the full complex difference.
-/

open Complex Filter Function MeromorphicOn Metric Set Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Clearing every other pole of a meromorphic pair leaves a uniform
moment error around the selected double-pole source. If the selected
order is greater than minus two, the same bound has zero source. -/
theorem exists_meromorphicPairClearedMoment_error {f g : ℂ → ℂ} {s a : ℂ} {R : ℝ}
    (hf : MeromorphicOn f (closedBall s R)) (hfs : AnalyticAt ℂ f s)
    (ha : ‖s - a‖ < R) (hne : s ≠ a) (ho : (-2 : WithTop ℤ) ≤ meromorphicOrderAt f a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖(s - a) ^ (n + 2) * signedTaylorMoment n
          (meromorphicPairClearingWeight f g (closedBall s R) a * f) s -
        ((n + 1 : ℕ) : ℂ) * meromorphicPairQuadraticRegular f g (closedBall s R) a a‖ ≤ C := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) ha
  have hs : s ∈ closedBall s R := mem_closedBall_self hR.le
  have hG := analyticOnNhd_meromorphicPairQuadraticRegular (g := g) (isCompact_closedBall s R) hf ho
  have hw := analyticAt_meromorphicPairClearingWeight f g (closedBall s R) a s
  have hraw : AnalyticAt ℂ ((fun z : ℂ ↦ z - a) ^ (2 : ℕ) *
      (meromorphicPairClearingWeight f g (closedBall s R) a * f)) s :=
    (analyticAt_id.sub analyticAt_const).pow 2 |>.mul (hw.mul hfs)
  have he := ((hG s hs).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hraw.continuousAt).mp
    (meromorphicPairQuadraticRegular_eventuallyEq (g := g) (a := a) hf hs)
  have hquot : (meromorphicPairClearingWeight f g (closedBall s R) a * f) =ᶠ[𝓝 s]
      (fun z ↦ meromorphicPairQuadraticRegular f g (closedBall s R) a z / (z - a) ^ 2) := by
    filter_upwards [he, eventually_ne_nhds hne] with z hz hza
    rw [hz]
    simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
  obtain ⟨C, hC, hbound⟩ := exists_doublePoleMoment_uniform_error hG ha hne
  refine ⟨C, hC, fun n ↦ ?_⟩
  rw [signedTaylorMoment_congr n hquot]
  exact hbound n

/-- The Euler center aligned with the selected zero's ordinate. -/
def zetaWronskianMomentCenter (rho : NontrivialZetaZero) : ℂ := 3 / 2 + I * rho.1.im

/-- An explicit radius between the selected zero and the critical
boundary. Boundary poles are included in the complete divisor. -/
def zetaWronskianMomentRadius (rho : NontrivialZetaZero) : ℝ := 5 / 4 - rho.1.re / 2

/-- The compact domain on which both actual pole sets are cleared. -/
def zetaWronskianMomentDomain (rho : NontrivialZetaZero) : Set ℂ :=
  closedBall (zetaWronskianMomentCenter rho) (zetaWronskianMomentRadius rho)

/-- The actual common finite weight, fixed independently of moment
order and determined by the two complete meromorphic divisors. -/
def zetaWronskianMomentWeight (rho : NontrivialZetaZero) : ℂ → ℂ :=
  meromorphicPairClearingWeight (zetaMoebiusWronskian rho) (zetaMoebiusPrimeWronskian rho)
    (zetaWronskianMomentDomain rho) rho.1

/-- The source coefficient keeps the selected leading zeta phase and
the explicit nonzero value of the common clearing weight. -/
def zetaWronskianMomentSource (rho : NontrivialZetaZero) : ℂ :=
  zetaWronskianMomentWeight rho rho.1 *
    ((analyticZetaZeroMultiplicity rho : ℂ) ^ 3 * meromorphicTrailingCoeffAt riemannZeta rho.1)

/-- The complete signed factorial moment after the common weighting. -/
def zetaWronskianFullMoment (rho : NontrivialZetaZero) (n : ℕ) : ℂ :=
  signedTaylorMoment n (zetaWronskianMomentWeight rho * zetaMoebiusWronskian rho)
    (zetaWronskianMomentCenter rho)

/-- The prime contribution with exactly the same weight and moment
normalization. -/
def zetaWronskianPrimeMoment (rho : NontrivialZetaZero) (n : ℕ) : ℂ :=
  signedTaylorMoment n (zetaWronskianMomentWeight rho * zetaMoebiusPrimeWronskian rho)
    (zetaWronskianMomentCenter rho)

/-- The complete signed composite contribution. Its arithmetic series
will be retained together with this derivative definition. -/
def zetaWronskianCompositeMoment (rho : NontrivialZetaZero) (n : ℕ) : ℂ :=
  signedTaylorMoment n (zetaWronskianMomentWeight rho * zetaMoebiusCompositeWronskian rho)
    (zetaWronskianMomentCenter rho)

/-- The selected complex displacement is the genuine positive real
distance from the Euler center to the zero. -/
theorem zetaWronskianMomentCenter_sub (rho : NontrivialZetaZero) :
    zetaWronskianMomentCenter rho - rho.1 = ((3 / 2 - rho.1.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [zetaWronskianMomentCenter]

/-- Every selected right-half zero lies strictly inside the explicit
disc, and the disc stays strictly to the right of one half. -/
theorem zetaWronskianMomentRadius_spec (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    0 < ‖zetaWronskianMomentCenter rho - rho.1‖ ∧
      ‖zetaWronskianMomentCenter rho - rho.1‖ < zetaWronskianMomentRadius rho ∧
      zetaWronskianMomentRadius rho < 1 := by
  have hu : 0 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  rw [zetaWronskianMomentCenter_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  dsimp [zetaWronskianMomentRadius]
  exact ⟨hu, by linarith, by linarith⟩

private theorem selected_mem_domain (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    rho.1 ∈ zetaWronskianMomentDomain rho := by
  simpa [zetaWronskianMomentDomain, mem_closedBall, dist_eq_norm, norm_sub_rev] using
    (zetaWronskianMomentRadius_spec rho hrho).2.1.le

private theorem domain_re_gt_half (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {s : ℂ} (hs : s ∈ zetaWronskianMomentDomain rho) : 1 / 2 < s.re := by
  have hnorm : ‖s - zetaWronskianMomentCenter rho‖ ≤ zetaWronskianMomentRadius rho := by
    simpa [zetaWronskianMomentDomain, mem_closedBall, dist_eq_norm] using hs
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (s - zetaWronskianMomentCenter rho)).trans hnorm)).1
  have hc : (zetaWronskianMomentCenter rho).re = 3 / 2 := by simp [zetaWronskianMomentCenter]
  rw [Complex.sub_re, hc] at hre
  have hR := (zetaWronskianMomentRadius_spec rho hrho).2.2
  linarith

/-- The common weight has actual finite support on this compact disc. -/
theorem hasFiniteSupport_zetaWronskianMomentExponent (rho : NontrivialZetaZero) :
    (meromorphicPairClearingExponent (zetaMoebiusWronskian rho) (zetaMoebiusPrimeWronskian rho)
      (zetaWronskianMomentDomain rho) rho.1).HasFiniteSupport :=
  hasFiniteSupport_meromorphicPairClearingExponent _ _ (isCompact_closedBall _ _) _

/-- The weight is entire and is never defined by a divergent product. -/
theorem analyticAt_zetaWronskianMomentWeight (rho : NontrivialZetaZero) (s : ℂ) :
    AnalyticAt ℂ (zetaWronskianMomentWeight rho) s := analyticAt_meromorphicPairClearingWeight ..

/-- The weighted selected source is nonzero for its actual multiplicity. -/
theorem zetaWronskianMomentSource_ne_zero (rho : NontrivialZetaZero) :
    zetaWronskianMomentSource rho ≠ 0 := by
  rw [zetaWronskianMomentSource, ← meromorphicTrailingCoeffAt_zetaMoebiusWronskian]
  exact mul_ne_zero (meromorphicPairClearingWeight_ne_zero (zetaMoebiusWronskian rho)
    (zetaMoebiusPrimeWronskian rho) (zetaWronskianMomentDomain rho) rho.1)
    (meromorphicTrailingCoeffAt_zetaMoebiusWronskian_ne_zero rho)

private theorem cofactor_analytic_euler (rho : NontrivialZetaZero) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (zetaMoebiusWronskianCofactor rho) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hsr : s ≠ rho.1 := by intro h; rw [h] at hs; linarith [NontrivialZetaZero.re_lt_one rho]
  have hz := analyticOn_riemannZeta s (by simpa using hs1)
  change AnalyticAt ℂ ((deriv riemannZeta) ^ 2 /
    ((fun z ↦ z - rho.1) ^ ((analyticZetaZeroMultiplicity rho : ℤ) - 1))) s
  exact (hz.deriv.pow 2).div ((analyticAt_id.sub analyticAt_const).zpow (sub_ne_zero.mpr hsr))
    (zpow_ne_zero _ (sub_ne_zero.mpr hsr))

private theorem full_analytic_euler (rho : NontrivialZetaZero) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (zetaMoebiusWronskian rho) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hz := analyticOn_riemannZeta s (by simpa using hs1)
  exact (cofactor_analytic_euler rho hs).mul
    (hz.deriv.div (hz.pow 2) (pow_ne_zero _ (riemannZeta_ne_zero_of_one_lt_re hs)))

private theorem prime_analytic_euler (rho : NontrivialZetaZero) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (zetaMoebiusPrimeWronskian rho) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hz := analyticOn_riemannZeta s (by simpa using hs1)
  exact (cofactor_analytic_euler rho hs).mul
    ((hz.deriv.div hz (riemannZeta_ne_zero_of_one_lt_re hs)).add
      (analyticAt_zetaProperPrimePowerSeries (by linarith)))

/-- The complete moment has a linear selected source and a uniformly
bounded error, after every other pole has actually been cleared. -/
theorem exists_zetaWronskianFullMoment_error (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖(zetaWronskianMomentCenter rho - rho.1) ^ (n + 2) * zetaWronskianFullMoment rho n -
        ((n + 1 : ℕ) : ℂ) * zetaWronskianMomentSource rho‖ ≤ C := by
  have hspec := zetaWronskianMomentRadius_spec rho hrho
  have hm : MeromorphicOn (zetaMoebiusWronskian rho) (zetaWronskianMomentDomain rho) :=
    fun s _ ↦ meromorphicAt_zetaMoebiusWronskian rho s
  have he := meromorphicPairQuadraticRegular_apply (g := zetaMoebiusPrimeWronskian rho)
    (isCompact_closedBall _ _) hm (selected_mem_domain rho hrho)
    (meromorphicOrderAt_zetaMoebiusWronskian rho)
  rw [meromorphicTrailingCoeffAt_zetaMoebiusWronskian] at he
  obtain ⟨C, hC, hb⟩ := exists_meromorphicPairClearedMoment_error (g := zetaMoebiusPrimeWronskian rho)
    hm (full_analytic_euler rho (by norm_num [zetaWronskianMomentCenter])) hspec.2.1
    (sub_ne_zero.mp (norm_pos_iff.mp hspec.1)) (by rw [meromorphicOrderAt_zetaMoebiusWronskian])
  refine ⟨C, hC, fun n ↦ ?_⟩
  simpa only [he, zetaWronskianFullMoment, zetaWronskianMomentSource, zetaWronskianMomentWeight,
    zetaWronskianMomentDomain] using hb n

/-- An independent uniform upper bound for the actual prime
contribution at the geometric source scale. Every pole in the closed
disc, including the pole at one if present, is included in the clearing. -/
theorem exists_zetaWronskianPrimeMoment_bound (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖(zetaWronskianMomentCenter rho - rho.1) ^ (n + 2) * zetaWronskianPrimeMoment rho n‖ ≤ C := by
  have hspec := zetaWronskianMomentRadius_spec rho hrho
  have hm : MeromorphicOn (zetaMoebiusPrimeWronskian rho) (zetaWronskianMomentDomain rho) :=
    fun _ hs ↦ meromorphicAt_zetaMoebiusPrimeWronskian rho (domain_re_gt_half rho hrho hs)
  have ho : (-2 : WithTop ℤ) < meromorphicOrderAt (zetaMoebiusPrimeWronskian rho) rho.1 := by
    rw [meromorphicOrderAt_zetaMoebiusPrimeWronskian rho hrho]
    change ((-2 : ℤ) : WithTop ℤ) < (((analyticZetaZeroMultiplicity rho : ℤ) - 2 : ℤ) : WithTop ℤ)
    rw [WithTop.coe_lt_coe]
    have := analyticZetaZeroMultiplicity_positive rho
    omega
  have he := meromorphicPairQuadraticRegular_eq_zero (g := zetaMoebiusWronskian rho)
    (isCompact_closedBall _ _) hm (selected_mem_domain rho hrho) ho
  obtain ⟨C, hC, hb⟩ := exists_meromorphicPairClearedMoment_error (g := zetaMoebiusWronskian rho)
    hm (prime_analytic_euler rho (by norm_num [zetaWronskianMomentCenter])) hspec.2.1
    (sub_ne_zero.mp (norm_pos_iff.mp hspec.1)) ho.le
  refine ⟨C, hC, fun n ↦ ?_⟩
  simpa only [he, mul_zero, sub_zero, zetaWronskianPrimeMoment, zetaWronskianMomentWeight,
    zetaWronskianMomentDomain,
    meromorphicPairClearingWeight_comm (zetaMoebiusPrimeWronskian rho) (zetaMoebiusWronskian rho)] using hb n

/-- The composite moment is the exact signed difference under the
common weight, with both factors analytic at the Euler center. -/
theorem zetaWronskianCompositeMoment_eq_sub (rho : NontrivialZetaZero) (n : ℕ) :
    zetaWronskianCompositeMoment rho n = zetaWronskianFullMoment rho n - zetaWronskianPrimeMoment rho n := by
  have hcenter : 1 < (zetaWronskianMomentCenter rho).re := by norm_num [zetaWronskianMomentCenter]
  have hfull : AnalyticAt ℂ (fun z ↦ zetaWronskianMomentWeight rho z * zetaMoebiusWronskian rho z)
      (zetaWronskianMomentCenter rho) :=
    (analyticAt_zetaWronskianMomentWeight rho _).mul (full_analytic_euler rho hcenter)
  have hprime : AnalyticAt ℂ (fun z ↦ zetaWronskianMomentWeight rho z * zetaMoebiusPrimeWronskian rho z)
      (zetaWronskianMomentCenter rho) :=
    (analyticAt_zetaWronskianMomentWeight rho _).mul (prime_analytic_euler rho hcenter)
  change signedTaylorMoment n (fun z ↦ zetaWronskianMomentWeight rho z *
    (zetaMoebiusWronskian rho z - zetaMoebiusPrimeWronskian rho z)) _ = _
  simp only [mul_sub]
  exact signedTaylorMoment_sub n hfull hprime

/-- The composite response retains the full linear source with a
uniformly bounded error after the independently bounded prime arm is
removed. This does not bound the composite source from the other side. -/
theorem exists_zetaWronskianCompositeMoment_error (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖(zetaWronskianMomentCenter rho - rho.1) ^ (n + 2) * zetaWronskianCompositeMoment rho n -
        ((n + 1 : ℕ) : ℂ) * zetaWronskianMomentSource rho‖ ≤ C := by
  obtain ⟨C, hC, hc⟩ := exists_zetaWronskianFullMoment_error rho hrho
  obtain ⟨D, hD, hd⟩ := exists_zetaWronskianPrimeMoment_bound rho hrho
  refine ⟨C + D, by positivity, fun n ↦ ?_⟩
  rw [zetaWronskianCompositeMoment_eq_sub, mul_sub, sub_right_comm]
  exact (norm_sub_le _ _).trans (add_le_add (hc n) (hd n))

private theorem norm_div_nat_succ_sub_le {x c : ℂ} {C : ℝ} (n : ℕ)
    (h : ‖x - ((n + 1 : ℕ) : ℂ) * c‖ ≤ C) :
    ‖x / ((n + 1 : ℕ) : ℂ) - c‖ ≤ C / ((n + 1 : ℕ) : ℝ) := by
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [show x / ((n + 1 : ℕ) : ℂ) - c = (x - ((n + 1 : ℕ) : ℂ) * c) / ((n + 1 : ℕ) : ℂ) by
    field_simp, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)

/-- The actual normalized prime contribution has the quantitative
sub-source bound `C/(n+1)` for every moment order. -/
theorem exists_zetaWronskianPrimeMoment_decay_bound (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖((zetaWronskianMomentCenter rho - rho.1) ^ (n + 2) * zetaWronskianPrimeMoment rho n) /
        ((n + 1 : ℕ) : ℂ)‖ ≤ C / ((n + 1 : ℕ) : ℝ) := by
  obtain ⟨C, hC, hc⟩ := exists_zetaWronskianPrimeMoment_bound rho hrho
  refine ⟨C, hC, fun n ↦ ?_⟩
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (hc n) (Nat.cast_nonneg _)

/-- The complete normalized composite source has an explicit
`C/(n+1)` error allowance, with the complex source retained. -/
theorem exists_zetaWronskianCompositeMoment_decay_bound (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖((zetaWronskianMomentCenter rho - rho.1) ^ (n + 2) * zetaWronskianCompositeMoment rho n) /
        ((n + 1 : ℕ) : ℂ) - zetaWronskianMomentSource rho‖ ≤ C / ((n + 1 : ℕ) : ℝ) := by
  obtain ⟨C, hC, hc⟩ := exists_zetaWronskianCompositeMoment_error rho hrho
  exact ⟨C, hC, fun n ↦ norm_div_nat_succ_sub_le n (hc n)⟩

/-- The complete cofactor entering the literal arithmetic kernel. -/
def zetaWronskianArithmeticCofactor (rho : NontrivialZetaZero) (s : ℂ) : ℂ :=
  zetaWronskianMomentWeight rho s * zetaMoebiusWronskianCofactor rho s

/-- The exact complex kernel includes every cofactor derivative and
Dirichlet logarithmic moment, before any estimate is applied. -/
def zetaWronskianArithmeticKernel (rho : NontrivialZetaZero) (N m : ℕ) : ℂ :=
  zetaPrimeFeature (zetaWronskianMomentCenter rho) m *
    ∑ k ∈ Finset.range (N + 1),
      signedTaylorMoment k (zetaWronskianArithmeticCofactor rho) (zetaWronskianMomentCenter rho) *
        ((Real.log m : ℂ) ^ (N - k) / ((N - k).factorial : ℂ))

private theorem weighted_series_moment {c : ℕ → ℂ} (hc0 : c 0 = 0) {V A : ℂ → ℂ}
    (hV : ∀ s : ℂ, 1 < s.re → LSeriesHasSum c s (V s)) {s : ℂ} (hs : 1 < s.re)
    (hA : AnalyticAt ℂ A s) (N : ℕ) :
    HasSum (fun m : ℕ ↦ c m * zetaPrimeFeature s m *
      ∑ k ∈ Finset.range (N + 1), signedTaylorMoment k A s *
        ((Real.log m : ℂ) ^ (N - k) / ((N - k).factorial : ℂ)))
      (signedTaylorMoment N (fun z ↦ A z * V z) s) := by
  have hb : LSeries.abscissaOfAbsConv c ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro x hx
    exact (hV x (by simpa using hx)).LSeriesSummable
  have he : (fun z ↦ A z * V z) =ᶠ[𝓝 s] (fun z ↦ A z * LSeries c z) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    rw [(hV z hz).LSeries_eq]
  rw [signedTaylorMoment_congr N he]
  exact hasSum_signedTaylorMoment_mul_LSeries c hc0 hA
    (lt_of_le_of_lt hb (by exact_mod_cast hs)) N

private theorem arithmetic_cofactor_analytic (rho : NontrivialZetaZero) :
    AnalyticAt ℂ (zetaWronskianArithmeticCofactor rho) (zetaWronskianMomentCenter rho) :=
  (analyticAt_zetaWronskianMomentWeight rho _).mul
    (cofactor_analytic_euler rho (by norm_num [zetaWronskianMomentCenter]))

/-- The full globally weighted moment is a literal convergent sum
with coefficients `mu(m) log(m)` and the common exact arithmetic kernel. -/
theorem hasSum_zetaWronskianFullMoment (rho : NontrivialZetaZero) (N : ℕ) :
    HasSum (fun m ↦ zetaMoebiusDerivativeCoefficient m * zetaWronskianArithmeticKernel rho N m)
      (zetaWronskianFullMoment rho N) := by
  have h := weighted_series_moment (by simp [zetaMoebiusDerivativeCoefficient])
    (fun _ hs ↦ LSeriesHasSum_zetaMoebiusDerivative hs)
    (by norm_num [zetaWronskianMomentCenter]) (arithmetic_cofactor_analytic rho) N
  change HasSum _ (signedTaylorMoment N (fun z ↦ zetaWronskianMomentWeight rho z *
    zetaMoebiusWronskian rho z) (zetaWronskianMomentCenter rho))
  simpa only [zetaWronskianArithmeticKernel, zetaWronskianArithmeticCofactor, zetaMoebiusWronskian,
    mul_assoc] using h

/-- The independently bounded prime moment is the actual prime
restriction of that same convergent arithmetic kernel. -/
theorem hasSum_zetaWronskianPrimeMoment (rho : NontrivialZetaZero) (N : ℕ) :
    HasSum (fun m ↦ (if m.Prime then zetaMoebiusDerivativeCoefficient m else 0) *
      zetaWronskianArithmeticKernel rho N m) (zetaWronskianPrimeMoment rho N) := by
  have h := weighted_series_moment (by simp [zetaMoebiusDerivativeCoefficient])
    (fun _ hs ↦ LSeriesHasSum_zetaMoebiusPrimeDerivative hs)
    (by norm_num [zetaWronskianMomentCenter]) (arithmetic_cofactor_analytic rho) N
  change HasSum _ (signedTaylorMoment N (fun z ↦ zetaWronskianMomentWeight rho z *
    zetaMoebiusPrimeWronskian rho z) (zetaWronskianMomentCenter rho))
  simpa only [zetaWronskianArithmeticKernel, zetaWronskianArithmeticCofactor, zetaMoebiusPrimeWronskian,
    mul_assoc] using h

/-- The remaining globally weighted moment is exactly the convergent
squarefree-composite Möbius sum with all cofactor phases retained. -/
theorem hasSum_zetaWronskianCompositeMoment (rho : NontrivialZetaZero) (N : ℕ) :
    HasSum (fun m ↦ zetaMoebiusCompositeDerivativeCoefficient m * zetaWronskianArithmeticKernel rho N m)
      (zetaWronskianCompositeMoment rho N) := by
  have h := weighted_series_moment (by simp [zetaMoebiusCompositeDerivativeCoefficient,
      zetaMoebiusDerivativeCoefficient])
    (fun _ hs ↦ LSeriesHasSum_zetaMoebiusCompositeDerivative hs)
    (by norm_num [zetaWronskianMomentCenter]) (arithmetic_cofactor_analytic rho) N
  change HasSum _ (signedTaylorMoment N (fun z ↦ zetaWronskianMomentWeight rho z *
    zetaMoebiusCompositeWronskian rho z) (zetaWronskianMomentCenter rho))
  simpa only [zetaWronskianArithmeticKernel, zetaWronskianArithmeticCofactor, zetaMoebiusCompositeWronskian,
    zetaMoebiusWronskian, zetaMoebiusPrimeWronskian, mul_sub, mul_assoc] using h

private theorem tendsto_div_nat_succ (C : ℝ) :
    Tendsto (fun n : ℕ ↦ C / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
  ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)).const_div_atTop C

/-- The independently bounded literal prime moment tends to zero
after the full double-pole normalization. -/
theorem tendsto_zetaWronskianPrimeMoment (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun n : ℕ ↦
      ((zetaWronskianMomentCenter rho - rho.1) ^ (n + 2) * zetaWronskianPrimeMoment rho n) /
        ((n + 1 : ℕ) : ℂ)) atTop (𝓝 0) := by
  obtain ⟨C, _, hc⟩ := exists_zetaWronskianPrimeMoment_decay_bound rho hrho
  exact squeeze_zero_norm hc (tendsto_div_nat_succ C)

/-- The literal composite arithmetic moment converges to the exact
nonzero complex source, with the proved reciprocal-linear error bound. -/
theorem tendsto_zetaWronskianCompositeMoment (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun n : ℕ ↦
      ((zetaWronskianMomentCenter rho - rho.1) ^ (n + 2) * zetaWronskianCompositeMoment rho n) /
        ((n + 1 : ℕ) : ℂ)) atTop (𝓝 (zetaWronskianMomentSource rho)) := by
  obtain ⟨C, _, hc⟩ := exists_zetaWronskianCompositeMoment_decay_bound rho hrho
  have h := squeeze_zero_norm hc (tendsto_div_nat_succ C)
  simpa only [sub_add_cancel, zero_add] using h.add_const (zetaWronskianMomentSource rho)

/-- Rotating and scaling by the retained source makes the remaining
signed arithmetic target precise: its real part tends to one. -/
theorem tendsto_zetaWronskianCompositeMoment_aligned (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun n : ℕ ↦ ((zetaWronskianMomentSource rho)⁻¹ *
      (((zetaWronskianMomentCenter rho - rho.1) ^ (n + 2) * zetaWronskianCompositeMoment rho n) /
        ((n + 1 : ℕ) : ℂ))).re) atTop (𝓝 1) := by
  have h := (Complex.continuous_re.tendsto _).comp
    ((tendsto_zetaWronskianCompositeMoment rho hrho).const_mul ((zetaWronskianMomentSource rho)⁻¹))
  simpa only [inv_mul_cancel₀ (zetaWronskianMomentSource_ne_zero rho), Complex.one_re,
    Function.comp_def] using h

/-- The remaining arithmetic response eventually exceeds half its
full source in the source's exact direction. An independent upper
bound below this threshold is still required for the contradiction. -/
theorem zetaWronskianCompositeMoment_eventually_aligned (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) < ((zetaWronskianMomentSource rho)⁻¹ *
      (((zetaWronskianMomentCenter rho - rho.1) ^ (n + 2) * zetaWronskianCompositeMoment rho n) /
        ((n + 1 : ℕ) : ℂ))).re :=
  (tendsto_zetaWronskianCompositeMoment_aligned rho hrho).eventually (lt_mem_nhds (by norm_num))

end

end RiemannGaussian

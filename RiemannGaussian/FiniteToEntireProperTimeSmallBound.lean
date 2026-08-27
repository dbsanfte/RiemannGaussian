import RiemannGaussian.FiniteToEntireProperTimeSmall

/-!
# Quantitative control at proper time zero

This file exposes the statistic that controls the remaining small-time
frontier.  One upper root contributes at most `4 * z.im * alpha.im` to the
heat at every positive proper time.  Consequently its action before time
`a` is at most `a` times that quantity, and a finite divisor is controlled by
the multiplicity-counted sum of its upper-root heights.

Combining this elementary bound with the canonical concentration theorem
turns small-time escape into a concrete necessary inequality for the growing
polynomial divisors.  No bound on that height statistic is assumed here.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Reflection across the real axis increases squared distance from an upper
observation point by exactly four times the product of the two heights. -/
theorem normSq_sub_conj_eq_normSq_sub_add_four_mul_im
    (z alpha : ℂ) :
    Complex.normSq (z - starRingEnd ℂ alpha) =
      Complex.normSq (z - alpha) + 4 * z.im * alpha.im := by
  unfold Complex.normSq
  simp
  ring

/-- The one-root hyperbolic heat kernel factors into a Gaussian and the
standard exponential divided difference whose small-time coefficient is the
product of the two heights. -/
theorem upperHalfPlaneHyperbolicHeatIntegrand_eq_heightFactor
    (z alpha : ℂ) (tau : ℝ) :
    upperHalfPlaneHyperbolicHeatIntegrand z alpha tau =
      Real.exp (-(Complex.normSq (z - alpha) * tau)) *
        (tau⁻¹ *
          (1 - Real.exp (-(4 * z.im * alpha.im * tau)))) := by
  rw [upperHalfPlaneHyperbolicHeatIntegrand,
    normSq_sub_conj_eq_normSq_sub_add_four_mul_im]
  have hexp :
      Real.exp
          (-((Complex.normSq (z - alpha) + 4 * z.im * alpha.im) * tau)) =
        Real.exp (-(Complex.normSq (z - alpha) * tau)) *
          Real.exp (-(4 * z.im * alpha.im * tau)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- The exact one-root heat trace at proper time zero is four times the
product of the observation and root heights. -/
theorem tendsto_upperHalfPlaneHyperbolicHeatIntegrand_zero
    (z alpha : ℂ) :
    Tendsto (upperHalfPlaneHyperbolicHeatIntegrand z alpha)
      (nhdsWithin 0 (Ioi 0))
      (nhds (4 * z.im * alpha.im)) := by
  let q : ℝ := 4 * z.im * alpha.im
  have hinner : HasDerivAt (fun tau : ℝ ↦ -(q * tau)) (-q) 0 := by
    have hbase := ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul (-q))
    simpa [id_eq] using hbase
  have hexp : HasDerivAt (fun tau : ℝ ↦ Real.exp (-(q * tau))) (-q) 0 := by
    have hcomp := (Real.hasDerivAt_exp (-(q * 0))).comp 0 hinner
    simpa only [Function.comp_def, mul_zero, neg_zero, Real.exp_zero,
      one_mul] using hcomp
  have hquot : Tendsto
      (fun tau : ℝ ↦ tau⁻¹ * (1 - Real.exp (-(q * tau))))
      (nhdsWithin 0 (Ioi 0)) (nhds q) := by
    convert hexp.tendsto_slope_zero_right.neg using 1
    · funext tau
      simp only [zero_add, mul_zero, neg_zero, Real.exp_zero, smul_eq_mul]
      ring_nf
    · ring_nf
  have hgaussian : Tendsto
      (fun tau : ℝ ↦ Real.exp (-(Complex.normSq (z - alpha) * tau)))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hcontinuous : ContinuousAt
        (fun tau : ℝ ↦
          Real.exp (-(Complex.normSq (z - alpha) * tau))) 0 := by
      fun_prop
    simpa only [ContinuousWithinAt, mul_zero, neg_zero, Real.exp_zero] using
      hcontinuous.continuousWithinAt
  rw [show upperHalfPlaneHyperbolicHeatIntegrand z alpha =
      fun tau ↦
        Real.exp (-(Complex.normSq (z - alpha) * tau)) *
          (tau⁻¹ * (1 - Real.exp (-(q * tau)))) by
    funext tau
    simpa [q] using
      upperHalfPlaneHyperbolicHeatIntegrand_eq_heightFactor z alpha tau]
  simpa [q] using hgaussian.mul hquot

/-- At every positive proper time, one upper-root heat contribution is at
most four times the product of the observation and root heights. -/
theorem upperHalfPlaneHyperbolicHeatIntegrand_le_four_mul_im
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    {tau : ℝ} (htau : 0 < tau) :
    upperHalfPlaneHyperbolicHeatIntegrand z alpha tau ≤
      4 * z.im * alpha.im := by
  rw [upperHalfPlaneHyperbolicHeatIntegrand_eq_heightFactor]
  let q : ℝ := 4 * z.im * alpha.im
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqt : 0 ≤ q * tau := mul_nonneg hq htau.le
  have hexpLe : Real.exp (-(q * tau)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr hqt
  have hquotNonneg :
      0 ≤ tau⁻¹ * (1 - Real.exp (-(q * tau))) :=
    mul_nonneg (inv_nonneg.mpr htau.le) (sub_nonneg.mpr hexpLe)
  have hgaussianLe :
      Real.exp (-(Complex.normSq (z - alpha) * tau)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr
      (mul_nonneg (Complex.normSq_nonneg _) htau.le)
  have honeSub : 1 - Real.exp (-(q * tau)) ≤ q * tau := by
    linarith [Real.one_sub_le_exp_neg (q * tau)]
  have hquot : tau⁻¹ * (1 - Real.exp (-(q * tau))) ≤ q := by
    calc
      tau⁻¹ * (1 - Real.exp (-(q * tau))) ≤
          tau⁻¹ * (q * tau) :=
        mul_le_mul_of_nonneg_left honeSub (inv_nonneg.mpr htau.le)
      _ = q := by field_simp
  change Real.exp (-(Complex.normSq (z - alpha) * tau)) *
      (tau⁻¹ * (1 - Real.exp (-(q * tau)))) ≤ q
  exact (mul_le_of_le_one_left hquotNonneg hgaussianLe).trans hquot

/-- The multiplicity-counted total height of a finite upper divisor. -/
def finiteUpperHeightMass (upper : Multiset ℂ) : ℝ :=
  (upper.map Complex.im).sum

/-- At each finite stage, the proper-time-zero heat trace is exactly four
times the observation height times the total upper-root height. -/
theorem tendsto_finiteUpperHyperbolicHeatSum_zero
    (z : ℂ) (upper : Multiset ℂ) :
    Tendsto (finiteUpperHyperbolicHeatSum z upper)
      (nhdsWithin 0 (Ioi 0))
      (nhds (4 * z.im * finiteUpperHeightMass upper)) := by
  induction upper using Multiset.induction_on with
  | empty =>
      simp only [finiteUpperHeightMass, Multiset.map_zero,
        Multiset.sum_zero, mul_zero]
      exact tendsto_const_nhds
  | @cons alpha upper ih =>
      have hsum : finiteUpperHyperbolicHeatSum z (alpha ::ₘ upper) =
          fun tau ↦ upperHalfPlaneHyperbolicHeatIntegrand z alpha tau +
            finiteUpperHyperbolicHeatSum z upper tau := by
        funext tau
        simp [finiteUpperHyperbolicHeatSum]
      rw [hsum]
      have hadd :=
        (tendsto_upperHalfPlaneHyperbolicHeatIntegrand_zero z alpha).add ih
      convert hadd using 1
      simp only [finiteUpperHeightMass, Multiset.map_cons,
        Multiset.sum_cons]
      ring_nf

/-- A multiset of upper-half-plane points has nonnegative total height. -/
theorem finiteUpperHeightMass_nonneg
    {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im) :
    0 ≤ finiteUpperHeightMass upper := by
  apply Multiset.sum_nonneg
  intro y hy
  obtain ⟨alpha, halphaMem, rfl⟩ := Multiset.mem_map.mp hy
  exact (halpha alpha halphaMem).le

/-- The full fixed-time heat of a finite upper divisor is bounded by four
times the observation height times the divisor's total height. -/
theorem finiteUpperHyperbolicHeatSum_le_four_mul_im_mul_height
    {z : ℂ} (hz : 0 < z.im) {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    {tau : ℝ} (htau : 0 < tau) :
    finiteUpperHyperbolicHeatSum z upper tau ≤
      4 * z.im * finiteUpperHeightMass upper := by
  induction upper using Multiset.induction_on with
  | empty => simp [finiteUpperHyperbolicHeatSum, finiteUpperHeightMass]
  | @cons alpha upper ih =>
      have halphaHead : 0 < alpha.im := halpha alpha (by simp)
      have halphaTail : ∀ beta ∈ upper, 0 < beta.im := by
        intro beta hbeta
        exact halpha beta (by simp [hbeta])
      rw [finiteUpperHyperbolicHeatSum, finiteUpperHeightMass,
        Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_cons, Multiset.sum_cons]
      calc
        upperHalfPlaneHyperbolicHeatIntegrand z alpha tau +
              (upper.map fun beta ↦
                upperHalfPlaneHyperbolicHeatIntegrand z beta tau).sum ≤
            4 * z.im * alpha.im +
              4 * z.im * (upper.map Complex.im).sum :=
          add_le_add
            (upperHalfPlaneHyperbolicHeatIntegrand_le_four_mul_im
              hz halphaHead htau)
            (ih halphaTail)
        _ = 4 * z.im * (alpha.im + (upper.map Complex.im).sum) := by
          ring

/-- Before any positive time `a`, a finite upper divisor carries at most
`a` times four times the observation height times its total upper height. -/
theorem upperHalfPlaneHyperbolicHeatAction_le_time_mul_height
    {z : ℂ} (hz : 0 < z.im) {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    {c a : ℝ} (hc : 0 < c) (hca : c ≤ a) :
    upperHalfPlaneHyperbolicHeatAction z upper (c, a) ≤
      a * (4 * z.im * finiteUpperHeightMass upper) := by
  rw [upperHalfPlaneHyperbolicHeatAction_eq_intervalIntegral
    z upper hc hca]
  let C : ℝ := 4 * z.im * finiteUpperHeightMass upper
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) hz.le)
      (finiteUpperHeightMass_nonneg halpha)
  calc
    (∫ tau in c..a, finiteUpperHyperbolicHeatSum z upper tau) ≤
        ∫ _tau in c..a, C := by
      apply intervalIntegral.integral_mono_on hca
      · exact intervalIntegrable_finiteUpperHyperbolicHeatSum
          z upper hc hca
      · exact intervalIntegrable_const
      · intro tau htau
        exact finiteUpperHyperbolicHeatSum_le_four_mul_im_mul_height
          hz halpha (hc.trans_le htau.1)
    _ = (a - c) * C := by simp
    _ ≤ a * C := by
      exact mul_le_mul_of_nonneg_right (sub_le_self a hc.le) hC

/-- The total upper-root height of a real polynomial, with algebraic
multiplicity. -/
def realPolynomialUpperHeightMass (A : ℝ[X]) : ℝ :=
  finiteUpperHeightMass (realPolynomialUpperRootMultiset A)

/-- Under failure of RH, the same canonical sequence must satisfy a concrete
small-time height obstruction.  At every scale `a`, its eventual upper-root
height is large enough to dominate the fixed Hardy mass not already present
in a suitable compact spectral-xi action, up to arbitrary error. -/
theorem exists_canonicalFiniteHardyFrontier_smallTimeHeightObstruction_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      riemannXiSpectral z ≠ 0 ∧ ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
        ∀ (a error : ℝ), 0 < a → 0 < error →
          ∃ T : ℝ, a ≤ T ∧
            ∀ᶠ n in atTop,
              (-2 * Real.log (pairHyperbolicThreshold eta z.im) -
                  (∫ tau in a..T,
                    riemannXiUpperHyperbolicHeatSum z tau) - error) /
                    (4 * a * z.im) <
                realPolynomialUpperHeightMass (B n) := by
  obtain ⟨eta, heta, z, hz, hxi, B, hlimit, hfrontier, _hheat,
      hpositive, _hmass, _hcompact, _hlarge, hsmall⟩ :=
    exists_canonicalFiniteHardyFrontier_smallTimeEscape_of_not_rh hRH
  refine ⟨eta, heta, z, hz, hxi, B, hlimit, hfrontier, hpositive, ?_⟩
  intro a error ha herror
  obtain ⟨T, haT, hconcentrate⟩ := hsmall a error ha herror
  refine ⟨T, haT, ?_⟩
  filter_upwards [hconcentrate] with n hn
  obtain ⟨c, hc, hca, hn⟩ := hn
  have hraw := hn.trans_le
    (upperHalfPlaneHyperbolicHeatAction_le_time_mul_height
      hz (realPolynomialUpperRootMultiset_im_pos (B n)) hc hca.le)
  apply (div_lt_iff₀ (by positivity : 0 < 4 * a * z.im)).2
  calc
    -2 * Real.log (pairHyperbolicThreshold eta z.im) -
          (∫ tau in a..T, riemannXiUpperHyperbolicHeatSum z tau) - error <
        a * (4 * z.im * realPolynomialUpperHeightMass (B n)) := hraw
    _ = realPolynomialUpperHeightMass (B n) * (4 * a * z.im) := by ring

end

end RiemannGaussian

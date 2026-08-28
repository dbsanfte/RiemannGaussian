import RiemannGaussian.RiemannXiSuzukiWeilSafeLine

/-!
# Prime-series evaluation on the Suzuki--Weil safe line

This file applies the proved safe-line Fourier inversion formula to the
absolutely convergent von Mangoldt Dirichlet series on `Re s = 3/2`.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal FourierTransform Interval LSeries.notation Topology lp

namespace RiemannGaussian

noncomputable section

/-- One safe-line von Mangoldt term integrates to `2π` times the corresponding
positive- and negative-logarithm Suzuki test samples. -/
theorem integral_suzukiWeilSafeLineWeight_mul_vonMangoldtTerm
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) (n : ℕ) :
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        LSeries.term
          (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
          (3 / 2 + Complex.I * (r : ℂ)) n) =
      ((2 * Real.pi : ℝ) : ℂ) *
        (suzukiWeilPositivePrimeSample t z n +
          suzukiWeilNegativePrimeSample t z n) := by
  by_cases hn : n = 0
  · subst n
    simp [suzukiWeilPositivePrimeSample_zero ht,
      suzukiWeilNegativePrimeSample_eq_zero ht]
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  let C : ℝ := ArithmeticFunction.vonMangoldt n *
    Real.exp (-(3 / 2 : ℝ) * Real.log n)
  rw [integral_congr_ae (Filter.Eventually.of_forall fun r ↦ by
    rw [vonMangoldt_LSeriesTerm_safeLine hn])]
  change
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        ((C : ℂ) *
          Complex.exp (-Complex.I * (r : ℂ) * Real.log n))) = _
  rw [show (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        ((C : ℂ) *
          Complex.exp (-Complex.I * (r : ℂ) * Real.log n))) =
      fun r : ℝ ↦ (C : ℂ) *
        (suzukiWeilSafeLineSpectralWeight t z r *
          Complex.exp
            (Complex.I * (r : ℂ) * ((-Real.log n : ℝ) : ℂ))) by
    funext r
    push_cast
    ring_nf]
  rw [integral_const_mul,
    integral_suzukiWeilSafeLineSpectralWeight_mul_cexp
      ht hz (-Real.log n)]
  have hInvSqrt :
      Real.exp (-(1 / 2 : ℝ) * Real.log n) =
        1 / Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnpos]
    rw [eq_div_iff (Real.exp_ne_zero _), ← Real.exp_add]
    simp only [Real.exp_eq_one_iff]
    ring
  have hscale :
      Real.exp (-(3 / 2 : ℝ) * Real.log n) *
          Real.exp (Real.log n) =
        1 / Real.sqrt n := by
    rw [← Real.exp_add]
    rw [show -(3 / 2 : ℝ) * Real.log n + Real.log n =
      -(1 / 2 : ℝ) * Real.log n by ring,
      hInvSqrt]
  unfold C suzukiWeilSymmetricSafeLineTest
    suzukiWeilPositivePrimeSample suzukiWeilNegativePrimeSample
    suzukiWeilPrimeWeight
  rw [neg_neg]
  calc
    (((ArithmeticFunction.vonMangoldt n *
          Real.exp (-(3 / 2 : ℝ) * Real.log n) : ℝ) : ℂ) *
        (((2 * Real.pi : ℝ) : ℂ) *
          (((Real.exp (Real.log n) : ℝ) : ℂ) *
            (suzukiWeilTest t z (-Real.log n) +
              suzukiWeilTest t z (Real.log n))))) =
      ((2 * Real.pi : ℝ) : ℂ) *
        (((ArithmeticFunction.vonMangoldt n *
          (Real.exp (-(3 / 2 : ℝ) * Real.log n) *
            Real.exp (Real.log n)) : ℝ) : ℂ) *
          (suzukiWeilTest t z (Real.log n) +
            suzukiWeilTest t z (-Real.log n))) := by
      push_cast
      ring
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        (((ArithmeticFunction.vonMangoldt n *
          (1 / Real.sqrt n) : ℝ) : ℂ) *
          (suzukiWeilTest t z (Real.log n) +
            suzukiWeilTest t z (-Real.log n))) := by rw [hscale]
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
            suzukiWeilTest t z (Real.log n) +
          ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
            suzukiWeilTest t z (-Real.log n)) := by
      push_cast
      ring

/-- Every individual safe-line von Mangoldt term is absolutely integrable
against the reflected Suzuki weight. -/
theorem integrable_suzukiWeilSafeLineWeight_mul_vonMangoldtTerm
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) (n : ℕ) :
    Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        LSeries.term
          (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
          (3 / 2 + Complex.I * (r : ℂ)) n) := by
  by_cases hn : n = 0
  · subst n
    simp
  let C : ℂ := ArithmeticFunction.vonMangoldt n *
    Real.exp (-(3 / 2 : ℝ) * Real.log n)
  have hbase := integrable_suzukiWeilSafeLineSpectralWeight t hz
  have hscaled : Integrable (fun r : ℝ ↦ C *
      (suzukiWeilSafeLineSpectralWeight t z r *
        Complex.exp (-Complex.I * (r : ℂ) * Real.log n))) :=
    ((hbase.mul_bdd
      (show AEStronglyMeasurable (fun r : ℝ ↦
        Complex.exp (-Complex.I * (r : ℂ) * Real.log n))
        volume from (by fun_prop : Continuous (fun r : ℝ ↦
          Complex.exp (-Complex.I * (r : ℂ) * Real.log n))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun r ↦ by
        show ‖Complex.exp (-Complex.I * (r : ℂ) * Real.log n)‖ ≤
          (1 : ℝ)
        rw [Complex.norm_exp]
        rw [show
          (-Complex.I * (r : ℂ) * ((Real.log n : ℝ) : ℂ)).re = 0 by
            simp only [mul_re, neg_re, I_re, ofReal_re, neg_im, I_im,
              ofReal_im]
            ring]
        simp)).const_mul C)
  exact hscaled.congr (Filter.Eventually.of_forall fun r ↦ by
    dsimp only
    rw [vonMangoldt_LSeriesTerm_safeLine hn]
    unfold C
    push_cast
    ring)

/-- The absolute integrals of the reflected safe-line Dirichlet terms form a
summable series.  This is the precise Fubini hypothesis used below. -/
theorem summable_integral_norm_suzukiWeilSafeLineWeight_mul_vonMangoldtTerm
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) :
    Summable (fun n : ℕ ↦ ∫ r : ℝ,
      ‖suzukiWeilSafeLineSpectralWeight t z r *
        LSeries.term
          (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
          (3 / 2 + Complex.I * (r : ℂ)) n‖) := by
  have hL := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (3 / 2 : ℂ)) (by norm_num)
  have hW := integrable_suzukiWeilSafeLineSpectralWeight t hz
  let A : ℝ := ∫ r : ℝ, ‖suzukiWeilSafeLineSpectralWeight t z r‖
  have hsummable : Summable (fun n : ℕ ↦ A *
      ‖LSeries.term
        (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
        (3 / 2 : ℂ) n‖) := hL.norm.mul_left A
  refine hsummable.congr fun n ↦ ?_
  rw [show A = ∫ r : ℝ,
      ‖suzukiWeilSafeLineSpectralWeight t z r‖ by rfl]
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r ↦ by
    dsimp only
    rw [norm_mul, norm_vonMangoldt_LSeriesTerm_safeLine]

/-- The complete von Mangoldt `L`-series on `Re s = 3/2` is absolutely
integrable against the reflected Suzuki weight. -/
theorem integrable_suzukiWeilSafeLineWeight_mul_vonMangoldtLSeries
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) :
    Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        LSeries
          (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
          (3 / 2 + Complex.I * (r : ℂ))) := by
  let F := fun n : ℕ ↦ fun r : ℝ ↦
    suzukiWeilSafeLineSpectralWeight t z r *
      LSeries.term
        (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
        (3 / 2 + Complex.I * (r : ℂ)) n
  let C : ℝ := ∑' n : ℕ,
    ‖LSeries.term
      (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
      (3 / 2 : ℂ) n‖
  have hL := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (3 / 2 : ℂ)) (by norm_num)
  have hLnorm : Summable (fun n : ℕ ↦
      ‖LSeries.term
        (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
        (3 / 2 : ℂ) n‖) := hL.norm
  have hFint : ∀ n : ℕ, Integrable (F n) := by
    intro n
    exact integrable_suzukiWeilSafeLineWeight_mul_vonMangoldtTerm
      t hz n
  have hmajorant : Integrable (fun r : ℝ ↦
      ‖suzukiWeilSafeLineSpectralWeight t z r‖ * C) :=
    (integrable_suzukiWeilSafeLineSpectralWeight t hz).norm.mul_const C
  have htsum : Integrable (fun r : ℝ ↦ ∑' n : ℕ, F n r) := by
    refine hmajorant.mono'
      (AEStronglyMeasurable.tsum fun n ↦ (hFint n).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun r ↦ by
      have hsumNorm : Summable (fun n : ℕ ↦ ‖F n r‖) := by
        refine hLnorm.mul_left
          ‖suzukiWeilSafeLineSpectralWeight t z r‖ |>.congr ?_
        intro n
        unfold F
        rw [norm_mul, norm_vonMangoldt_LSeriesTerm_safeLine]
      calc
        ‖∑' n : ℕ, F n r‖ ≤ ∑' n : ℕ, ‖F n r‖ :=
          norm_tsum_le_tsum_norm hsumNorm
        _ = ‖suzukiWeilSafeLineSpectralWeight t z r‖ * C := by
          unfold F C
          simp_rw [norm_mul, norm_vonMangoldt_LSeriesTerm_safeLine]
          exact tsum_mul_left
  exact htsum.congr (Filter.Eventually.of_forall fun r ↦ by
    unfold F LSeries
    exact tsum_mul_left)

/-- Termwise integration of the complete von Mangoldt series recovers
exactly `2π` times both literal Suzuki prime sums. -/
theorem integral_suzukiWeilSafeLineWeight_mul_vonMangoldtLSeries
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) :
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        LSeries
          (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
          (3 / 2 + Complex.I * (r : ℂ))) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((∑' n : ℕ, suzukiWeilPositivePrimeSample t z n) +
          ∑' n : ℕ, suzukiWeilNegativePrimeSample t z n) := by
  let F := fun n : ℕ ↦ fun r : ℝ ↦
    suzukiWeilSafeLineSpectralWeight t z r *
      LSeries.term
        (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
        (3 / 2 + Complex.I * (r : ℂ)) n
  have hFint : ∀ n : ℕ, Integrable (F n) := by
    intro n
    exact integrable_suzukiWeilSafeLineWeight_mul_vonMangoldtTerm
      t hz n
  have hFnorm : Summable (fun n : ℕ ↦ ∫ r : ℝ, ‖F n r‖) := by
    simpa only [F] using
      summable_integral_norm_suzukiWeilSafeLineWeight_mul_vonMangoldtTerm
        t hz
  have hinterchange :
      (∑' n : ℕ, ∫ r : ℝ, F n r) =
        ∫ r : ℝ, ∑' n : ℕ, F n r :=
    integral_tsum_of_summable_integral_norm hFint hFnorm
  have hzSafe : z ∈ suzukiXiSafeUpperHalfPlane := by
    change (1 / 2 : ℝ) < z.im
    linarith
  calc
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        LSeries
          (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
          (3 / 2 + Complex.I * (r : ℂ))) =
        ∫ r : ℝ, ∑' n : ℕ, F n r := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun r ↦ by
        unfold F LSeries
        exact tsum_mul_left.symm
    _ = ∑' n : ℕ, ∫ r : ℝ, F n r := hinterchange.symm
    _ = ∑' n : ℕ,
        ((2 * Real.pi : ℝ) : ℂ) *
          (suzukiWeilPositivePrimeSample t z n +
            suzukiWeilNegativePrimeSample t z n) := by
      apply tsum_congr
      intro n
      unfold F
      exact integral_suzukiWeilSafeLineWeight_mul_vonMangoldtTerm
        ht hz n
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        (∑' n : ℕ,
          (suzukiWeilPositivePrimeSample t z n +
            suzukiWeilNegativePrimeSample t z n)) := by
      rw [tsum_mul_left]
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        ((∑' n : ℕ, suzukiWeilPositivePrimeSample t z n) +
          ∑' n : ℕ, suzukiWeilNegativePrimeSample t z n) := by
      rw [(summable_suzukiWeilPositivePrimeSample ht hzSafe).tsum_add
        (summable_suzukiWeilNegativePrimeSample ht z)]

/-- The safe-line negative logarithmic derivative of zeta is absolutely
integrable against the reflected Suzuki weight. -/
theorem integrable_suzukiWeilSafeLineWeight_mul_negLogDeriv_riemannZeta
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) :
    Integrable (fun r : ℝ ↦
      suzukiWeilSafeLineSpectralWeight t z r *
        (-deriv riemannZeta
            (3 / 2 + Complex.I * (r : ℂ)) /
          riemannZeta (3 / 2 + Complex.I * (r : ℂ)))) := by
  refine (integrable_suzukiWeilSafeLineWeight_mul_vonMangoldtLSeries
    t hz).congr (Filter.Eventually.of_forall fun r ↦ ?_)
  dsimp only
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (by norm_num)]

/-- The prime part of the horizontal Suzuki contour is now completely
evaluated from the zeta Dirichlet series. -/
theorem integral_suzukiWeilSafeLineWeight_mul_negLogDeriv_riemannZeta
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.im) :
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        (-deriv riemannZeta
            (3 / 2 + Complex.I * (r : ℂ)) /
          riemannZeta (3 / 2 + Complex.I * (r : ℂ)))) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((∑' n : ℕ, suzukiWeilPositivePrimeSample t z n) +
          ∑' n : ℕ, suzukiWeilNegativePrimeSample t z n) := by
  calc
    (∫ r : ℝ,
      suzukiWeilSafeLineSpectralWeight t z r *
        (-deriv riemannZeta
            (3 / 2 + Complex.I * (r : ℂ)) /
          riemannZeta (3 / 2 + Complex.I * (r : ℂ)))) =
        ∫ r : ℝ,
          suzukiWeilSafeLineSpectralWeight t z r *
            LSeries
              (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
              (3 / 2 + Complex.I * (r : ℂ)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun r ↦ by
        dsimp only
        rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
          (by norm_num)]
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        ((∑' n : ℕ, suzukiWeilPositivePrimeSample t z n) +
          ∑' n : ℕ, suzukiWeilNegativePrimeSample t z n) :=
      integral_suzukiWeilSafeLineWeight_mul_vonMangoldtLSeries ht hz

end

end RiemannGaussian

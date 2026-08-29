import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEta

/-!
# A convergent eta-series formula for the positive-strip zeta logarithmic derivative

This module differentiates the paired eta series on `0 < re s`. The explicit
derivative summand is an odd-even pair weighted by logarithms. Rather than
assuming its convergence, the proof reuses the locally uniform summable bound
for the holomorphic eta summands and applies the Cauchy derivative theorem for
locally uniform series. Lean thereby proves that the derivative terms sum to
the genuine derivative of `pairedEtaCore` and are summable.

After differentiating the elementary eta factor, the terminal theorem gives
an exact convergent arithmetic quotient for `logDeriv riemannZeta` throughout
`1 / 2 < re s < 1`, away from the zeta divisor. The nonvanishing hypothesis is
kept explicitly: the construction represents the logarithmic derivative but
does not totalize away or discard its zero singularities.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The explicit derivative of one odd-even pair in the eta series. -/
def pairedEtaCoreDerivativeSummand (s : ℂ) (n : ℕ) : ℂ :=
  -Complex.log ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) *
      ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) +
    Complex.log ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) *
      ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s)

/-- Termwise differentiation of an odd-even eta pair. -/
lemma hasDerivAt_pairedEtaCoreSummand (s : ℂ) (n : ℕ) :
    HasDerivAt (fun w : ℂ => pairedEtaCoreSummand w n)
      (pairedEtaCoreDerivativeSummand s n) s := by
  unfold pairedEtaCoreSummand pairedEtaCoreDerivativeSummand
  have hleft := (hasDerivAt_neg' s).const_cpow
    (c := ((((2 * n + 1 : ℕ) : ℝ) : ℂ)))
    (Or.inl (by exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)))
  have hright := (hasDerivAt_neg' s).const_cpow
    (c := ((((2 * n + 2 : ℕ) : ℝ) : ℂ)))
    (Or.inl (by exact_mod_cast (show 2 * n + 2 ≠ 0 by omega)))
  have h := hleft.sub hright
  have hcoeff :
      ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) *
            Complex.log ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) * (-1) -
          ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) *
            Complex.log ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) * (-1) =
        -Complex.log ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) *
            ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) +
          Complex.log ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) *
            ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
    ring
  rw [hcoeff] at h
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun w => rfl)

/-- The derivative of an eta pair is its explicit logarithmically weighted
pair. -/
lemma deriv_pairedEtaCoreSummand (s : ℂ) (n : ℕ) :
    deriv (fun w : ℂ => pairedEtaCoreSummand w n) s =
      pairedEtaCoreDerivativeSummand s n :=
  (hasDerivAt_pairedEtaCoreSummand s n).deriv

/-- On the full positive half-plane, the explicit derivative pairs sum to the
genuine derivative of the paired eta function. -/
theorem hasSum_pairedEtaCoreDerivativeSummand_deriv
    {s : ℂ} (hs : 0 < s.re) :
    HasSum (pairedEtaCoreDerivativeSummand s) (deriv pairedEtaCore s) := by
  let delta : ℝ := s.re / 2
  let radius : ℝ := s.re / 2
  let K : ℝ := ‖s‖ + radius
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbase : Summable
      (fun m : ℕ => ((((m : ℝ) + 1) ^ (delta + 1)))⁻¹) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 (delta + 1)).mpr (by linarith)
    apply h.congr
    intro m
    rw [abs_of_nonneg (by positivity)]
    simp only [one_div]
  have hodd : Summable
      (fun n : ℕ => ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹) := by
    simpa [Function.comp_def] using
      hbase.comp_injective (i := fun n : ℕ => 2 * n) (by
        intro n m h
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)
  have hmajor : Summable
      (fun n : ℕ => K *
        ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹) :=
    hodd.mul_left K
  have hterms (n : ℕ) :
      DifferentiableOn ℂ (fun w : ℂ => pairedEtaCoreSummand w n)
        (Metric.ball s radius) := by
    intro w hw
    exact (hasDerivAt_pairedEtaCoreSummand w n).differentiableAt.differentiableWithinAt
  have hbound (n : ℕ) (w : ℂ) (hw : w ∈ Metric.ball s radius) :
      ‖pairedEtaCoreSummand w n‖ ≤
        K * ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹ := by
    have hdist : dist w s < radius := by simpa [Metric.mem_ball] using hw
    have hreNorm : |w.re - s.re| ≤ dist w s := by
      calc
        |w.re - s.re| = |(w - s).re| := by simp
        _ ≤ ‖w - s‖ := Complex.abs_re_le_norm _
        _ = dist w s := by rw [dist_eq_norm]
    have hwre : delta < w.re := by
      dsimp [delta, radius] at *
      linarith [neg_le_abs (w.re - s.re)]
    have hwNorm : ‖w‖ ≤ K := by
      calc
        ‖w‖ ≤ ‖w - s‖ + ‖s‖ := by
          simpa only [sub_add_cancel] using norm_add_le (w - s) s
        _ = dist w s + ‖s‖ := by rw [dist_eq_norm]
        _ ≤ K := by dsimp [K]; linarith
    have hraw := norm_pairedEtaCoreSummand_le (s := w) (hdelta.trans hwre) n
    let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
    have ha1 : 1 ≤ a := by
      dsimp [a]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
    have ha0 : 0 ≤ a := zero_le_one.trans ha1
    have hpow : a ^ (-w.re - 1) ≤ a ^ (-delta - 1) :=
      Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
    rw [← Real.rpow_neg ha0, show -(w.re + 1) = -w.re - 1 by ring] at hraw
    rw [← Real.rpow_neg ha0, show -(delta + 1) = -delta - 1 by ring]
    calc
      ‖pairedEtaCoreSummand w n‖ ≤ ‖w‖ * a ^ (-w.re - 1) := by
        simpa [a] using hraw
      _ ≤ K * a ^ (-delta - 1) :=
        mul_le_mul hwNorm hpow (Real.rpow_nonneg ha0 _) hK
  have hsum := Complex.hasSum_deriv_of_summable_norm
    (F := fun n w => pairedEtaCoreSummand w n)
    hmajor hterms Metric.isOpen_ball hbound (Metric.mem_ball_self hradius)
  have hfun : (fun w : ℂ => ∑' n : ℕ, pairedEtaCoreSummand w n) =
      pairedEtaCore := by rfl
  rw [hfun] at hsum
  apply hsum.congr_fun
  intro n
  exact (deriv_pairedEtaCoreSummand s n).symm

/-- The paired eta derivative series is summable throughout `0 < re s`. -/
lemma summable_pairedEtaCoreDerivativeSummand
    {s : ℂ} (hs : 0 < s.re) :
    Summable (pairedEtaCoreDerivativeSummand s) :=
  (hasSum_pairedEtaCoreDerivativeSummand_deriv hs).summable

/-- The totalized logarithmic derivative of paired eta is its convergent
derivative series divided by paired eta. -/
theorem logDeriv_pairedEtaCore_eq_tsum
    {s : ℂ} (hs : 0 < s.re) :
    logDeriv pairedEtaCore s =
      (∑' n : ℕ, pairedEtaCoreDerivativeSummand s n) /
        pairedEtaCore s := by
  rw [logDeriv_apply,
    (hasSum_pairedEtaCoreDerivativeSummand_deriv hs).tsum_eq]

/-- The elementary factor relating paired eta to zeta. -/
def pairedEtaFactor (s : ℂ) : ℂ :=
  1 - 2 * (2 : ℂ) ^ (-s)

/-- The explicit totalized logarithmic derivative of the elementary eta
factor. -/
def pairedEtaFactorLogDerivative (s : ℂ) : ℂ :=
  (2 * Complex.log 2 * (2 : ℂ) ^ (-s)) / pairedEtaFactor s

/-- The derivative of the elementary eta factor. -/
lemma hasDerivAt_pairedEtaFactor (s : ℂ) :
    HasDerivAt pairedEtaFactor
      (2 * Complex.log 2 * (2 : ℂ) ^ (-s)) s := by
  have hpow := (hasDerivAt_neg' s).const_cpow (c := (2 : ℂ))
    (Or.inl (by norm_num))
  have h := (hasDerivAt_const s (1 : ℂ)).sub (hpow.const_mul 2)
  have hcoeff :
      0 - 2 * ((2 : ℂ) ^ (-s) * Complex.log 2 * (-1)) =
        2 * Complex.log 2 * (2 : ℂ) ^ (-s) := by ring
  rw [hcoeff] at h
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun w => by rfl)

/-- The totalized logarithmic derivative of the eta factor has its explicit
closed form. -/
lemma logDeriv_pairedEtaFactor (s : ℂ) :
    logDeriv pairedEtaFactor s = pairedEtaFactorLogDerivative s := by
  rw [logDeriv_apply, (hasDerivAt_pairedEtaFactor s).deriv]
  rfl

/-- Away from the zeta divisor in the positive critical half-strip, the eta
logarithmic derivative splits into its elementary factor and zeta parts. -/
theorem logDeriv_pairedEtaCore_eq_factor_add_riemannZeta
    {s : ℂ} (hlower : 1 / 2 < s.re) (hupper : s.re < 1)
    (hzeta : riemannZeta s ≠ 0) :
    logDeriv pairedEtaCore s =
      pairedEtaFactorLogDerivative s + logDeriv riemannZeta s := by
  have hsone : s ≠ 1 := by
    intro h
    subst s
    norm_num at hupper
  have hfactor : pairedEtaFactor s ≠ 0 := by
    exact pairedEtaFactor_ne_zero_of_re_lt_one hupper
  have hevent : pairedEtaCore =ᶠ[𝓝 s]
      fun w : ℂ => pairedEtaFactor w * riemannZeta w := by
    filter_upwards [
      (Complex.isOpen_re_gt 0).mem_nhds (show 0 < s.re by linarith),
      isOpen_compl_singleton.mem_nhds
        (show s ∈ ({1}ᶜ : Set ℂ) by simpa)] with w hwre hwone
    simpa [pairedEtaFactor] using
      pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
        hwre (by simpa using hwone)
  rw [(logDeriv_congr_nhds hevent).self_of_nhds]
  rw [logDeriv_mul s hfactor hzeta
    (hasDerivAt_pairedEtaFactor s).differentiableAt
    (differentiableAt_riemannZeta hsone)]
  rw [logDeriv_pairedEtaFactor]

/-- Throughout the positive critical half-strip away from the zeta divisor,
`zeta'/zeta` is the exact quotient of two convergent paired eta series minus
the explicit elementary-factor correction. -/
theorem logDeriv_riemannZeta_eq_pairedEtaArithmetic_of_half_lt_re_of_re_lt_one
    {s : ℂ} (hlower : 1 / 2 < s.re) (hupper : s.re < 1)
    (hzeta : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s =
      (∑' n : ℕ, pairedEtaCoreDerivativeSummand s n) /
          pairedEtaCore s -
        pairedEtaFactorLogDerivative s := by
  have h := logDeriv_pairedEtaCore_eq_factor_add_riemannZeta
    hlower hupper hzeta
  rw [logDeriv_pairedEtaCore_eq_tsum (by linarith)] at h
  linear_combination -h

end
end RiemannGaussian

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszEulerCutoff
import RiemannGaussian.ZetaMomentPoleJet
import RiemannGaussian.ZetaRieszFixedCofactor

/-!
# Cutoff-uniform factorial moments of the Euler correction

The original inverse-length normalization absorbs the linear physical-phase
cost. Cauchy estimates preserve an integrable majorant at every factorial
order, and the exact logarithm-marked polynomial filter has a geometric
allowance at every source scale below one. The prime universe and physical
cutoff are the original ones. Measurability and integrability are proved
before integrating any differentiated expression. This bounds the standalone
correction; it does not bound its mixed leading-response coupling.
-/

namespace RiemannGaussian.ZetaRieszEulerMoments
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open ZetaRieszEulerQuotient ZetaRieszEulerCorrectionEnergy
open ZetaRieszEulerCutoff

/-- The full correction is holomorphic in the arithmetic parameter where
every local denominator is uniformly separated from zero. -/
theorem analyticAt_actual_correctionProduct (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} (hs : 1 / 2 ≤ s.re) (xi : ℝ) :
    AnalyticAt ℂ (fun z => correctionProduct Q (zetaPrimeFeature z) (fun p => Real.log p) xi) s := by
  unfold correctionProduct
  apply Finset.analyticAt_fun_prod
  intro p hp
  have hf : AnalyticAt ℂ (fun z => zetaPrimeFeature z p) s := by
    have hd : Differentiable ℂ (fun z => zetaPrimeFeature z p) := by unfold zetaPrimeFeature; fun_prop
    exact hd.analyticAt s
  apply analyticAt_const.add
  unfold localCorrection
  exact ((hf.pow 2).mul analyticAt_const).div
    (analyticAt_const.sub (hf.mul analyticAt_const))
    (local_denominator_ne_zero (ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter hs (h16 p hp))
      (Complex.norm_exp_ofReal_mul_I _).le)

/-- The two physical phases are constant in the arithmetic parameter,
so the genuinely paired frequency quotient is holomorphic there as well. -/
theorem analyticAt_actual_shiftedCorrection_div (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} (hs : 1 / 2 ≤ s.re) (L xi : ℝ) :
    AnalyticAt ℂ (fun z =>
      shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) L xi / (xi : ℂ) ^ 2) s := by
  have hp := analyticAt_actual_correctionProduct Q h16 hs xi
  have hm := analyticAt_actual_correctionProduct Q h16 hs (-xi)
  have ha : AnalyticAt ℂ (fun z =>
      shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) L xi) s :=
    (analyticAt_const.mul (hp.sub analyticAt_const)).add
      (analyticAt_const.mul (hm.sub analyticAt_const))
  exact ha.div_const

/-- A pointwise integrable majorant retains the cutoff cosine and all
weighted prime cosines, suitable for uniform Cauchy estimates. -/
def phaseMajorant {ι : Type*} (Q : Finset ι) (q : ι → ℂ) (ell : ι → ℝ) (L xi : ℝ) : ℝ :=
  (evenCost Q q + 4 * expCost Q q) * phaseEnergy Q q ell xi +
    4 * expCost Q q * localMass Q q * ((1 - Real.cos ((2 * L) * xi)) / xi ^ 2)

/-- Monotonicity of square amplitudes controls their finite mass without
discarding the logarithmic labels. -/
theorem localMass_mono {ι : Type*} (Q : Finset ι) (q r : ι → ℂ)
    (hqr : ∀ p ∈ Q, ‖q p‖ ^ 2 ≤ ‖r p‖ ^ 2) : localMass Q q ≤ localMass Q r :=
  Finset.sum_le_sum hqr

/-- The exponential cost is monotone in the retained square amplitudes. -/
theorem expCost_mono {ι : Type*} (Q : Finset ι) (q r : ι → ℂ)
    (hqr : ∀ p ∈ Q, ‖q p‖ ^ 2 ≤ ‖r p‖ ^ 2) : expCost Q q ≤ expCost Q r := by
  unfold expCost
  exact add_le_add le_rfl (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (localMass_mono Q q r hqr) (by norm_num)))

/-- The complete even cost has the same amplitude monotonicity. -/
theorem evenCost_mono {ι : Type*} (Q : Finset ι) (q r : ι → ℂ)
    (hqr : ∀ p ∈ Q, ‖q p‖ ^ 2 ≤ ‖r p‖ ^ 2) : evenCost Q q ≤ evenCost Q r := by
  have h := mul_le_mul (localMass_mono Q q r hqr) (expCost_mono Q q r hqr)
    (expCost_nonneg Q q) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  unfold evenCost
  nlinarith

/-- Nonnegative cosine energies retain every logarithmic phase while
allowing a uniform half-plane amplitude majorant. -/
theorem phaseEnergy_mono {ι : Type*} (Q : Finset ι) (q r : ι → ℂ) (ell : ι → ℝ)
    (hqr : ∀ p ∈ Q, ‖q p‖ ^ 2 ≤ ‖r p‖ ^ 2) (xi : ℝ) :
    phaseEnergy Q q ell xi ≤ phaseEnergy Q r ell xi := by
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_right (hqr p hp)
    (div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (sq_nonneg _))

/-- The entire integrable majorant, including the odd cutoff coupling,
is monotone in the original prime-square amplitudes. -/
theorem phaseMajorant_mono {ι : Type*} (Q : Finset ι) (q r : ι → ℂ) (ell : ι → ℝ)
    (hqr : ∀ p ∈ Q, ‖q p‖ ^ 2 ≤ ‖r p‖ ^ 2) (L xi : ℝ) :
    phaseMajorant Q q ell L xi ≤ phaseMajorant Q r ell L xi := by
  have he := expCost_mono Q q r hqr
  have hm := localMass_mono Q q r hqr
  have hb := add_le_add (evenCost_mono Q q r hqr)
    (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 4))
  have hr0 : 0 ≤ localMass Q r := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq0 : 0 ≤ localMass Q q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc0 := expCost_nonneg Q r
  have hfirst := mul_le_mul hb (phaseEnergy_mono Q q r ell hqr xi)
    (phaseEnergy_nonneg Q q ell xi) (by unfold evenCost; positivity)
  have hsecond := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul he hm hq0 hc0) (show (0 : ℝ) ≤ 4 by norm_num))
    (div_nonneg (sub_nonneg.mpr (Real.cos_le_one ((2 * L) * xi))) (sq_nonneg xi))
  exact add_le_add hfirst (by convert hsecond using 1 <;> ring)

/-- One real slice of the arithmetic parameter bounds the correction
pointwise throughout the closed half-plane, uniformly in height. -/
theorem norm_actual_shiftedCorrection_le_majorant (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {sigma : ℝ} (hsigma : 1 / 2 ≤ sigma)
    {s : ℂ} (hs : sigma ≤ s.re) (L xi : ℝ) :
    ‖shiftedCorrection Q (zetaPrimeFeature s) (fun p => Real.log p) L xi / (xi : ℂ) ^ 2‖ ≤
      phaseMajorant Q (zetaPrimeFeature (sigma : ℂ)) (fun p => Real.log p) L xi := by
  apply (norm_shiftedCorrection_div_le_energy Q (zetaPrimeFeature s) (fun p => Real.log p)
    (fun p hp => ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter (hsigma.trans hs) (h16 p hp)) L xi).trans
  apply phaseMajorant_mono
  intro p _hp
  rw [norm_zetaPrimeFeature, norm_zetaPrimeFeature, Complex.ofReal_re]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (ZetaPrimeNonlinearHalfplane.expWeight_mono hs p) 2

/-- A closed Cauchy disc stays in its exact leftmost real half-plane. -/
theorem disc_re_lower_bound {s z : ℂ} {R : ℝ} (hz : z ∈ Metric.closedBall s R) :
    s.re - R ≤ z.re := by
  have hn : ‖z - s‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hr := (abs_le.mp ((Complex.abs_re_le_norm (z - s)).trans hn)).1
  simp only [Complex.sub_re] at hr
  linarith

/-- Every factorial moment of the physical-phase correction keeps the
same integrable majorant and exact Cauchy radius. No factorial loss or
prime-count factor is inserted by differentiation. -/
theorem norm_actual_shiftedCorrection_moment_le (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hhalf : 1 / 2 ≤ s.re - R) (L xi : ℝ) (n : ℕ) :
    ‖signedTaylorMoment n (fun z =>
      shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) L xi / (xi : ℂ) ^ 2) s‖ ≤
        phaseMajorant Q (zetaPrimeFeature ((s.re - R : ℝ) : ℂ))
          (fun p => Real.log p) L xi / R ^ n := by
  have ha : AnalyticOnNhd ℂ (fun z =>
      shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) L xi / (xi : ℂ) ^ 2)
        (Metric.closedBall s R) :=
    fun _ hz => analyticAt_actual_shiftedCorrection_div Q h16
      (hhalf.trans (disc_re_lower_bound hz)) L xi
  have hd : DiffContOnCl ℂ (fun z =>
      shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) L xi / (xi : ℂ) ^ 2)
        (Metric.ball s R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s hR.ne']
    exact ha.differentiableOn
  apply norm_signedTaylorMoment_le hR hd
  intro z hz
  exact norm_actual_shiftedCorrection_le_majorant Q h16 hhalf
    (disc_re_lower_bound (Metric.sphere_subset_closedBall hz)) L xi

/-- The finite rational-exponential correction is jointly measurable in
frequency and the arithmetic parameter, including its totalized algebraic
values away from the analytic domain used for Cauchy's formula. -/
theorem stronglyMeasurable_actual_shiftedCorrection_div (Q : Finset ℕ) (L : ℝ) :
    StronglyMeasurable (fun v : ℝ × ℂ =>
      shiftedCorrection Q (zetaPrimeFeature v.2) (fun p => Real.log p) L v.1 / (v.1 : ℂ) ^ 2) := by
  apply Measurable.stronglyMeasurable
  unfold shiftedCorrection correctionProduct localCorrection zetaPrimeFeature phase
  fun_prop

/-- Cauchy's exact circle formula preserves the sign and factorial
normalization of the actual moment coordinate. -/
theorem signedTaylorMoment_eq_circleIntegral {f : ℂ → ℂ} {s : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (Metric.ball s R)) (n : ℕ) :
    signedTaylorMoment n f s = ((-1 : ℂ) ^ n / (2 * Real.pi * Complex.I)) *
      (∮ z in C(s, R), (1 / (z - s) ^ (n + 1)) * f z) := by
  have hc := hf.circleIntegral_one_div_sub_center_pow_smul hR n
  simp only [smul_eq_mul] at hc
  rw [hc, signedTaylorMoment]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

/-- Measurability passes through the fixed Cauchy circle while retaining
the external frequency parameter. This does not assume an integral swap. -/
theorem stronglyMeasurable_parametric_circle (f : ℝ × ℂ → ℂ)
    (hf : StronglyMeasurable f) (s : ℂ) (R : ℝ) (n : ℕ) :
    StronglyMeasurable (fun xi : ℝ =>
      ∮ z in C(s, R), (1 / (z - s) ^ (n + 1)) * f (xi, z)) := by
  have hg : StronglyMeasurable (fun v : ℝ × ℝ =>
      deriv (circleMap s R) v.2 *
        ((1 / (circleMap s R v.2 - s) ^ (n + 1)) * f (v.1, circleMap s R v.2))) := by
    have hcomp := hf.measurable.comp (measurable_fst.prodMk
      ((measurable_circleMap s R).comp measurable_snd))
    apply Measurable.stronglyMeasurable
    simp only [deriv_circleMap]
    fun_prop
  simp only [circleIntegral, smul_eq_mul, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  exact hg.integral_prod_right'

/-- The Cauchy representation proves frequency measurability of every
actual factorial moment, before applying the integrable majorant. -/
theorem stronglyMeasurable_actual_shiftedCorrection_moment (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hhalf : 1 / 2 ≤ s.re - R) (L : ℝ) (n : ℕ) :
    StronglyMeasurable (fun xi : ℝ => signedTaylorMoment n (fun z =>
      shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) L xi / (xi : ℂ) ^ 2) s) := by
  have he (xi : ℝ) := signedTaylorMoment_eq_circleIntegral hR (f := fun z =>
    shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) L xi / (xi : ℂ) ^ 2)
    (s := s) (show DiffContOnCl ℂ _ (Metric.ball s R) from by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball s hR.ne']
      intro z hz
      exact (analyticAt_actual_shiftedCorrection_div Q h16
        (hhalf.trans (disc_re_lower_bound hz)) L xi).differentiableAt.differentiableWithinAt) n
  simp_rw [he]
  exact (stronglyMeasurable_parametric_circle _
    (stronglyMeasurable_actual_shiftedCorrection_div Q L) s R n).const_mul _

/-- The retained majorant has a genuine ordinary frequency integral. -/
theorem integrable_phaseMajorant {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (L : ℝ) :
    IntegrableOn (phaseMajorant Q q ell L) (Ioi 0) :=
  ((integrable_phaseEnergy Q q ell).const_mul _).add
    ((CosineHinge.integrable_one_sub_cos_div_sq (2 * L)).const_mul _)

/-- Differentiation in the arithmetic parameter preserves genuine
frequency integrability for every factorial order of the full correction. -/
theorem integrable_actual_shiftedCorrection_moment (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hhalf : 1 / 2 ≤ s.re - R) (L : ℝ) (n : ℕ) :
    IntegrableOn (fun xi : ℝ => signedTaylorMoment n (fun z =>
      shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) L xi / (xi : ℂ) ^ 2) s)
        (Ioi 0) := by
  apply ((integrable_phaseMajorant Q (zetaPrimeFeature ((s.re - R : ℝ) : ℂ))
    (fun p => Real.log p) L).div_const (R ^ n)).mono'
  · exact (stronglyMeasurable_actual_shiftedCorrection_moment Q h16 hR hhalf L n).aestronglyMeasurable
  · filter_upwards [] with xi
    exact norm_actual_shiftedCorrection_moment_le Q h16 hR hhalf L xi n

/-- The Cauchy majorant integrates to the full linear-shift budget,
with the weighted logarithmic frequencies still explicit. -/
theorem integral_phaseMajorant {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (L : ℝ) :
    (∫ xi : ℝ in Ioi 0, phaseMajorant Q q ell L xi) =
      (evenCost Q q + 4 * expCost Q q) *
        (Real.pi / 2 * ∑ p ∈ Q, ‖q p‖ ^ 2 * |ell p|) +
          4 * Real.pi * expCost Q q * localMass Q q * |L| := by
  unfold phaseMajorant
  rw [integral_add ((integrable_phaseEnergy Q q ell).const_mul _)
    ((CosineHinge.integrable_one_sub_cos_div_sq (2 * L)).const_mul _),
    integral_const_mul, integral_const_mul, integral_phaseEnergy,
    CosineHinge.integral_one_sub_cos_div_sq, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring

/-- Every actual factorial moment has an ordinary integrated bound by
the same square-log tail, divided only by its exact Cauchy-radius power. -/
theorem integral_norm_actual_shiftedCorrection_moment_le (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hhalf : 1 / 2 < s.re - R) (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p) (L : ℝ) (n : ℕ) :
    (∫ xi : ℝ in Ioi 0, ‖signedTaylorMoment n (fun z =>
      shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) L xi / (xi : ℂ) ^ 2) s‖) ≤
        (phaseTailCost (s.re - R) L * ZetaPrimeNonlinearTail.squareLogTail (s.re - R) K) /
          R ^ n := by
  calc
    _ ≤ ∫ xi : ℝ in Ioi 0,
        phaseMajorant Q (zetaPrimeFeature ((s.re - R : ℝ) : ℂ))
          (fun p => Real.log p) L xi / R ^ n :=
      integral_mono_ae (integrable_actual_shiftedCorrection_moment Q h16 hR hhalf.le L n).norm
        ((integrable_phaseMajorant Q _ _ L).div_const _)
        (Filter.Eventually.of_forall (fun xi =>
          norm_actual_shiftedCorrection_moment_le Q h16 hR hhalf.le L xi n))
    _ ≤ _ := by
      rw [integral_div, integral_phaseMajorant]
      apply div_le_div_of_nonneg_right _ (pow_nonneg hR.le n)
      exact actual_phaseBudget_le_tail Q h16 hhalf (by simp) K hK L

/-- The carrier's existing inverse-length normalization absorbs the
linear physical-phase cost uniformly over all lengths above a positive base. -/
theorem phaseTailCost_div_le (sigma : ℝ) {a L : ℝ} (ha : 0 < a) (hL : a ≤ L) :
    phaseTailCost sigma L / L ≤ phaseTailCost sigma a / a := by
  have hL0 : 0 < L := ha.trans_le hL
  have hM : 0 ≤ massCeiling sigma := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hB : 0 ≤ (32 + 64 * massCeiling sigma * (2 + Real.exp (8 * massCeiling sigma)) +
      4 * (2 + Real.exp (8 * massCeiling sigma))) * (Real.pi / 2) := by positivity
  apply (div_le_div_iff₀ hL0 ha).mpr
  unfold phaseTailCost
  rw [abs_of_pos hL0, abs_of_pos ha]
  have hb := mul_le_mul_of_nonneg_left hL hB
  convert (add_le_add hb (le_refl
    (4 * Real.pi * (2 + Real.exp (8 * massCeiling sigma)) * L * a / Real.log 16))) using 1 <;> ring

/-- Every normalized actual factorial moment is uniformly controlled in
the physical cutoff. Its only order cost is the original Cauchy power. -/
theorem integral_norm_normalized_actual_moment_le (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hhalf : 1 / 2 < s.re - R) (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p)
    {a L : ℝ} (ha : 0 < a) (hL : a ≤ L) (n : ℕ) :
    (∫ xi : ℝ in Ioi 0, ‖signedTaylorMoment n (fun z =>
      shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) L xi / (xi : ℂ) ^ 2) s‖ / L) ≤
        ((phaseTailCost (s.re - R) a / a) *
          ZetaPrimeNonlinearTail.squareLogTail (s.re - R) K) / R ^ n := by
  rw [integral_div]
  apply (div_le_div_of_nonneg_right
    (integral_norm_actual_shiftedCorrection_moment_le Q h16 hR hhalf K hK L n)
    (ha.trans_le hL).le).trans
  calc
    _ = ((phaseTailCost (s.re - R) L / L) *
        ZetaPrimeNonlinearTail.squareLogTail (s.re - R) K) / R ^ n := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (phaseTailCost_div_le (s.re - R) ha hL)
        (ZetaPrimeNonlinearTail.squareLogTail_nonneg hhalf K)) (pow_nonneg hR.le n)

/-- The arithmetic budget after the original inverse-length
normalization; it is independent of the growing physical cutoff. -/
def normalizedTailBudget (sigma a : ℝ) (K : ℕ) : ℝ :=
  (phaseTailCost sigma a / a) * ZetaPrimeNonlinearTail.squareLogTail sigma K

/-- The cutoff-normalized budget is nonnegative in its analytic domain. -/
theorem normalizedTailBudget_nonneg {sigma a : ℝ} (hsigma : 1 / 2 < sigma)
    (ha : 0 < a) (K : ℕ) : 0 ≤ normalizedTailBudget sigma a K := by
  have hM : 0 ≤ massCeiling sigma := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hcost : 0 ≤ phaseTailCost sigma a := by
    unfold phaseTailCost
    have hlog : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
    positivity
  exact mul_nonneg (div_nonneg hcost ha.le) (ZetaPrimeNonlinearTail.squareLogTail_nonneg hsigma K)

/-- The full correction moment uses the original negative prime-character
orientation and the original positive physical normalization. -/
def momentResponse (Q : Finset ℕ) (s : ℂ) (L : ℝ) (n : ℕ) : ℂ :=
  (∫ xi : ℝ in Ioi 0, signedTaylorMoment n (fun z =>
    shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) (-L) xi / (xi : ℂ) ^ 2) s) /
      (L : ℂ)

/-- Reversing the reciprocal-frequency orientation leaves its certified
allowance unchanged while keeping the underlying phases distinct. -/
theorem phaseTailCost_neg (sigma L : ℝ) : phaseTailCost sigma (-L) = phaseTailCost sigma L := by
  simp only [phaseTailCost, abs_neg]

/-- The literal frequency orientation and every factorial moment have
one cutoff-uniform arithmetic bound. -/
theorem norm_momentResponse_le (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 / 2 < s.re - R)
    (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p) {a L : ℝ} (ha : 0 < a) (hL : a ≤ L) (n : ℕ) :
    ‖momentResponse Q s L n‖ ≤ normalizedTailBudget (s.re - R) a K / R ^ n := by
  have hL0 : 0 < L := ha.trans_le hL
  unfold momentResponse
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0]
  have hi := integral_norm_actual_shiftedCorrection_moment_le Q h16 hR hhalf K hK (-L) n
  rw [phaseTailCost_neg] at hi
  apply (div_le_div_of_nonneg_right ((norm_integral_le_integral_norm _).trans hi) hL0.le).trans
  calc
    _ = ((phaseTailCost (s.re - R) L / L) *
        ZetaPrimeNonlinearTail.squareLogTail (s.re - R) K) / R ^ n := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (phaseTailCost_div_le (s.re - R) ha hL)
        (ZetaPrimeNonlinearTail.squareLogTail_nonneg hhalf K)) (pow_nonneg hR.le n)

/-- The fixed filter pays only its literal coefficients and factorial
offsets at the selected Cauchy radius. -/
def filterRadiusCost (P : Polynomial ℂ) (R : ℝ) : ℝ :=
  ∑ k ∈ P.support, ‖P.coeff k‖ * ((k : ℝ) + 1) / R ^ k

/-- A Cauchy moment bound passes through the complete logarithm-marked
polynomial filter, preserving the exact offset and its linear order cost. -/
theorem norm_logMomentFilter_le (P : Polynomial ℂ) (v : ℕ → ℂ) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 < R) (hv : ∀ n, ‖v n‖ ≤ C / R ^ n) (N : ℕ) :
    ‖zetaMomentSequenceFilter P (fun k => ((k + 1 : ℕ) : ℂ) * v (k + 1)) N‖ ≤
      (C * ((N : ℝ) + 1) / R ^ (N + 1)) * filterRadiusCost P R := by
  unfold zetaMomentSequenceFilter Polynomial.sum
  calc
    _ ≤ ∑ k ∈ P.support, ‖P.coeff k * (((N + k + 1 : ℕ) : ℂ) * v (N + k + 1))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ P.support,
        ‖P.coeff k‖ * ((N + k + 1 : ℕ) : ℝ) * (C / R ^ (N + k + 1)) := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hv (N + k + 1)) (Nat.cast_nonneg _)) (norm_nonneg _)
    _ ≤ ∑ k ∈ P.support,
        ‖P.coeff k‖ * (((N : ℝ) + 1) * ((k : ℝ) + 1)) * (C / R ^ (N + k + 1)) := by
      apply Finset.sum_le_sum
      intro k _hk
      have hn : ((N + k + 1 : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * ((k : ℝ) + 1) := by
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
        (div_nonneg hC (pow_nonneg hR.le _))
    _ = _ := by
      unfold filterRadiusCost
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [show N + k + 1 = (N + 1) + k by omega, pow_add]
      field_simp

/-- The actual fixed factorial filter on the normalized correction,
including the logarithmic mark's shift and multiplicity. -/
def filteredResponse (Q : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  zetaMomentSequenceFilter P (fun k => ((k + 1 : ℕ) : ℂ) * momentResponse Q s L (k + 1)) N

/-- The entire fixed filter has an explicit integrated correction bound,
uniform in the physical length and in every finite prime selection. -/
theorem norm_filteredResponse_le (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (P : Polynomial ℂ) (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hhalf : 1 / 2 < s.re - R) (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p)
    {a L : ℝ} (ha : 0 < a) (hL : a ≤ L) :
    ‖filteredResponse Q P N s L‖ ≤
      (normalizedTailBudget (s.re - R) a K * ((N : ℝ) + 1) / R ^ (N + 1)) *
        filterRadiusCost P R :=
  norm_logMomentFilter_le P _ (normalizedTailBudget_nonneg hhalf ha K) hR
    (fun n => norm_momentResponse_le Q h16 hR hhalf K hK ha hL n) N

/-- Source normalization turns the full factorial-filter allowance into
an explicit polynomial times a geometric ratio, uniformly in the cutoff. -/
theorem norm_scaled_filteredResponse_le (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (P : Polynomial ℂ) (N : ℕ) {s : ℂ} {R u : ℝ} (hR : 0 < R) (hu : 0 ≤ u)
    (hhalf : 1 / 2 < s.re - R) (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p)
    {a L : ℝ} (ha : 0 < a) (hL : a ≤ L) :
    ‖(u : ℂ) ^ (N + 1) * filteredResponse Q P N s L‖ ≤
      (normalizedTailBudget (s.re - R) a K * filterRadiusCost P R) *
        (((N : ℝ) + 1) * (u / R) ^ (N + 1)) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  apply (mul_le_mul_of_nonneg_left
    (norm_filteredResponse_le Q h16 P N hR hhalf K hK ha hL) (pow_nonneg hu _)).trans_eq
  rw [div_pow]
  ring

/-- Every finite prime selection may vary with the order. The full
normalized fixed-filter correction still decays whenever the Cauchy radius
exceeds the source scale, with no restriction on the growth of the cutoff. -/
theorem tendsto_scaled_filteredResponse (P : Polynomial ℂ) (Q : ℕ → Finset ℕ)
    (h16 : ∀ N p, p ∈ Q N → 16 ≤ p) (L : ℕ → ℝ) {a : ℝ} (ha : 0 < a)
    (hL : ∀ N, a ≤ L N) {s : ℂ} {R u : ℝ} (hu : 0 ≤ u) (huR : u < R)
    (hhalf : 1 / 2 < s.re - R) :
    Filter.Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * filteredResponse (Q N) P N s (L N))
      Filter.atTop (nhds 0) := by
  have hR : 0 < R := lt_of_le_of_lt hu huR
  have hb (N : ℕ) := norm_scaled_filteredResponse_le (Q N) (h16 N) P N hR hu hhalf 0
    (fun _ _ => Nat.zero_le _) ha (hL N)
  apply squeeze_zero_norm hb
  have ht := (tendsto_self_mul_const_pow_of_lt_one (div_nonneg hu hR.le)
    ((div_lt_one hR).mpr huR)).comp (Filter.tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, mul_zero] using
    ht.const_mul (normalizedTailBudget (s.re - R) a 0 * filterRadiusCost P R)

/-- At the literal Euler center and the original growing Riesz length,
every fixed factorial polynomial filter of the complete correction decays
at each source scale below one. All prime selections and phases are retained. -/
theorem tendsto_physical_filteredResponse (P : Polynomial ℂ) (y : ℝ)
    (Q : ℕ → Finset ℕ) (h16 : ∀ N p, p ∈ Q N → 16 ≤ p)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Filter.Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      filteredResponse (Q N) P N (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u N))
        Filter.atTop (nhds 0) := by
  let R : ℝ := (u + 1) / 2
  apply tendsto_scaled_filteredResponse P Q h16 (SquarefreeVaughanLogSource.length u)
    (Real.log_pos (by norm_num : (1 : ℝ) < 4)) (ZetaRieszFixedCofactor.length_ge_log_four u)
    hu.le (show u < R by dsimp [R]; linarith)
  have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  rw [hs]
  dsimp [R]
  linarith

/-- The exact large-prime part of the completed original observation band. -/
def originalCorrectionPrimes (N : ℕ) : Finset ℕ :=
  (primorial (2 ^ (32 * N))).primeFactors.filter (fun p => 16 ≤ p)

/-- The complete correction on the actual original prime universe has
vanishing normalized factorial-filter response at the actual physical cutoff.
This is a bound for the correction alone, before its leading Euler coupling. -/
theorem tendsto_original_correction_response (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Filter.Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      filteredResponse (originalCorrectionPrimes N) P N (3 / 2 + Complex.I * y)
        (SquarefreeVaughanLogSource.length u N)) Filter.atTop (nhds 0) :=
  tendsto_physical_filteredResponse P y originalCorrectionPrimes
    (fun _ _ hp => (Finset.mem_filter.mp hp).2) hu hu1

end
end RiemannGaussian.ZetaRieszEulerMoments

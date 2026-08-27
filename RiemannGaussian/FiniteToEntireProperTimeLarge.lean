import RiemannGaussian.FiniteToEntireProperTimeEscape
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The large proper-time endpoint

This file begins the direct analysis of the endpoint `t → ∞`.  A single
hyperbolic heat term tends to zero unless the observation point coincides
with its upper root.  Dominated convergence over the genuine spectral-xi
divisor then proves that the complete spectral heat tends to zero at every
observation point which is not itself a spectral zero.

The second part proves a quantitative finite-divisor statement.  If every
upper root stays at least `delta > 0` from the observation point, then its
heat after time `T` decays relative to its value at `T` at exponential rate
`delta ^ 2`.  Consequently every later truncated action is at most the heat
at `T` divided by `delta ^ 2`.  Combining this estimate with fixed-time
convergence and the spectral decay gives uniform large-time tightness.

Thus the large endpoint is closed whenever the pinned observation point is
separated from the limiting spectral divisor.  The final theorem records
the exact remaining alternative for the canonical sequence under failure of
RH: either that tightness holds, or the pinned point is itself a spectral-xi
zero.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical Interval Topology

namespace RiemannGaussian

noncomputable section

/-! ## Decay of the complete spectral heat -/

/-- A non-colliding upper-half-plane pair has heat tending to zero at large
proper time. -/
theorem tendsto_upperHalfPlaneHyperbolicHeatIntegrand_atTop_zero
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    (hne : z ≠ alpha) :
    Tendsto (upperHalfPlaneHyperbolicHeatIntegrand z alpha)
      atTop (nhds 0) := by
  have hupper : 0 < Complex.normSq (z - alpha) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  have hneConj : z ≠ starRingEnd ℂ alpha := by
    intro heq
    have him := congrArg Complex.im heq
    simp only [Complex.conj_im] at him
    linarith
  have hlower : 0 < Complex.normSq (z - starRingEnd ℂ alpha) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hneConj)
  have hupperExp : Tendsto
      (fun tau : ℝ ↦ Real.exp
        (-(Complex.normSq (z - alpha) * tau)))
      atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [neg_mul, id_eq] using
      tendsto_const_nhds.neg_mul_atTop
        (neg_lt_zero.mpr hupper) tendsto_id
  have hlowerExp : Tendsto
      (fun tau : ℝ ↦ Real.exp
        (-(Complex.normSq (z - starRingEnd ℂ alpha) * tau)))
      atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [neg_mul, id_eq] using
      tendsto_const_nhds.neg_mul_atTop
        (neg_lt_zero.mpr hlower) tendsto_id
  change Tendsto
    (fun tau : ℝ ↦ tau⁻¹ *
      (Real.exp (-(Complex.normSq (z - alpha) * tau)) -
        Real.exp
          (-(Complex.normSq (z - starRingEnd ℂ alpha) * tau))))
    atTop (nhds 0)
  simpa only [zero_sub, neg_zero, mul_zero] using
    tendsto_inv_atTop_zero.mul (hupperExp.sub hlowerExp)

/-- If the observation point is not a spectral-xi zero, every individual
spectral heat summand tends to zero at large proper time. -/
theorem tendsto_zetaUpperHyperbolicHeatSummand_atTop_zero_of_ne_zero
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (rho : NontrivialZetaZero) :
    Tendsto (fun tau ↦ zetaUpperHyperbolicHeatSummand z tau rho)
      atTop (nhds 0) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hne : z ≠ zetaSpectralCoordinate rho.1 := by
      intro heq
      apply hxi
      exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero z).mpr
        ⟨rho, heq⟩
    have hupper' : rho.1.re < (2 : ℝ)⁻¹ := by
      rw [zetaSpectralCoordinate_im] at hupper
      linarith
    have hheat := tendsto_upperHalfPlaneHyperbolicHeatIntegrand_atTop_zero
      hz hupper hne
    have hscaled : Tendsto
        (fun tau ↦ (analyticZetaZeroMultiplicity rho : ℝ) *
          upperHalfPlaneHyperbolicHeatIntegrand z
            (zetaSpectralCoordinate rho.1) tau)
        atTop (nhds 0) := by
      simpa using hheat.const_mul
        (analyticZetaZeroMultiplicity rho : ℝ)
    apply hscaled.congr'
    exact Eventually.of_forall fun tau ↦ by
      simp [zetaUpperHyperbolicHeatSummand, hupper']
  · have hupper' : ¬rho.1.re < (2 : ℝ)⁻¹ := by
      intro hlt
      apply hupper
      rw [zetaSpectralCoordinate_im]
      linarith
    have hzero : Tendsto (fun _ : ℝ ↦ (0 : ℝ))
        atTop (nhds 0) := tendsto_const_nhds
    apply hzero.congr'
    exact Eventually.of_forall fun tau ↦ by
      simp [zetaUpperHyperbolicHeatSummand, hupper']

/-- Away from the spectral divisor, the complete upper spectral-xi heat sum
tends to zero at large proper time.  The proof uses the summable heat series
at time `1` as a common majorant for every later time. -/
theorem tendsto_riemannXiUpperHyperbolicHeatSum_atTop_zero_of_ne_zero
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    Tendsto (riemannXiUpperHyperbolicHeatSum z) atTop (nhds 0) := by
  have hboundSummable : Summable
      (zetaUpperHyperbolicHeatSummand z 1) :=
    summable_zetaUpperHyperbolicHeatSummand hz zero_lt_one
  have hterm (rho : NontrivialZetaZero) :
      Tendsto (fun tau ↦ zetaUpperHyperbolicHeatSummand z tau rho)
        atTop (nhds 0) :=
    tendsto_zetaUpperHyperbolicHeatSummand_atTop_zero_of_ne_zero
      hz hxi rho
  have hbound : ∀ᶠ tau in atTop,
      ∀ rho : NontrivialZetaZero,
        ‖zetaUpperHyperbolicHeatSummand z tau rho‖ ≤
          zetaUpperHyperbolicHeatSummand z 1 rho := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with tau htau
    intro rho
    by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
    · have htauPos : 0 < tau := zero_lt_one.trans_le htau
      have hheatNonneg : 0 ≤ upperHalfPlaneHyperbolicHeatIntegrand z
          (zetaSpectralCoordinate rho.1) tau :=
        (upperHalfPlaneHyperbolicHeatIntegrand_pos
          hz hupper htauPos).le
      rw [zetaUpperHyperbolicHeatSummand,
        if_pos hupper, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hheatNonneg),
        zetaUpperHyperbolicHeatSummand, if_pos hupper]
      exact mul_le_mul_of_nonneg_left
        (upperHalfPlaneHyperbolicHeatIntegrand_le_of_time_le
          hz hupper zero_lt_one htau)
        (Nat.cast_nonneg _)
    · rw [zetaUpperHyperbolicHeatSummand, if_neg hupper,
        zetaUpperHyperbolicHeatSummand, if_neg hupper]
      simp
  have hlimit := tendsto_tsum_of_dominated_convergence
    hboundSummable hterm hbound
  change Tendsto
    (fun tau ↦ ∑' rho : NontrivialZetaZero,
      zetaUpperHyperbolicHeatSummand z tau rho)
    atTop (nhds 0)
  simpa only [tsum_zero] using hlimit

/-! ## Relative exponential decay for finite divisors -/

/-- A divided exponential difference with lower spectral edge at least
`delta ^ 2` decays, relative to its value at an earlier time, at rate
`delta ^ 2`. -/
theorem expDifferenceDiv_le_mul_exp_decay
    {A B delta s t : ℝ} (hdeltaA : delta ^ 2 ≤ A) (hAB : A ≤ B)
    (hs : 0 < s) (hst : s ≤ t) :
    t⁻¹ * (Real.exp (-(A * t)) - Real.exp (-(B * t))) ≤
      (s⁻¹ * (Real.exp (-(A * s)) - Real.exp (-(B * s)))) *
        Real.exp (-(delta ^ 2 * (t - s))) := by
  have ht : 0 < t := hs.trans_le hst
  rw [expDifferenceDiv_eq_intervalIntegral ht,
    expDifferenceDiv_eq_intervalIntegral hs]
  calc
    (∫ x in A..B, Real.exp (-(x * t))) ≤
        ∫ x in A..B,
          Real.exp (-(x * s)) *
            Real.exp (-(delta ^ 2 * (t - s))) := by
      apply intervalIntegral.integral_mono_on hAB
      · exact (by fun_prop : Continuous fun x : ℝ ↦
          Real.exp (-(x * t))).intervalIntegrable A B
      · exact (by fun_prop : Continuous fun x : ℝ ↦
          Real.exp (-(x * s)) *
            Real.exp (-(delta ^ 2 * (t - s)))).intervalIntegrable A B
      · intro x hx
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hdeltaX : delta ^ 2 ≤ x := hdeltaA.trans hx.1
        nlinarith [mul_nonneg (sub_nonneg.mpr hdeltaX)
          (sub_nonneg.mpr hst)]
    _ = (∫ x in A..B, Real.exp (-(x * s))) *
          Real.exp (-(delta ^ 2 * (t - s))) := by
      rw [intervalIntegral.integral_mul_const]

/-- A separated upper-half-plane root has the corresponding relative
large-time exponential decay. -/
theorem upperHalfPlaneHyperbolicHeatIntegrand_le_mul_exp_decay
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    {delta s t : ℝ} (hdelta : 0 ≤ delta)
    (hdist : delta ≤ dist z alpha)
    (hs : 0 < s) (hst : s ≤ t) :
    upperHalfPlaneHyperbolicHeatIntegrand z alpha t ≤
      upperHalfPlaneHyperbolicHeatIntegrand z alpha s *
        Real.exp (-(delta ^ 2 * (t - s))) := by
  have hnorm : delta ≤ ‖z - alpha‖ := by
    simpa [dist_eq_norm] using hdist
  have hdeltaSq : delta ^ 2 ≤ Complex.normSq (z - alpha) := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_le_sq₀ hdelta (norm_nonneg _)).2 hnorm
  have hsqOrder : Complex.normSq (z - alpha) ≤
      Complex.normSq (z - starRingEnd ℂ alpha) := by
    rw [show Complex.normSq (z - alpha) =
        pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im by
      unfold Complex.normSq pairHyperbolicUpperSq
      simp
      ring,
      show Complex.normSq (z - starRingEnd ℂ alpha) =
        pairHyperbolicLowerSq (z.re - alpha.re) z.im alpha.im by
      unfold Complex.normSq pairHyperbolicLowerSq
      simp
      ring]
    exact (pairHyperbolicUpperSq_lt_lowerSq halpha hz).le
  unfold upperHalfPlaneHyperbolicHeatIntegrand
  exact expDifferenceDiv_le_mul_exp_decay
    hdeltaSq hsqOrder hs hst

/-- A finite upper divisor with a common observation gap inherits the same
relative exponential decay. -/
theorem finiteUpperHyperbolicHeatSum_le_mul_exp_decay
    {z : ℂ} (hz : 0 < z.im) {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    {delta s t : ℝ} (hdelta : 0 ≤ delta)
    (hdist : ∀ alpha ∈ upper, delta ≤ dist z alpha)
    (hs : 0 < s) (hst : s ≤ t) :
    finiteUpperHyperbolicHeatSum z upper t ≤
      finiteUpperHyperbolicHeatSum z upper s *
        Real.exp (-(delta ^ 2 * (t - s))) := by
  induction upper using Multiset.induction_on with
  | empty => simp [finiteUpperHyperbolicHeatSum]
  | @cons alpha upper ih =>
      rw [finiteUpperHyperbolicHeatSum, Multiset.map_cons,
        Multiset.sum_cons, finiteUpperHyperbolicHeatSum,
        Multiset.map_cons, Multiset.sum_cons]
      calc
        upperHalfPlaneHyperbolicHeatIntegrand z alpha t +
            (upper.map fun beta ↦
              upperHalfPlaneHyperbolicHeatIntegrand z beta t).sum ≤
          upperHalfPlaneHyperbolicHeatIntegrand z alpha s *
              Real.exp (-(delta ^ 2 * (t - s))) +
            (upper.map fun beta ↦
              upperHalfPlaneHyperbolicHeatIntegrand z beta s).sum *
              Real.exp (-(delta ^ 2 * (t - s))) := by
          apply add_le_add
          · exact upperHalfPlaneHyperbolicHeatIntegrand_le_mul_exp_decay
              hz (halpha alpha (by simp)) hdelta
              (hdist alpha (by simp)) hs hst
          · apply ih
            · intro beta hbeta
              exact halpha beta (by simp [hbeta])
            · intro beta hbeta
              exact hdist beta (by simp [hbeta])
        _ = (upperHalfPlaneHyperbolicHeatIntegrand z alpha s +
              (upper.map fun beta ↦
                upperHalfPlaneHyperbolicHeatIntegrand z beta s).sum) *
              Real.exp (-(delta ^ 2 * (t - s))) := by
          ring

/-- The integral of the normalized exponential tail is bounded by the
inverse squared gap. -/
theorem intervalIntegral_exp_neg_sq_sub_le_inv_sq
    {delta T U : ℝ} (hdelta : 0 < delta) :
    (∫ t in T..U, Real.exp (-(delta ^ 2 * (t - T)))) ≤
      (delta ^ 2)⁻¹ := by
  have hsq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hderiv (x : ℝ) :
      HasDerivAt
        (fun y : ℝ ↦
          -(delta ^ 2)⁻¹ *
            Real.exp (-(delta ^ 2 * (y - T))))
        (Real.exp (-(delta ^ 2 * (x - T)))) x := by
    have hinner : HasDerivAt
        (fun y : ℝ ↦ -(delta ^ 2 * (y - T)))
        (-(delta ^ 2)) x := by
      have hbase : HasDerivAt
          (fun y : ℝ ↦ -(delta ^ 2) * (y - T))
          (-(delta ^ 2)) x := by
        apply (((hasDerivAt_id x).sub_const T).const_mul
          (-(delta ^ 2))).congr_deriv
        ring
      apply hbase.congr_of_eventuallyEq
      exact Eventually.of_forall fun y ↦ by ring
    have hexp := (Real.hasDerivAt_exp
      (-(delta ^ 2 * (x - T)))).comp x hinner
    have hscaled := hexp.const_mul (-(delta ^ 2)⁻¹)
    apply hscaled.congr_deriv
    field_simp [ne_of_gt hsq]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hderiv x)
    ((by fun_prop : Continuous fun x : ℝ ↦
      Real.exp (-(delta ^ 2 * (x - T)))).intervalIntegrable T U)]
  have hinv : 0 ≤ (delta ^ 2)⁻¹ := inv_nonneg.mpr hsq.le
  have hprod : 0 ≤ (delta ^ 2)⁻¹ *
      Real.exp (-(delta ^ 2 * (U - T))) :=
    mul_nonneg hinv (Real.exp_pos _).le
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]
  nlinarith

/-- Every finite action after time `T` is bounded by the heat at `T` divided
by the squared common root gap.  The bound is uniform in the right endpoint
`U`. -/
theorem upperHalfPlaneHyperbolicHeatAction_le_heat_div_sq
    {z : ℂ} (hz : 0 < z.im) {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    {delta T U : ℝ} (hdelta : 0 < delta)
    (hdist : ∀ alpha ∈ upper, delta ≤ dist z alpha)
    (hT : 0 < T) (hTU : T ≤ U) :
    upperHalfPlaneHyperbolicHeatAction z upper (T, U) ≤
      finiteUpperHyperbolicHeatSum z upper T / delta ^ 2 := by
  rw [upperHalfPlaneHyperbolicHeatAction_eq_intervalIntegral
    z upper hT hTU]
  have hheatNonneg : 0 ≤ finiteUpperHyperbolicHeatSum z upper T :=
    finiteUpperHyperbolicHeatSum_nonneg hz halpha hT
  calc
    (∫ tau in T..U, finiteUpperHyperbolicHeatSum z upper tau) ≤
        ∫ tau in T..U,
          finiteUpperHyperbolicHeatSum z upper T *
            Real.exp (-(delta ^ 2 * (tau - T))) := by
      apply intervalIntegral.integral_mono_on hTU
      · exact intervalIntegrable_finiteUpperHyperbolicHeatSum
          z upper hT hTU
      · exact (by fun_prop : Continuous fun tau : ℝ ↦
          finiteUpperHyperbolicHeatSum z upper T *
            Real.exp (-(delta ^ 2 * (tau - T)))).intervalIntegrable T U
      · intro tau htau
        exact finiteUpperHyperbolicHeatSum_le_mul_exp_decay
          hz halpha hdelta.le hdist hT htau.1
    _ = finiteUpperHyperbolicHeatSum z upper T *
          (∫ tau in T..U,
            Real.exp (-(delta ^ 2 * (tau - T)))) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ finiteUpperHyperbolicHeatSum z upper T * (delta ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (intervalIntegral_exp_neg_sq_sub_le_inv_sq hdelta)
        hheatNonneg
    _ = finiteUpperHyperbolicHeatSum z upper T / delta ^ 2 := by
      rw [div_eq_mul_inv]

/-- Fixed-time convergence to a heat profile which vanishes at infinity,
together with one eventual common root gap, implies uniform large-time
tightness of all finite actions. -/
theorem eventually_finiteUpperHyperbolicHeatAction_largeTime_lt
    (upper : ℕ → Multiset ℂ) {z : ℂ} (hz : 0 < z.im)
    (halpha : ∀ n alpha, alpha ∈ upper n → 0 < alpha.im)
    {delta : ℝ} (hdelta : 0 < delta)
    (hdist : ∀ᶠ n in atTop,
      ∀ alpha ∈ upper n, delta ≤ dist z alpha)
    (g : ℝ → ℝ)
    (hpointwise : ∀ T : ℝ, 0 < T →
      Tendsto (fun n ↦ finiteUpperHyperbolicHeatSum z (upper n) T)
        atTop (nhds (g T)))
    (hdecay : Tendsto g atTop (nhds 0))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ T : ℝ, 0 < T ∧
      ∀ᶠ n in atTop, ∀ U : ℝ, T ≤ U →
        upperHalfPlaneHyperbolicHeatAction z (upper n) (T, U) <
          epsilon := by
  have htarget : 0 < epsilon * delta ^ 2 :=
    mul_pos hepsilon (sq_pos_of_pos hdelta)
  have hgBound : ∀ᶠ T in atTop,
      g T < epsilon * delta ^ 2 / 2 :=
    (tendsto_order.1 hdecay).2
      (epsilon * delta ^ 2 / 2) (by linarith)
  obtain ⟨T, hT, hgT⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and hgBound).exists
  have hgTFull : g T < epsilon * delta ^ 2 := by
    linarith
  have hheatBound : ∀ᶠ n in atTop,
      finiteUpperHyperbolicHeatSum z (upper n) T <
        epsilon * delta ^ 2 :=
    (tendsto_order.1 (hpointwise T hT)).2
      (epsilon * delta ^ 2) hgTFull
  refine ⟨T, hT, ?_⟩
  filter_upwards [hdist, hheatBound] with n hdistn hheatn
  intro U hTU
  have haction := upperHalfPlaneHyperbolicHeatAction_le_heat_div_sq
    hz (halpha n) hdelta hdistn hT hTU
  exact haction.trans_lt ((div_lt_iff₀ (sq_pos_of_pos hdelta)).2 hheatn)

/-! ## Separation supplied by zero-free locally uniform convergence -/

/-- If locally uniformly convergent separable real polynomials approach a
continuous function which is nonzero at `z`, then all of their upper roots
are eventually separated from `z` by one fixed positive distance. -/
theorem exists_eventually_realPolynomialUpperRootMultiset_separated_of_ne_zero
    (A : ℕ → ℝ[X]) {f : ℂ → ℂ}
    (hlimit : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      f atTop Set.univ)
    (hseparable : ∀ n, (A n).Separable)
    (hf : Continuous f) {z : ℂ} (hz : f z ≠ 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ᶠ n in atTop, ∀ alpha ∈
        realPolynomialUpperRootMultiset (A n),
          delta ≤ dist z alpha := by
  let V : Set ℂ := f ⁻¹' ({0}ᶜ : Set ℂ)
  have hVOpen : IsOpen V := isOpen_compl_singleton.preimage hf
  have hzV : z ∈ V := by
    simpa [V] using hz
  obtain ⟨r, hr, hball⟩ := (Metric.isOpen_iff.mp hVOpen z hzV)
  let delta := r / 2
  have hdelta : 0 < delta := by
    simp only [delta]
    linarith
  have hclosed : closedBall z delta ⊆ V := by
    intro w hw
    apply hball
    rw [mem_ball]
    have hwle : dist w z ≤ delta := mem_closedBall.mp hw
    calc
      dist w z ≤ delta := hwle
      _ < r := by
        simp only [delta]
        linarith
  have hzeroV : ∀ w ∈ V, f w ≠ 0 := by
    intro w hw
    simpa [V] using hw
  have happroximantZeroFree : ∀ᶠ n in atTop,
      ∀ w ∈ closedBall z delta,
        ((A n).map Complex.ofRealHom).eval w ≠ 0 :=
    eventually_forall_ne_zero_on_compact_of_tendstoLocallyUniformlyOn
      (hlimit.mono (subset_univ V)) hVOpen
      (isCompact_closedBall z delta) hclosed hf.continuousOn hzeroV
  refine ⟨delta, hdelta, ?_⟩
  filter_upwards [happroximantZeroFree] with n hn
  intro alpha halpha
  by_contra hnot
  have hdistLt : dist z alpha < delta := lt_of_not_ge hnot
  have halphaBall : alpha ∈ closedBall z delta := by
    rw [mem_closedBall, dist_comm]
    exact hdistLt.le
  have halphaRoots : alpha ∈
      ((A n).map Complex.ofRealHom).roots :=
    (Multiset.mem_filter.mp halpha).1
  have halphaZero : ((A n).map Complex.ofRealHom).eval alpha = 0 :=
    (Polynomial.mem_roots
      (Polynomial.map_ne_zero (hseparable n).ne_zero)).mp halphaRoots
  exact (hn alpha halphaBall) halphaZero

/-- For an actual locally uniform polynomial approximation to spectral xi,
noncollision of the observation point closes the large proper-time endpoint
once the already-proved fixed-time heat convergence is available. -/
theorem eventually_realPolynomialUpperHeatAction_largeTime_lt_of_ne_zero
    (A : ℕ → ℝ[X])
    (hlimit : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral atTop Set.univ)
    (hseparable : ∀ n, (A n).Separable)
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (hpointwise : ∀ T : ℝ, 0 < T →
      Tendsto
        (fun n ↦ realPolynomialUpperHyperbolicHeatSum (A n) z T)
        atTop (nhds (riemannXiUpperHyperbolicHeatSum z T)))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ T : ℝ, 0 < T ∧
      ∀ᶠ n in atTop, ∀ U : ℝ, T ≤ U →
        upperHalfPlaneHyperbolicHeatAction z
          (realPolynomialUpperRootMultiset (A n)) (T, U) < epsilon := by
  obtain ⟨delta, hdelta, hseparated⟩ :=
    exists_eventually_realPolynomialUpperRootMultiset_separated_of_ne_zero
      A hlimit hseparable differentiable_riemannXiSpectral.continuous hxi
  apply eventually_finiteUpperHyperbolicHeatAction_largeTime_lt
    (fun n ↦ realPolynomialUpperRootMultiset (A n)) hz
    (fun n ↦ realPolynomialUpperRootMultiset_im_pos (A n))
    hdelta hseparated (riemannXiUpperHyperbolicHeatSum z)
  · intro T hT
    simpa [realPolynomialUpperHyperbolicHeatSum] using
      hpointwise T hT
  · exact tendsto_riemannXiUpperHyperbolicHeatSum_atTop_zero_of_ne_zero
      hz hxi
  · exact hepsilon

/-! ## The canonical RH reductio frontier -/

/-- Under failure of RH, the canonical finite Hardy sequence now satisfies
an exact large-time dichotomy.  If its pinned point is not itself a
spectral-xi zero, all sufficiently late finite actions are uniformly tight at
infinity.  The only remaining large-time alternative is literal collision of
the pinned point with the limiting spectral divisor.

The same sequence retains its fixed positive full-mass lower bound, so in the
noncollision branch any surviving endpoint escape is forced toward proper
time zero. -/
theorem exists_canonicalFiniteHardyFrontier_largeTimeTight_or_collision_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        (∀ (u : ℂ) (tau : ℝ), 0 < u.im → 0 < tau →
          Tendsto
            (fun n ↦ realPolynomialUpperHyperbolicHeatSum (B n) u tau)
            atTop (nhds (riemannXiUpperHyperbolicHeatSum u tau))) ∧
        0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
        (∀ n,
          -2 * Real.log (pairHyperbolicThreshold eta z.im) ≤
            realPolynomialUpperHyperbolicHeatMass (B n) z) ∧
        (riemannXiSpectral z = 0 ∨
          ∀ epsilon : ℝ, 0 < epsilon →
            ∃ T : ℝ, 0 < T ∧
              ∀ᶠ n in atTop, ∀ U : ℝ, T ≤ U →
                upperHalfPlaneHyperbolicHeatAction z
                  (realPolynomialUpperRootMultiset (B n)) (T, U) <
                    epsilon) := by
  obtain ⟨eta, heta, z, hz, hxi, B, hlimit, hfrontier, hheat⟩ :=
    exists_canonicalFiniteHardyFrontier_fullHeat_tendsto_of_not_rh hRH
  have hstageZero := realPolynomialUpperHyperbolicHeatAction_frontier
    (hfrontier 0).separable heta hz (hfrontier 0).homotopyRoot
  refine ⟨eta, heta, z, hz, B, hlimit, hfrontier, hheat,
    hstageZero.2.1, ?_, ?_⟩
  · intro n
    exact (realPolynomialUpperHyperbolicHeatAction_frontier
      (hfrontier n).separable heta hz
      (hfrontier n).homotopyRoot).2.2
  · right
    intro epsilon hepsilon
    exact eventually_realPolynomialUpperHeatAction_largeTime_lt_of_ne_zero
      B hlimit (fun n ↦ (hfrontier n).separable)
      hz hxi (fun T hT ↦ hheat z T hz hT) hepsilon

/-- Under failure of RH, the canonical radial Hardy sequence may be chosen
at a noncolliding pinned homotopy root, and its large-time actions are then
uniformly tight.  This removes the collision branch from the actual
finite-to-entire sequence while retaining its fixed-time heat limit and
stage-independent positive full-mass lower bound. -/
theorem exists_canonicalFiniteHardyFrontier_largeTimeTight_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      riemannXiSpectral z ≠ 0 ∧ ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        (∀ (u : ℂ) (tau : ℝ), 0 < u.im → 0 < tau →
          Tendsto
            (fun n ↦ realPolynomialUpperHyperbolicHeatSum (B n) u tau)
            atTop (nhds (riemannXiUpperHyperbolicHeatSum u tau))) ∧
        0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
        (∀ n,
          -2 * Real.log (pairHyperbolicThreshold eta z.im) ≤
            realPolynomialUpperHyperbolicHeatMass (B n) z) ∧
        (∀ (u : ℂ) (a b : ℝ), 0 < u.im → 0 < a → a ≤ b →
          IntervalIntegrable (riemannXiUpperHyperbolicHeatSum u)
              volume a b ∧
            Tendsto
              (fun n ↦ upperHalfPlaneHyperbolicHeatAction u
                (realPolynomialUpperRootMultiset (B n)) (a, b))
              atTop
              (nhds (∫ tau in a..b,
                riemannXiUpperHyperbolicHeatSum u tau))) ∧
        ∀ epsilon : ℝ, 0 < epsilon →
          ∃ T : ℝ, 0 < T ∧
            ∀ᶠ n in atTop, ∀ U : ℝ, T ≤ U →
              upperHalfPlaneHyperbolicHeatAction z
                (realPolynomialUpperRootMultiset (B n)) (T, U) <
                  epsilon := by
  obtain ⟨eta, heta, z, hz, hxi, B, hlimit, hfrontier, hheat⟩ :=
    exists_canonicalFiniteHardyFrontier_fullHeat_tendsto_of_not_rh hRH
  have hstageZero := realPolynomialUpperHyperbolicHeatAction_frontier
    (hfrontier 0).separable heta hz (hfrontier 0).homotopyRoot
  refine ⟨eta, heta, z, hz, hxi, B, hlimit, hfrontier, hheat,
    hstageZero.2.1, ?_, ?_, ?_⟩
  · intro n
    exact (realPolynomialUpperHyperbolicHeatAction_frontier
      (hfrontier n).separable heta hz
      (hfrontier n).homotopyRoot).2.2
  · intro u a b hu ha hab
    apply tendsto_realPolynomialUpperHeatAction_on_compact_of_pointwise
      B hu (fun tau htau ↦ hheat u tau hu htau) ha hab
  · intro epsilon hepsilon
    exact eventually_realPolynomialUpperHeatAction_largeTime_lt_of_ne_zero
      B hlimit (fun n ↦ (hfrontier n).separable)
      hz hxi (fun T hT ↦ hheat z T hz hT) hepsilon

end

end RiemannGaussian

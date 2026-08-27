import RiemannGaussian.FiniteToEntireDegreeControl

/-!
# Expanding-disk Taylor control for spectral xi

This file replaces qualitative compact convergence by a quantitative estimate
on disks whose radius grows like the square root of the Taylor index.  It first
proves a Cauchy coefficient bound directly from the circle integral, transports
that bound to the fixed global power series by analytic uniqueness, and sums
the geometric tail.

The formal quadratic growth theorem for spectral xi then yields constants
`A ≥ 1` and `c > 0` for which its real Taylor polynomial of order `n`
converges uniformly throughout `‖w‖ ≤ c * sqrt n`.  The same scale makes a
linearly degree-weighted Gaussian root tail vanish at every fixed positive
proper time.  `FiniteToEntireExpandingPinned` carries this control through
exact root pinning and separability.  The remaining localization task is a
zero-counting argument on expanding zero-free circles.
-/

open Filter Polynomial Set
open scoped ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- At every positive proper time and every fixed positive scale `c`, a linear
degree factor times the Gaussian at radius `c * sqrt n` tends to zero. -/
theorem tendsto_indexGaussian_const_mul_sqrt
    {c tau : ℝ} (hc : 0 < c) (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ ↦ ((max n 3 : ℕ) : ℝ) *
        (tau⁻¹ * Real.exp
          (-((c * Real.sqrt (n : ℝ)) ^ 2 * tau))))
      atTop (nhds 0) := by
  have hb : 0 < c ^ 2 * tau := mul_pos (sq_pos_of_pos hc) htau
  have hbase :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 : ℝ) (c ^ 2 * tau) hb).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlinear : Tendsto
      (fun n : ℕ ↦ (n : ℝ) *
        (tau⁻¹ * Real.exp (-((c ^ 2 * tau) * (n : ℝ)))))
      atTop (nhds 0) := by
    simpa [Real.rpow_one, mul_assoc, mul_comm, mul_left_comm] using
      hbase.const_mul tau⁻¹
  apply hlinear.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [max_eq_left hn]
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  congr 3
  ring

/-- For linearly degree-controlled polynomials, separation of every unused
root by `c * sqrt n`, for any fixed `c > 0`, forces the exact complement heat
to vanish. -/
theorem tendsto_realPolynomialUpperHeatRemainderOutsideRootMultiset_zero_of_const_mul_sqrtIndexSeparation
    (B : ℕ → ℝ[X])
    (hdegree : ∀ n, (B n).natDegree ≤ max n 3)
    (selected : ℕ → Multiset ℂ)
    {z : ℂ} (hz : 0 < z.im) {c tau : ℝ}
    (hc : 0 < c) (htau : 0 < tau)
    (hdist : ∀ᶠ n in atTop, ∀ alpha ∈
      realPolynomialUpperRootMultiset (B n) - selected n,
      c * Real.sqrt (n : ℝ) ≤ dist z alpha) :
    Tendsto
      (fun n ↦ realPolynomialUpperHeatRemainderOutsideRootMultiset
        (B n) (selected n) z tau)
      atTop (nhds 0) := by
  apply
    tendsto_realPolynomialUpperHeatRemainderOutsideRootMultiset_zero_of_indexGaussian
      B hdegree selected hz htau (fun n ↦ c * Real.sqrt (n : ℝ))
  · filter_upwards with n
    positivity
  · exact hdist
  · exact tendsto_indexGaussian_const_mul_sqrt hc htau

/-- The global quadratic growth estimate for xi, transported to the spectral
coordinate with a convenient additive constant. -/
theorem exists_riemannXiSpectral_quadraticGrowth :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ z : ℂ,
      ‖riemannXiSpectral z‖ ≤
        Real.exp (A * (‖z‖ + 2) ^ 2) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  refine ⟨A, hA, ?_⟩
  intro z
  refine (hbound (completedSpectralCoordinate z)).trans ?_
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  apply (sq_le_sq₀ (by positivity) (by positivity)).2
  unfold completedSpectralCoordinate
  calc
    ‖1 / 2 + Complex.I * z‖ + 1 ≤
        (‖(1 / 2 : ℂ)‖ + ‖Complex.I * z‖) + 1 := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖z‖ + 2 := by
      simp
      linarith

/-- A uniform bound on a positive circle gives the corresponding Cauchy
coefficient bound. -/
theorem cauchyPowerSeries_norm_le_of_circle_bound
    {f : ℂ → ℂ} (hf : Continuous f) {R M : ℝ} (hR : 0 < R)
    (hbound : ∀ theta ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖f (circleMap 0 R theta)‖ ≤ M) (n : ℕ) :
    ‖cauchyPowerSeries f 0 R n‖ ≤ M * R⁻¹ ^ n := by
  have hcont : Continuous (fun theta : ℝ ↦
      ‖f (circleMap 0 R theta)‖) := by
    fun_prop
  have hint :
      (∫ theta : ℝ in 0..2 * Real.pi,
          ‖f (circleMap 0 R theta)‖) ≤
        ∫ _theta : ℝ in 0..2 * Real.pi, M := by
    apply intervalIntegral.integral_mono_on
    · positivity
    · exact hcont.intervalIntegrable _ _
    · exact intervalIntegrable_const
    · exact hbound
  calc
    ‖cauchyPowerSeries f 0 R n‖ ≤
        ((2 * Real.pi)⁻¹ *
          ∫ theta : ℝ in 0..2 * Real.pi,
            ‖f (circleMap 0 R theta)‖) * |R|⁻¹ ^ n :=
      norm_cauchyPowerSeries_le f 0 R n
    _ ≤ ((2 * Real.pi)⁻¹ *
          (∫ _theta : ℝ in 0..2 * Real.pi, M)) * |R|⁻¹ ^ n := by
      gcongr
    _ = M * R⁻¹ ^ n := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      rw [abs_of_pos hR]
      field_simp

/-- For an entire function, analytic uniqueness transfers a sphere bound at
an arbitrary positive radius to the canonical radius-one Cauchy series. -/
theorem entire_cauchyPowerSeries_norm_le_of_sphere_bound
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R M : ℝ} (hR : 0 < R)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ M) (n : ℕ) :
    ‖cauchyPowerSeries f 0 1 n‖ ≤ M * R⁻¹ ^ n := by
  let Rnn : NNReal := ⟨R, hR.le⟩
  have hpone : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 1) 0 ⊤ :=
    hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)
  have hpR : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 Rnn) 0 ⊤ :=
    hf.hasFPowerSeriesOnBall 0 (R := Rnn) (by exact_mod_cast hR)
  have hseries : cauchyPowerSeries f 0 1 = cauchyPowerSeries f 0 R := by
    rw [← show (Rnn : ℝ) = R from rfl]
    exact hpone.hasFPowerSeriesAt.eq_formalMultilinearSeries
      hpR.hasFPowerSeriesAt
  rw [hseries]
  apply cauchyPowerSeries_norm_le_of_circle_bound hf.continuous hR
  intro theta _
  apply hbound
  simp [norm_circleMap_zero, abs_of_pos hR]

/-- The `n`th power-series term at `w` obeys the geometric Cauchy bound with
ratio `‖w‖ / R`. -/
theorem entire_cauchyPowerSeries_apply_norm_le_of_sphere_bound
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R M : ℝ} (hR : 0 < R)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ M) (w : ℂ) (n : ℕ) :
    ‖cauchyPowerSeries f 0 1 n (fun _ ↦ w)‖ ≤
      M * (‖w‖ / R) ^ n := by
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, norm_smul,
    norm_pow, ← FormalMultilinearSeries.norm_apply_eq_norm_coef]
  calc
    ‖w‖ ^ n * ‖cauchyPowerSeries f 0 1 n‖ ≤
        ‖w‖ ^ n * (M * R⁻¹ ^ n) :=
      mul_le_mul_of_nonneg_left
        (entire_cauchyPowerSeries_norm_le_of_sphere_bound
          hf hR hbound n) (pow_nonneg (norm_nonneg w) n)
    _ = M * (‖w‖ / R) ^ n := by
      simp only [div_eq_mul_inv, mul_pow]
      ring

/-- The Taylor remainder of an entire function is bounded by the geometric
tail induced by any larger positive comparison sphere. -/
theorem entire_cauchyPowerSeries_partialSum_remainder_le_of_sphere_bound
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R M : ℝ} (hR : 0 < R)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ M)
    {w : ℂ} (hw : ‖w‖ < R) (N : ℕ) :
    ‖(cauchyPowerSeries f 0 1).partialSum N w - f w‖ ≤
      M * (‖w‖ / R) ^ N / (1 - ‖w‖ / R) := by
  have hratio : ‖w‖ / R < 1 := (div_lt_one hR).2 hw
  have hp : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 1) 0 ⊤ :=
    hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)
  apply norm_sub_le_of_geometric_bound_of_hasSum hratio
  · intro n
    exact entire_cauchyPowerSeries_apply_norm_le_of_sphere_bound
      hf hR hbound w n
  · simpa using hp.hasSum (y := w) (by simp)

/-- Evaluation of the mapped real Taylor polynomial is exactly the canonical
complex formal-series partial sum. -/
theorem entireRealTaylorPolynomial_map_eval
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (N : ℕ) (w : ℂ) :
    ((entireRealTaylorPolynomial f N).map Complex.ofRealHom).eval w =
      (cauchyPowerSeries f 0 1).partialSum N w := by
  apply realFormalPowerSeriesPartialPolynomial_map_eval
  intro n
  have hp : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 1) 0 ⊤ :=
    hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)
  exact formalPowerSeries_coeff_im_eq_zero_of_maps_real_to_real
    hf hreal hp n

/-- Spectral xi's real Taylor polynomial has an explicit pointwise Cauchy
remainder bound on every disk strictly inside its comparison circle. -/
theorem exists_riemannXiSpectral_taylor_remainder_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {R : ℝ}, 0 < R → ∀ {w : ℂ}, ‖w‖ < R → ∀ N : ℕ,
      ‖((riemannXiSpectralRealTaylorPolynomial N).map
          Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤
        Real.exp (A * (R + 2) ^ 2) * (‖w‖ / R) ^ N /
          (1 - ‖w‖ / R) := by
  obtain ⟨A, hA, hgrowth⟩ := exists_riemannXiSpectral_quadraticGrowth
  refine ⟨A, hA, ?_⟩
  intro R hR w hw N
  rw [riemannXiSpectralRealTaylorPolynomial,
    entireRealTaylorPolynomial_map_eval
      differentiable_riemannXiSpectral riemannXiSpectral_ofReal_im]
  apply entire_cauchyPowerSeries_partialSum_remainder_le_of_sphere_bound
    differentiable_riemannXiSpectral hR
  · intro u hu
    simpa [hu] using hgrowth u
  · exact hw

/-- If the square-root scale is below the explicit quadratic-growth
threshold, its Cauchy envelope times `2⁻ⁿ` tends to zero. -/
theorem tendsto_quadraticGrowth_mul_half_pow
    {A c : ℝ} (hA : 0 ≤ A)
    (hsmall : 8 * A * c ^ 2 < Real.log 2) :
    Tendsto
      (fun n : ℕ ↦ Real.exp
          (A * (2 * c * Real.sqrt (n : ℝ) + 2) ^ 2) *
        ((1 : ℝ) / 2) ^ n)
      atTop (nhds 0) := by
  let q : ℝ := Real.exp (8 * A * c ^ 2) / 2
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq1 : q < 1 := by
    rw [div_lt_one (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_lt_exp.mpr hsmall
  have hupper (n : ℕ) :
      Real.exp (A * (2 * c * Real.sqrt (n : ℝ) + 2) ^ 2) *
          ((1 : ℝ) / 2) ^ n ≤
        Real.exp (8 * A) * q ^ n := by
    have hsqrt : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg n)
    have hsquare :
        (2 * c * Real.sqrt (n : ℝ) + 2) ^ 2 ≤
          8 * c ^ 2 * (n : ℝ) + 8 := by
      nlinarith [sq_nonneg (2 * c * Real.sqrt (n : ℝ) - 2)]
    calc
      Real.exp (A * (2 * c * Real.sqrt (n : ℝ) + 2) ^ 2) *
          ((1 : ℝ) / 2) ^ n ≤
        Real.exp (A * (8 * c ^ 2 * (n : ℝ) + 8)) *
          ((1 : ℝ) / 2) ^ n := by
            gcongr
      _ = Real.exp (8 * A) * q ^ n := by
        dsimp [q]
        simp only [div_pow, one_pow]
        rw [← Real.exp_nat_mul]
        have harg : A * (8 * c ^ 2 * (n : ℝ) + 8) =
            8 * A + (n : ℝ) * (8 * A * c ^ 2) := by
          ring
        rw [harg, Real.exp_add]
        ring
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards with n
    exact hupper n
  · simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul
        (Real.exp (8 * A))

/-- Every positive quadratic-growth constant admits a positive square-root
scale strictly below the Cauchy decay threshold. -/
theorem exists_pos_quadraticGrowth_sqrt_scale
    {A : ℝ} (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ 8 * A * c ^ 2 < Real.log 2 := by
  let c : ℝ := Real.sqrt (Real.log 2 / (16 * A))
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have harg : 0 < Real.log 2 / (16 * A) := by positivity
  refine ⟨c, Real.sqrt_pos.2 harg, ?_⟩
  dsimp [c]
  rw [Real.sq_sqrt harg.le]
  have hAne : A ≠ 0 := hA.ne'
  calc
    8 * A * (Real.log 2 / (16 * A)) = Real.log 2 / 2 := by
      field_simp
      ring
    _ < Real.log 2 := by linarith

/-- Spectral xi's order-`n` real Taylor polynomial converges uniformly on an
expanding disk of radius `c * sqrt n` for some explicit positive scale.  The
first conjunct records a geometric pointwise majorant; the second is its
uniform epsilon formulation over the entire stage-dependent disk. -/
theorem exists_riemannXiSpectral_taylor_expanding_sqrt_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ c : ℝ, 0 < c ∧
      (∀ {n : ℕ}, 1 ≤ n → ∀ {w : ℂ},
        ‖w‖ ≤ c * Real.sqrt (n : ℝ) →
        ‖((riemannXiSpectralRealTaylorPolynomial n).map
              Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤
          2 * (Real.exp
            (A * (2 * c * Real.sqrt (n : ℝ) + 2) ^ 2) *
              ((1 : ℝ) / 2) ^ n)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ w : ℂ,
        ‖w‖ ≤ c * Real.sqrt (n : ℝ) →
        ‖((riemannXiSpectralRealTaylorPolynomial n).map
              Complex.ofRealHom).eval w - riemannXiSpectral w‖ < ε := by
  obtain ⟨A, hA, htaylor⟩ :=
    exists_riemannXiSpectral_taylor_remainder_bound
  obtain ⟨c, hc, hsmall⟩ :=
    exists_pos_quadraticGrowth_sqrt_scale (lt_of_lt_of_le zero_lt_one hA)
  have hpoint {n : ℕ} (hn : 1 ≤ n) {w : ℂ}
      (hw : ‖w‖ ≤ c * Real.sqrt (n : ℝ)) :
      ‖((riemannXiSpectralRealTaylorPolynomial n).map
            Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤
        2 * (Real.exp
          (A * (2 * c * Real.sqrt (n : ℝ) + 2) ^ 2) *
            ((1 : ℝ) / 2) ^ n) := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    have houter : 0 < 2 * c * Real.sqrt (n : ℝ) := by positivity
    have hwouter : ‖w‖ < 2 * c * Real.sqrt (n : ℝ) := by
      calc
        ‖w‖ ≤ c * Real.sqrt (n : ℝ) := hw
        _ < 2 * c * Real.sqrt (n : ℝ) := by nlinarith
    have hraw := htaylor houter hwouter n
    let r : ℝ := ‖w‖ / (2 * c * Real.sqrt (n : ℝ))
    have hr0 : 0 ≤ r := by
      dsimp [r]
      positivity
    have hrhalf : r ≤ (1 : ℝ) / 2 := by
      dsimp [r]
      rw [div_le_iff₀ houter]
      nlinarith
    have hrlt : r < 1 := hrhalf.trans_lt (by norm_num)
    calc
      ‖((riemannXiSpectralRealTaylorPolynomial n).map
            Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤
          Real.exp
              (A * (2 * c * Real.sqrt (n : ℝ) + 2) ^ 2) *
            r ^ n / (1 - r) := by
              simpa only [r] using hraw
      _ ≤ (Real.exp
              (A * (2 * c * Real.sqrt (n : ℝ) + 2) ^ 2) *
            r ^ n) / ((1 : ℝ) / 2) := by
              apply div_le_div_of_nonneg_left
              · positivity
              · norm_num
              · linarith
      _ = 2 * (Real.exp
              (A * (2 * c * Real.sqrt (n : ℝ) + 2) ^ 2) *
            r ^ n) := by ring
      _ ≤ 2 * (Real.exp
              (A * (2 * c * Real.sqrt (n : ℝ) + 2) ^ 2) *
            ((1 : ℝ) / 2) ^ n) := by
              gcongr
  refine ⟨A, hA, c, hc, ?_, ?_⟩
  · intro n hn w hw
    exact hpoint hn hw
  · have hupper : Tendsto
        (fun n : ℕ ↦ 2 * (Real.exp
            (A * (2 * c * Real.sqrt (n : ℝ) + 2) ^ 2) *
              ((1 : ℝ) / 2) ^ n))
        atTop (nhds 0) := by
      simpa using
        (tendsto_quadraticGrowth_mul_half_pow
          (zero_le_one.trans hA) hsmall).const_mul 2
    intro ε hε
    have hevent : ∀ᶠ n : ℕ in atTop,
        2 * (Real.exp
            (A * (2 * c * Real.sqrt (n : ℝ) + 2) ^ 2) *
              ((1 : ℝ) / 2) ^ n) < ε :=
      (tendsto_order.1 hupper).2 ε hε
    filter_upwards [eventually_ge_atTop 1, hevent] with n hn hbound
    intro w hw
    exact (hpoint hn hw).trans_lt hbound

end

end RiemannGaussian

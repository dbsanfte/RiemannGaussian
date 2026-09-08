import RiemannGaussian.EtaGammaKernel

/-!
# The actual eta Mellin transform under gamma smoothing

Paired exponential prefixes converge to the Fermi kernel under a
summable Mellin dominator. This identifies the integral with the actual
paired eta function for every positive real part. At a genuine zeta
zero the full smoothed transform has an explicit cubic bound.
-/

open Complex Filter MeasureTheory Set
open scoped Classical Topology Interval ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaSmoothing

noncomputable section

/-- For a fixed smoothing parameter the full real transform is continuous in its Mellin variable. -/
theorem continuous_gammaTransform_left (x : ℝ) : Continuous (fun t ↦ gammaTransform t x) := by
  have h1 : Continuous fermiOne :=
    continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_fermiOne t).continuousAt
  have h2 : Continuous fermiTwo :=
    continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_fermiTwo t).continuousAt
  let hshift : Continuous (fun t : ℝ ↦ t + x) := continuous_id.add_const x
  exact ((continuous_fermi.comp hshift).sub ((h1.comp hshift).const_mul x)).add
    ((h2.comp hshift).const_mul (x ^ 2 / 2))

/-- The exact complex Mellin integrand of the retained cubic kernel correction. -/
def mellinRemainderKernel (s : ℂ) (x t : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) * ((gammaTransform t x - fermi t : ℝ) : ℂ)

/-- The complex Mellin remainder is continuous on its genuine positive integration domain. -/
theorem continuousOn_mellinRemainderKernel (s : ℂ) (x : ℝ) :
    ContinuousOn (mellinRemainderKernel s x) (Ioi 0) := by
  apply ContinuousOn.mul
  · apply continuousOn_of_forall_continuousAt
    intro t ht
    have hc : ContinuousAt (fun z : ℂ ↦ z ^ (s - 1)) (t : ℂ) :=
      continuousAt_cpow_const (ofReal_mem_slitPlane.mpr ht)
    exact hc.comp continuous_ofReal.continuousAt
  · exact (continuous_ofReal.comp ((continuous_gammaTransform_left x).sub continuous_fermi)).continuousOn

/-- The original Mellin phase is retained until its cubic kernel estimate is applied. -/
theorem norm_mellinRemainderKernel_le (s : ℂ) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    ‖mellinRemainderKernel s x t‖ ≤
      x ^ 3 / 6 * (Real.exp (-t) * t ^ (s.re - 1)) := by
  rw [mellinRemainderKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_cpow_eq_rpow_re_of_pos ht (s - 1)]
  simp only [Complex.sub_re, Complex.one_re]
  apply (mul_le_mul_of_nonneg_left (abs_gammaTransform_sub_le t hx)
    (Real.rpow_nonneg ht.le _)).trans_eq
  ring

/-- The complex cubic correction is genuinely integrable for every positive real part. -/
theorem integrableOn_mellinRemainderKernel {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (mellinRemainderKernel s x) (Ioi 0) := by
  apply ((Real.GammaIntegral_convergent hs).const_mul (x ^ 3 / 6)).mono'
    ((continuousOn_mellinRemainderKernel s x).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_mellinRemainderKernel_le s hx ht

/-- The full complex integral keeps the cubic rate after the original Mellin phase is integrated. -/
theorem norm_integral_mellinRemainderKernel_le {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖∫ t in Ioi (0 : ℝ), mellinRemainderKernel s x t‖ ≤ x ^ 3 / 6 * Real.Gamma s.re := by
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), x ^ 3 / 6 * (Real.exp (-t) * t ^ (s.re - 1)) := by
      apply norm_integral_le_of_norm_le ((Real.GammaIntegral_convergent hs).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_mellinRemainderKernel_le s hx ht
    _ = _ := by
      rw [integral_const_mul, ← Real.Gamma_eq_integral hs]

/-- The Gamma-normalized complex cubic Mellin remainder. -/
def mellinRemainder (s : ℂ) (x : ℝ) : ℂ :=
  (∫ t in Ioi (0 : ℝ), mellinRemainderKernel s x t) / Complex.Gamma s

/-- The actual Gamma normalization and the full cubic allowance remain explicit. -/
theorem norm_mellinRemainder_le {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖mellinRemainder s x‖ ≤ Real.Gamma s.re / (6 * ‖Complex.Gamma s‖) * x ^ 3 := by
  rw [mellinRemainder, norm_div]
  apply (div_le_div_of_nonneg_right (norm_integral_mellinRemainderKernel_le hs hx) (norm_nonneg _)).trans_eq
  ring

/-- A positive-real-part Mellin normalization has a strictly positive finite cubic coefficient. -/
theorem mellinRemainderConstant_pos {s : ℂ} (hs : 0 < s.re) :
    0 < Real.Gamma s.re / (6 * ‖Complex.Gamma s‖) := by
  have hG := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hs)
  exact div_pos (Real.Gamma_pos_of_pos hs) (by positivity)

/-- The literal positive-exponential term under the eta Mellin integral. -/
def mellinExponential (s : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) * (Real.exp (-(n : ℝ) * t) : ℂ)

/-- Each positive integer exponential term is integrable without relying on a conditionally summed integral. -/
theorem integrableOn_mellinExponential {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    IntegrableOn (mellinExponential s n) (Ioi 0) := by
  apply (Real.GammaIntegral_convergent hs).mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.mul
    · apply continuousOn_of_forall_continuousAt
      intro t ht
      have hc : ContinuousAt (fun z : ℂ ↦ z ^ (s - 1)) (t : ℂ) :=
        continuousAt_cpow_const (ofReal_mem_slitPlane.mpr ht)
      exact hc.comp continuous_ofReal.continuousAt
    · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [mellinExponential, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), norm_cpow_eq_rpow_re_of_pos ht (s - 1)]
    simp only [Complex.sub_re, Complex.one_re]
    rw [mul_comm (Real.exp (-t))]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (le_of_lt ht) _)
    apply Real.exp_le_exp.mpr
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have ht0 : 0 < t := ht
    nlinarith

/-- Integrating a literal positive exponential recovers its actual complex Dirichlet term and Gamma factor. -/
theorem integral_mellinExponential {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    (∫ t in Ioi (0 : ℝ), mellinExponential s n t) = Complex.Gamma s * (n : ℂ) ^ (-s) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hi := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hnR
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← neg_mul] at hi
  change (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (Real.exp (-(n : ℝ) * t) : ℂ)) = _
  rw [hi, one_div, Complex.inv_cpow_ofReal_nonneg hnR.le, ← Complex.cpow_neg]
  simp only [Complex.ofReal_natCast]
  exact mul_comm _ _

/-- A complete finite odd-even exponential prefix, expressed without a conditional infinite series. -/
def fermiPartial (N : ℕ) (t : ℝ) : ℝ := fermi t * (1 - (Real.exp (-t) ^ 2) ^ N)

private theorem fermi_pair_factor (t : ℝ) :
    fermi t * (1 - Real.exp (-t) ^ 2) = Real.exp (-t) - Real.exp (-t) ^ 2 := by
  rw [fermi, Real.exp_neg]
  field_simp
  ring

/-- The geometric finite kernel is exactly the original odd-even exponential prefix. -/
theorem sum_exponential_pairs_eq_fermiPartial (N : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.range N, (Real.exp (-t) ^ (2 * n + 1) - Real.exp (-t) ^ (2 * n + 2))) =
      fermiPartial N t := by
  induction N with
  | zero => simp [fermiPartial]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [fermiPartial, pow_add, pow_mul, pow_one]
    have h := fermi_pair_factor t
    linear_combination -((Real.exp (-t) ^ 2) ^ N) * h

/-- The complete finite exponential prefix is nonnegative and bounded by the full Fermi kernel. -/
theorem fermiPartial_bounds (N : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ fermiPartial N t ∧ fermiPartial N t ≤ fermi t := by
  have hE : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hEle : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp : 0 ≤ (Real.exp (-t) ^ 2) ^ N := by positivity
  have hp1 : (Real.exp (-t) ^ 2) ^ N ≤ 1 := pow_le_one₀ (by positivity) (pow_le_one₀ hE hEle)
  have hf := (fermi_bounds t).1.le
  unfold fermiPartial
  exact ⟨mul_nonneg hf (sub_nonneg.mpr hp1), by nlinarith⟩

/-- The complete finite exponential prefixes converge pointwise to the Fermi kernel on the positive axis. -/
theorem fermiPartial_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ ↦ fermiPartial N t) atTop (𝓝 (fermi t)) := by
  have hp : Real.exp (-t) ^ 2 < 1 := by
    have hE := Real.exp_pos (-t)
    have hE1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    nlinarith
  simpa only [fermiPartial, sub_zero, mul_one] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hp)).const_mul (fermi t)

/-- The finite Mellin prefixes retain the actual odd-even Dirichlet coefficients. -/
theorem integral_mellin_fermiPartial {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (fermiPartial N t : ℂ)) =
      Complex.Gamma s * RiemannGaussian.pairedEtaCorePartialSum N s := by
  have he (t : ℝ) : (t : ℂ) ^ (s - 1) * (fermiPartial N t : ℂ) =
      ∑ n ∈ Finset.range N, (mellinExponential s (2 * n + 1) t - mellinExponential s (2 * n + 2) t) := by
    rw [← sum_exponential_pairs_eq_fermiPartial, Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp only [Complex.ofReal_sub, mul_sub, mellinExponential, ← Real.exp_nat_mul, mul_neg, neg_mul]
  simp_rw [he]
  rw [integral_finsetSum (Finset.range N)
    (f := fun n t ↦ mellinExponential s (2 * n + 1) t - mellinExponential s (2 * n + 2) t)
    (fun n _ ↦ (integrableOn_mellinExponential hs (by omega : 1 ≤ 2 * n + 1)).sub
    (integrableOn_mellinExponential hs (by omega : 1 ≤ 2 * n + 2)))]
  rw [RiemannGaussian.pairedEtaCorePartialSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_sub (integrableOn_mellinExponential hs (by omega : 1 ≤ 2 * n + 1))
    (integrableOn_mellinExponential hs (by omega : 1 ≤ 2 * n + 2)),
    integral_mellinExponential hs (by omega : 1 ≤ 2 * n + 1),
    integral_mellinExponential hs (by omega : 1 ≤ 2 * n + 2)]
  simp only [RiemannGaussian.pairedEtaCoreSummand, Complex.ofReal_natCast]
  ring

/-- The original Fermi Mellin integrand, including its complete complex power. -/
def mellinFermi (s : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (s - 1) * (fermi t : ℂ)

private theorem continuousOn_mellin_mul (s : ℂ) {f : ℝ → ℝ} (hf : Continuous f) :
    ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) * (f t : ℂ)) (Ioi 0) := by
  apply ContinuousOn.mul
  · apply continuousOn_of_forall_continuousAt
    intro t ht
    have hc : ContinuousAt (fun z : ℂ ↦ z ^ (s - 1)) (t : ℂ) :=
      continuousAt_cpow_const (ofReal_mem_slitPlane.mpr ht)
    exact hc.comp continuous_ofReal.continuousAt
  · exact (continuous_ofReal.comp hf).continuousOn

/-- The original eta Mellin integral converges throughout the positive half-plane. -/
theorem integrableOn_mellinFermi {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (mellinFermi s) (Ioi 0) := by
  apply (Real.GammaIntegral_convergent hs).mono'
    ((continuousOn_mellin_mul s continuous_fermi).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (fermi_bounds t).1, norm_cpow_eq_rpow_re_of_pos ht (s - 1)]
  simp only [Complex.sub_re, Complex.one_re]
  exact (mul_le_mul_of_nonneg_left (fermi_le_exp_neg t) (Real.rpow_nonneg (le_of_lt ht) _)).trans_eq (mul_comm _ _)

/-- Dominated convergence transports the complete finite odd-even Mellin prefixes on the whole positive axis. -/
theorem integral_mellin_fermiPartial_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ ↦ ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (fermiPartial N t : ℂ))
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), mellinFermi s t)) := by
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ ↦ Real.exp (-t) * t ^ (s.re - 1))
  · intro N
    apply (continuousOn_mellin_mul s _).aestronglyMeasurable measurableSet_Ioi
    exact continuous_fermi.mul
      (continuous_const.sub (((continuous_neg.rexp).pow 2).pow N))
  · exact Real.GammaIntegral_convergent hs
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fermiPartial_bounds N ht).1, norm_cpow_eq_rpow_re_of_pos ht (s - 1)]
    simp only [Complex.sub_re, Complex.one_re]
    exact (mul_le_mul_of_nonneg_left ((fermiPartial_bounds N ht).2.trans (fermi_le_exp_neg t))
      (Real.rpow_nonneg (le_of_lt ht) _)).trans_eq (mul_comm _ _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ((continuous_ofReal.continuousAt.tendsto).comp (fermiPartial_tendsto ht)).const_mul _

/-- The genuine Fermi Mellin integral equals Gamma times the repository's actual eta core. -/
theorem integral_mellinFermi_eq_gamma_eta {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Ioi (0 : ℝ), mellinFermi s t) = Complex.Gamma s * RiemannGaussian.pairedEtaCore s := by
  have hi := integral_mellin_fermiPartial_tendsto hs
  simp_rw [integral_mellin_fermiPartial hs] at hi
  have heta := (RiemannGaussian.summable_pairedEtaCoreSummand hs).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hi (heta.const_mul (Complex.Gamma s))

/-- The full gamma-smoothed eta transform is defined by its genuine complex Mellin integral. -/
def smoothedEtaMellin (s : ℂ) (x : ℝ) : ℂ :=
  (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (gammaTransform t x : ℂ)) / Complex.Gamma s

/-- The full smoothed eta integrand is integrable, not just its cubic correction. -/
theorem integrableOn_smoothedEtaMellinKernel {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) * (gammaTransform t x : ℂ)) (Ioi 0) := by
  apply ((integrableOn_mellinFermi hs).add (integrableOn_mellinRemainderKernel hs hx)).congr_fun _ measurableSet_Ioi
  intro t _
  simp only [Pi.add_apply, mellinFermi, mellinRemainderKernel, Complex.ofReal_sub]
  ring

/-- The exact smoothed eta value retains its original eta core and its entire complex cubic correction. -/
theorem smoothedEtaMellin_eq_eta_add_remainder {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 ≤ x) :
    smoothedEtaMellin s x = RiemannGaussian.pairedEtaCore s + mellinRemainder s x := by
  have he (t : ℝ) : (t : ℂ) ^ (s - 1) * (gammaTransform t x : ℂ) =
      mellinFermi s t + mellinRemainderKernel s x t := by
    simp only [mellinFermi, mellinRemainderKernel, Complex.ofReal_sub]
    ring
  rw [smoothedEtaMellin]
  simp_rw [he]
  rw [integral_add (integrableOn_mellinFermi hs) (integrableOn_mellinRemainderKernel hs hx),
    add_div, integral_mellinFermi_eq_gamma_eta hs,
    mul_div_cancel_left₀ _ (Complex.Gamma_ne_zero_of_re_pos hs)]
  rfl

/-- At an actual nontrivial zero, the full smoothed eta Mellin transform has a checked cubic bound. -/
theorem norm_smoothedEtaMellin_at_zero_le (rho : RiemannGaussian.NontrivialZetaZero)
    {x : ℝ} (hx : 0 ≤ x) :
    ‖smoothedEtaMellin rho.1 x‖ ≤
      Real.Gamma rho.1.re / (6 * ‖Complex.Gamma rho.1‖) * x ^ 3 := by
  rw [smoothedEtaMellin_eq_eta_add_remainder (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho) hx,
    RiemannGaussian.pairedEtaCore_eq_zero_of_nontrivialZetaZero rho, zero_add]
  exact norm_mellinRemainder_le (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho) hx

end

end RiemannGaussian.EtaGammaSmoothing

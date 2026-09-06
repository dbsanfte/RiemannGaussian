import RiemannGaussian.ZetaLocalLogDerivative
import RiemannGaussian.EtaZetaStripDerivative

/-!
# The actual zeta pole and translated local divisor

The pole-removed local function keeps the exact logarithmic derivative of
zeta and its simple pole at one. The real-axis estimate retains the leading
coefficient one. Translation preserves the full multiplicity of every
actual nontrivial zero in the selected local disc.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Removing zeta's pole preserves nonvanishing on the closed right
half-plane, including the filled value at one. -/
theorem riemannZeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  by_cases h1 : s = 1
  · simp [h1, riemannZeta₁_one]
  · rw [riemannZeta₁_eq_sub_one_mul h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs)

/-- The actual logarithmic derivative splits off the simple pole at
one wherever zeta is regular and nonzero. -/
theorem neg_logDeriv_riemannZeta_eq_pole_sub {s : ℂ} (h1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    -logDeriv riemannZeta s = 1 / (s - 1) - logDeriv riemannZeta₁ s := by
  have hsub := sub_ne_zero.mpr h1
  have hnonzero : riemannZeta₁ s ≠ 0 := by
    rw [riemannZeta₁_eq_sub_one_mul h1]
    exact mul_ne_zero hsub hz
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add h1,
    riemannZeta_eq_inv_sub_mul h1]
  field_simp
  ring

/-- Translation to the safe-center disc retains the exact logarithmic
derivative, with derivative of the translation equal to one. -/
theorem logDeriv_localZetaPoleRemoved_eq (y : ℝ) (z : ℂ) :
    logDeriv (localZetaPoleRemoved y) z = logDeriv riemannZeta₁ (3 / 2 + I * y + z) := by
  have hd : HasDerivAt (localZetaPoleRemoved y) (deriv riemannZeta₁ (3 / 2 + I * y + z)) z := by
    change HasDerivAt (fun w : ℂ ↦ riemannZeta₁ (3 / 2 + I * y + w)) _ z
    simpa only [Function.comp_def, mul_one, id_eq] using
      (differentiable_riemannZeta₁ (3 / 2 + I * y + z)).hasDerivAt.comp z
        ((hasDerivAt_id z).const_add (3 / 2 + I * y))
  simp only [logDeriv_apply, hd.deriv, localZetaPoleRemoved]

/-- The real-axis pole estimate retains the sharp leading coefficient
one and gives an explicit bound for the pole-removed remainder. -/
theorem neg_logDeriv_riemannZeta_real_le {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 28224) :
    (-logDeriv riemannZeta ((1 + x : ℝ) : ℂ)).re ≤ 1 / x + 28224 := by
  have hxstrip : 1 + x ∈ Icc (3 / 4 : ℝ) (5 / 4) := by constructor <;> linarith
  have hdiff := norm_riemannZeta₁_sub_le_etaStrip_horizontal (u := 1) (v := 1 + x) 0
    (by constructor <;> norm_num) hxstrip
  have hclose : ‖riemannZeta₁ ((1 + x : ℝ) : ℂ) - 1‖ ≤ 14112 * x := by
    simpa [riemannZeta₁_one, abs_of_pos hx, show (32 : ℝ) * 21 ^ 2 = 14112 by norm_num] using hdiff
  have hfloor : 1 / 2 ≤ ‖riemannZeta₁ ((1 + x : ℝ) : ℂ)‖ := by
    have hn := norm_sub_norm_le (1 : ℂ) (riemannZeta₁ ((1 + x : ℝ) : ℂ))
    rw [norm_one, norm_sub_rev] at hn
    linarith
  have hbound : ‖deriv riemannZeta₁ ((1 + x : ℝ) : ℂ)‖ ≤ 14112 := by
    simpa [show (32 : ℝ) * 21 ^ 2 = 14112 by norm_num] using
      norm_deriv_riemannZeta₁_le_etaStrip (s := ((1 + x : ℝ) : ℂ))
      (by simpa using hxstrip.1) (by simpa using hxstrip.2)
  have hlogbound : ‖logDeriv riemannZeta₁ ((1 + x : ℝ) : ℂ)‖ ≤ 28224 := by
    rw [logDeriv_apply, norm_div, div_le_iff₀ (by linarith : 0 < ‖riemannZeta₁ ((1 + x : ℝ) : ℂ)‖)]
    linarith
  have hs : 1 < (((1 + x : ℝ) : ℂ)).re := by simpa using hx
  rw [neg_logDeriv_riemannZeta_eq_pole_sub (by intro h; have := congrArg Complex.re h; simp at this; linarith)
    (riemannZeta_ne_zero_of_one_le_re hs.le), Complex.sub_re]
  have hpole : (1 / ((((1 + x : ℝ) : ℂ)) - 1)).re = 1 / x := by
    norm_cast
    ring
  rw [hpole]
  linarith [(abs_le.mp (Complex.abs_re_le_norm (logDeriv riemannZeta₁ ((1 + x : ℝ) : ℂ)))).1]

/-- A complete local divisor point lies strictly to the left of the
line corresponding to `re s = 1`. -/
theorem localZetaDivisor_re_lt_neg_half (y : ℝ) {i : ℂ}
    (hi : divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i ≠ 0) :
    i.re < -(1 / 2 : ℝ) := by
  have hf := localZetaPoleRemoved_eq_zero_of_divisor_ne_zero y hi
  by_contra h
  have hs : 1 ≤ (3 / 2 + I * (y : ℂ) + i).re := by simp; linarith
  exact riemannZeta₁_ne_zero_of_one_le_re hs hf

/-- Removing the pole at one preserves the full genuine multiplicity
of each actual nontrivial zeta zero. -/
theorem meromorphicOrderAt_riemannZeta₁_nontrivialZero (rho : NontrivialZetaZero) :
    meromorphicOrderAt riemannZeta₁ rho.1 = (analyticZetaZeroMultiplicity rho : ℤ) := by
  obtain ⟨g, hg, hgne, he⟩ := riemannZeta₁_eventuallyEq_multiplicity_factor rho
  apply (meromorphicOrderAt_eq_int_iff ((differentiable_riemannZeta₁).analyticAt rho.1).meromorphicAt).mpr
  refine ⟨g, hg, hgne, ?_⟩
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with z hz
  simpa only [zpow_natCast, smul_eq_mul] using hz

/-- An actual zero near the right boundary is in its own translated
canonical disc. -/
theorem nontrivialZero_mem_localZetaCanonicalBall (rho : NontrivialZetaZero) (hrho : 3 / 4 ≤ rho.1.re) :
    ((rho.1.re - 3 / 2 : ℝ) : ℂ) ∈ ball 0 (localZetaCanonicalRadius rho.1.im) := by
  rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith [NontrivialZetaZero.re_lt_one rho])]
  linarith [(localZetaCanonicalRadius_spec rho.1.im).1]

/-- Translation retains exactly the full actual zero multiplicity in
the complete local divisor used by the signed pole sum. -/
theorem divisor_localZetaPoleRemoved_nontrivialZero (rho : NontrivialZetaZero) (hrho : 3 / 4 ≤ rho.1.re) :
    divisor (localZetaPoleRemoved rho.1.im) (ball 0 (localZetaCanonicalRadius rho.1.im))
      ((rho.1.re - 3 / 2 : ℝ) : ℂ) = (analyticZetaZeroMultiplicity rho : ℤ) := by
  have hmem := nontrivialZero_mem_localZetaCanonicalBall rho hrho
  rw [((analyticOnNhd_localZetaPoleRemoved_canonicalDisc rho.1.im).mono ball_subset_closedBall).meromorphicOn.divisor_apply hmem]
  have hf : localZetaPoleRemoved rho.1.im = riemannZeta₁ ∘ (· + (3 / 2 + I * (rho.1.im : ℂ))) := by
    funext z
    simp only [localZetaPoleRemoved, Function.comp_def, add_comm z]
  rw [hf, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  have he : ((rho.1.re - 3 / 2 : ℝ) : ℂ) + (3 / 2 + I * (rho.1.im : ℂ)) = rho.1 := by
    apply Complex.ext <;> simp
  rw [he, meromorphicOrderAt_riemannZeta₁_nontrivialZero]
  simp

end

end RiemannGaussian

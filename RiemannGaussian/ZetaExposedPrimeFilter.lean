/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSemiprimeDeletion
import RiemannGaussian.ZetaMoebiusFractionalBudgetAudit

/-!
# Constant prime filters at exposed zeros

Every other actual canonical zero mode lies strictly outside the exposed
source radius. A fixed polynomial vanishing at that source therefore has
vanishing normalized complete prime response without annihilating the
other zero modes or the pole. Exact polynomial linearity then proves that
the constant filter one retains the full negative multiplicity source.
The actual canonical divisor, pole, reflected modes and remainder remain.
-/

namespace RiemannGaussian.ZetaExposedPrimeFilter
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- At an exposed zero every other actual canonical divisor point is
strictly farther than the source radius, with no phase information lost. -/
theorem canonical_support_norm_gt_exposed {rho : NontrivialZetaZero}
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (r : Set.Ico (3 / 4 : ℝ) 1) {i : ℂ} (hi : i ∈ adaptiveZetaZeroSupport r rho.1.im)
    (hne : i ≠ ((rho.1.re - 3 / 2 : ℝ) : ℂ)) :
    3 / 2 - rho.1.re < ‖i‖ := by
  have hdiv := (mem_adaptiveZetaZeroSupport r rho.1.im i).mp hi
  have himem := (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
    (Metric.ball 0 (adaptiveZetaCanonicalRadius r rho.1.im))).supportWithinDomain hdiv
  have hiR : ‖i‖ < adaptiveZetaCanonicalRadius r rho.1.im := by
    simpa only [Metric.mem_ball, dist_zero_right] using himem
  have hi1 : ‖i‖ < 1 := hiR.trans (adaptiveZetaCanonicalRadius_spec r rho.1.im).2.1
  let s : ℂ := 3 / 2 + Complex.I * (rho.1.im : ℂ) + i
  have hspos : 0 < s.re := by
    simp only [s, Complex.add_re, Complex.mul_re, Complex.div_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num
    linarith [(abs_le.mp (Complex.abs_re_le_norm i)).1]
  have hs0 : riemannZeta₁ s = 0 := adaptiveZetaPoleRemoved_eq_zero_of_divisor_ne_zero r rho.1.im hdiv
  let tau : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hs0⟩
  have htau : tau ≠ rho := by
    intro hsame
    apply hne
    have hre := congrArg (fun tau : NontrivialZetaZero => tau.1.re) hsame
    have him := congrArg (fun tau : NontrivialZetaZero => tau.1.im) hsame
    change s.re = rho.1.re at hre
    change s.im = rho.1.im at him
    norm_num [s] at hre him
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      linarith
    · simp only [Complex.ofReal_im]
      linarith
  have he : (3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1 = -i := by
    change (3 / 2 + Complex.I * (rho.1.im : ℂ)) - s = -i
    dsimp [s]
    ring
  simpa only [he, norm_neg] using hexposed tau htau

/-- At an exposed zero a fixed filter vanishing on that one source
mode has vanishing normalized complete prime response. It need not kill
any other zero or the zeta pole exactly. -/
theorem tendsto_primeFilter_of_exposed_eval_zero (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (P : Polynomial ℂ) (hP : P.eval (((3 / 2 - rho.1.re : ℝ) : ℂ)⁻¹) = 0) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaPrimeLogFilter P N (3 / 2 + Complex.I * (rho.1.im : ℂ))) atTop (𝓝 0) := by
  let r := zetaRightHalfDiscParameter rho hrho
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hR : ‖(u : ℂ)‖ < adaptiveZetaCanonicalRadius r rho.1.im := by
    have hh := (adaptiveZetaCanonicalRadius_spec r rho.1.im).1
    change 5 / 4 - rho.1.re / 2 < _ at hh
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    dsimp [u]
    linarith
  have hres := tendsto_adaptiveZetaResidualFilter_mul_pow r rho.1.im P
    (by exact_mod_cast hu.ne' : (u : ℂ) ≠ 0) hR
  have href := tendsto_adaptiveZetaReflectedFilter_mul_pow r rho.1.im P hR
  have hpole : ‖(u : ℂ) * (1 / 2 + Complex.I * (rho.1.im : ℂ))⁻¹‖ < 1 := by
    have hy : 1 < ‖(1 / 2 + Complex.I * (rho.1.im : ℂ))‖ := by
      apply (nontrivialZetaZero_one_lt_abs_im rho).trans_le
      simpa using Complex.abs_im_le_norm (1 / 2 + Complex.I * (rho.1.im : ℂ))
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu,
      ← div_eq_mul_inv]
    exact (div_lt_one (by linarith)).mpr (hu1.trans hy)
  have hpol := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hpole).comp
    (tendsto_add_atTop_nat 1)).mul_const (P.eval (1 / 2 + Complex.I * (rho.1.im : ℂ))⁻¹)
  simp only [zero_mul] at hpol
  let d (i : ℂ) : ℂ := (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
    (Metric.ball 0 (adaptiveZetaCanonicalRadius r rho.1.im)) i : ℂ)
  have hterm (i : ℂ) (hi : i ∈ adaptiveZetaZeroSupport r rho.1.im) :
      Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
        (d i * ((-i⁻¹) ^ (N + 1) * P.eval (-i⁻¹)))) atTop (𝓝 0) := by
    by_cases he : i = ((rho.1.re - 3 / 2 : ℝ) : ℂ)
    · have hiu : i = -(u : ℂ) := by rw [he]; dsimp [u]; push_cast; ring
      have hzero : P.eval (-i⁻¹) = 0 := by
        rw [hiu, inv_neg, neg_neg]
        exact hP
      simpa only [hzero, mul_zero] using (tendsto_const_nhds :
        Tendsto (fun _N : ℕ => (0 : ℂ)) atTop (𝓝 0))
    · have hdist := canonical_support_norm_gt_exposed hexposed r hi he
      have hnorm : ‖(u : ℂ) * (-i⁻¹)‖ < 1 := by
        rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu,
          ← div_eq_mul_inv]
        exact (div_lt_one (hu.trans hdist)).mpr hdist
      have h := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm).comp
        (tendsto_add_atTop_nat 1)).const_mul (d i * P.eval (-i⁻¹))
      simp only [mul_zero] at h
      convert h using 1
      funext N
      simp only [Function.comp_def, mul_pow]
      ring
  have hsum := tendsto_finsetSum (adaptiveZetaZeroSupport r rho.1.im) hterm
  simp only [Finset.sum_const_zero] at hsum
  have h := ((hpol.sub hres).sub hsum).add href
  simp only [sub_zero, zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaPrimeLogFilter_eq_adaptive_modes r rho.1.im]
  simp only [adaptiveZetaReflectedFilter, Finset.mul_sum, mul_sub,
    Finset.sum_sub_distrib, Function.comp_def, mul_pow]
  dsimp only [d, u]
  ring

/-- Addition of fixed polynomial filters preserves the literal prime moments. -/
theorem primeLogFilter_add (P Q : Polynomial ℂ) (N : ℕ) (s : ℂ) :
    zetaPrimeLogFilter (P + Q) N s = zetaPrimeLogFilter P N s + zetaPrimeLogFilter Q N s := by
  simpa only [zetaPrimeLogFilter, Polynomial.sum] using
    Polynomial.sum_add_index P Q (fun k c => c * zetaPrimeLogMoment (N + k) s)
      (by intro k; simp only [zero_mul]) (by intro k a b; exact add_mul _ _ _)

/-- Subtraction of filters is an exact signed identity before any limit. -/
theorem primeLogFilter_sub (P Q : Polynomial ℂ) (N : ℕ) (s : ℂ) :
    zetaPrimeLogFilter (P - Q) N s = zetaPrimeLogFilter P N s - zetaPrimeLogFilter Q N s := by
  have h := primeLogFilter_add (P - Q) Q N s
  rw [sub_add_cancel] at h
  exact (eq_sub_iff_add_eq).mpr h.symm

/-- The unfiltered complete prime response itself recovers the negative
analytic multiplicity at exposed zeros. All other modes decay without
requiring an annihilating polynomial. -/
theorem tendsto_primeFilter_one_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaPrimeLogFilter 1 N (3 / 2 + Complex.I * (rho.1.im : ℂ))) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hQ : (1 - zetaRightHalfPoleJetFilter rho hrho).eval
      (((3 / 2 - rho.1.re : ℝ) : ℂ)⁻¹) = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_one, zetaRightHalfPoleJetFilter_eval_selected, sub_self]
  have hz := tendsto_primeFilter_of_exposed_eval_zero rho hrho hexposed
    (1 - zetaRightHalfPoleJetFilter rho hrho) hQ
  have h := hz.add (tendsto_zetaRightHalfPoleJetFilter rho hrho)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  rw [primeLogFilter_sub]
  ring

end
end RiemannGaussian.ZetaExposedPrimeFilter

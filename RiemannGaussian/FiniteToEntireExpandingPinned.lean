import RiemannGaussian.FiniteToEntireFastSeparable
import Mathlib.Analysis.Complex.Liouville

/-!
# Expanding-disk control for exact finite homotopy root pinning

The real Taylor polynomials for spectral xi converge on disks of radius
`c * sqrt n`, but the finite Hardy construction also requires an exact zero
of its homotopy polynomial.  The affine correction that pins this zero
depends on both the value and derivative errors at the limiting analytic
root.

This file derives a quantitative derivative estimate from the Cauchy formula,
propagates the geometric Taylor remainder through the homotopy expression,
and proves that the affine correction vanishes uniformly on the same
expanding disks.  Combining this with arbitrarily fast separable
perturbations produces an actual separable, exact-root sequence of degree at
most `max n 3` with expanding-disk convergence to spectral xi.  Under the
negation of RH, every member of the sequence carries the canonical finite
Hardy frontier at a common upper-half-plane root.
-/

open Filter Metric Polynomial Set
open scoped ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- A uniform value error on a circle controls the derivative error at its
center by the Cauchy estimate. -/
theorem norm_polynomial_derivative_sub_deriv_le_of_sphere_error
    (P : ℝ[X]) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {z : ℂ} {r C : ℝ} (hr : 0 < r)
    (herror : ∀ w ∈ sphere z r,
      ‖((P.map Complex.ofRealHom).eval w) - f w‖ ≤ C) :
    ‖((P.derivative.map Complex.ofRealHom).eval z) - deriv f z‖ ≤
      C / r := by
  let p : ℂ[X] := P.map Complex.ofRealHom
  let g : ℂ → ℂ := fun w ↦ p.eval w - f w
  have hg : Differentiable ℂ g := p.differentiable.sub hf
  have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hr hg.diffContOnCl (by
      intro w hw
      exact herror w hw)
  have hgderiv : HasDerivAt g
      (p.derivative.eval z - deriv f z) z :=
    (p.hasDerivAt z).sub (hf z).hasDerivAt
  rw [hgderiv.deriv] at hbound
  simpa only [p, Polynomial.derivative_map] using hbound

/-- The spectral-xi Taylor remainder on a fixed disk has a geometric bound
with ratio `1 / 2`. -/
theorem exists_riemannXiSpectral_taylor_fixedDisk_geometric_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {r : ℝ}, 0 < r → ∀ {N : ℕ} {w : ℂ},
      ‖w‖ ≤ r →
      ‖((riemannXiSpectralRealTaylorPolynomial N).map
            Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤
        2 * (Real.exp (A * (2 * r + 2) ^ 2) *
          ((1 : ℝ) / 2) ^ N) := by
  obtain ⟨A, hA, htaylor⟩ :=
    exists_riemannXiSpectral_taylor_remainder_bound
  refine ⟨A, hA, ?_⟩
  intro r hr N w hw
  have houter : 0 < 2 * r := by positivity
  have hwouter : ‖w‖ < 2 * r := lt_of_le_of_lt hw (by linarith)
  have hraw := htaylor houter hwouter N
  let q : ℝ := ‖w‖ / (2 * r)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqhalf : q ≤ (1 : ℝ) / 2 := by
    dsimp [q]
    rw [div_le_iff₀ houter]
    nlinarith
  have hqlt : q < 1 := hqhalf.trans_lt (by norm_num)
  calc
    ‖((riemannXiSpectralRealTaylorPolynomial N).map
          Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤
        Real.exp (A * (2 * r + 2) ^ 2) * q ^ N /
          (1 - q) := by
            simpa only [q] using hraw
    _ ≤ (Real.exp (A * (2 * r + 2) ^ 2) * q ^ N) /
          ((1 : ℝ) / 2) := by
            apply div_le_div_of_nonneg_left
            · positivity
            · norm_num
            · linarith
    _ = 2 * (Real.exp (A * (2 * r + 2) ^ 2) * q ^ N) := by
      ring
    _ ≤ 2 * (Real.exp (A * (2 * r + 2) ^ 2) *
          ((1 : ℝ) / 2) ^ N) := by
      gcongr

/-- Spectral xi and its derivative are simultaneously approximated at every
point by its real Taylor polynomials with an explicit geometric majorant. -/
theorem exists_riemannXiSpectral_taylor_value_derivative_geometric_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (z : ℂ) (N : ℕ),
      ‖((riemannXiSpectralRealTaylorPolynomial N).map
            Complex.ofRealHom).eval z - riemannXiSpectral z‖ ≤
          2 * (Real.exp (A * (2 * ‖z‖ + 4) ^ 2) *
            ((1 : ℝ) / 2) ^ N) ∧
      ‖((riemannXiSpectralRealTaylorPolynomial N).derivative.map
            Complex.ofRealHom).eval z - deriv riemannXiSpectral z‖ ≤
          2 * (Real.exp (A * (2 * ‖z‖ + 4) ^ 2) *
            ((1 : ℝ) / 2) ^ N) := by
  obtain ⟨A, hA, hfixed⟩ :=
    exists_riemannXiSpectral_taylor_fixedDisk_geometric_bound
  refine ⟨A, hA, ?_⟩
  intro z N
  constructor
  · simpa only [
        show 2 * (‖z‖ + 1) + 2 = 2 * ‖z‖ + 4 by ring] using
      hfixed (show 0 < ‖z‖ + 1 by positivity)
        (show ‖z‖ ≤ ‖z‖ + 1 by linarith)
  · let C : ℝ := 2 * (Real.exp (A * (2 * ‖z‖ + 4) ^ 2) *
      ((1 : ℝ) / 2) ^ N)
    have herror : ∀ w ∈ sphere z (1 : ℝ),
        ‖((riemannXiSpectralRealTaylorPolynomial N).map
            Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤ C := by
      intro w hw
      have hwsphere : ‖w - z‖ = 1 := by
        simpa [mem_sphere_iff_norm] using hw
      have hwnorm : ‖w‖ ≤ ‖z‖ + 1 := by
        calc
          ‖w‖ = ‖(w - z) + z‖ := by congr 1; ring
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ = ‖z‖ + 1 := by rw [hwsphere]; ring
      simpa only [C,
        show 2 * (‖z‖ + 1) + 2 = 2 * ‖z‖ + 4 by ring] using
        hfixed (show 0 < ‖z‖ + 1 by positivity) hwnorm
    have hder := norm_polynomial_derivative_sub_deriv_le_of_sphere_error
      (riemannXiSpectralRealTaylorPolynomial N)
      differentiable_riemannXiSpectral (z := z) (r := 1)
      (C := C) (by norm_num) herror
    simpa only [C, div_one] using hder

/-- The finite homotopy expression of the spectral-xi Taylor polynomial
converges geometrically to the analytic homotopy expression at every point. -/
theorem exists_riemannXiSpectral_taylor_finiteE_geometric_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (eta : ℝ) (z : ℂ) (N : ℕ),
      ‖(finiteEPolynomial (riemannXiSpectralRealTaylorPolynomial N) eta).eval z -
          analyticEValue riemannXiSpectral eta z‖ ≤
        (1 + |eta|) *
          (2 * (Real.exp (A * (2 * ‖z‖ + 4) ^ 2) *
            ((1 : ℝ) / 2) ^ N)) := by
  obtain ⟨A, hA, hboth⟩ :=
    exists_riemannXiSpectral_taylor_value_derivative_geometric_bound
  refine ⟨A, hA, ?_⟩
  intro eta z N
  let valueError : ℂ :=
    ((riemannXiSpectralRealTaylorPolynomial N).map
        Complex.ofRealHom).eval z - riemannXiSpectral z
  let derivativeError : ℂ :=
    ((riemannXiSpectralRealTaylorPolynomial N).derivative.map
        Complex.ofRealHom).eval z - deriv riemannXiSpectral z
  let C : ℝ := 2 * (Real.exp (A * (2 * ‖z‖ + 4) ^ 2) *
    ((1 : ℝ) / 2) ^ N)
  have hvalue : ‖valueError‖ ≤ C := (hboth z N).1
  have hderivative : ‖derivativeError‖ ≤ C := (hboth z N).2
  have hform :
      (finiteEPolynomial
          (riemannXiSpectralRealTaylorPolynomial N) eta).eval z -
          analyticEValue riemannXiSpectral eta z =
        valueError + Complex.I * (eta : ℂ) * derivativeError := by
    simp only [finiteEPolynomial_eval, analyticEValue, valueError,
      derivativeError, Polynomial.eval_map]
    ring
  rw [hform]
  calc
    ‖valueError + Complex.I * (eta : ℂ) * derivativeError‖ ≤
        ‖valueError‖ +
          ‖Complex.I * (eta : ℂ) * derivativeError‖ :=
      norm_add_le _ _
    _ = ‖valueError‖ + |eta| * ‖derivativeError‖ := by simp
    _ ≤ C + |eta| * C := by gcongr
    _ = (1 + |eta|) *
          (2 * (Real.exp (A * (2 * ‖z‖ + 4) ^ 2) *
            ((1 : ℝ) / 2) ^ N)) := by
      simp only [C]
      ring

/-- The slope of the affine exact-root correction is bounded by the finite
homotopy residual divided by its nondegenerate imaginary denominator. -/
theorem abs_finiteERootPinSlope_le_residual
    (A : ℝ[X]) (eta : ℝ) (z : ℂ) :
    |finiteERootPinSlope A eta z| ≤
      ‖(finiteEPolynomial A eta).eval z‖ / |z.im + eta| := by
  rw [finiteERootPinSlope, abs_div, abs_neg]
  gcongr
  exact Complex.abs_im_le_norm _

/-- The intercept of the affine exact-root correction is controlled by the
finite homotopy residual and the corresponding slope bound. -/
theorem abs_finiteERootPinIntercept_le_residual
    (A : ℝ[X]) (eta : ℝ) (z : ℂ) :
    |finiteERootPinIntercept A eta z| ≤
      ‖(finiteEPolynomial A eta).eval z‖ +
        (‖(finiteEPolynomial A eta).eval z‖ / |z.im + eta|) *
          |z.re| := by
  unfold finiteERootPinIntercept
  calc
    |-((finiteEPolynomial A eta).eval z).re -
        finiteERootPinSlope A eta z * z.re| ≤
      |-((finiteEPolynomial A eta).eval z).re| +
        |finiteERootPinSlope A eta z * z.re| := abs_sub _ _
    _ = |((finiteEPolynomial A eta).eval z).re| +
        |finiteERootPinSlope A eta z| * |z.re| := by
      rw [abs_neg, abs_mul]
    _ ≤ ‖(finiteEPolynomial A eta).eval z‖ +
        (‖(finiteEPolynomial A eta).eval z‖ / |z.im + eta|) *
          |z.re| := by
      gcongr
      · exact Complex.abs_re_le_norm _
      · exact abs_finiteERootPinSlope_le_residual A eta z

/-- Pointwise evaluation of the affine exact-root correction is controlled by
the finite homotopy residual and the evaluation radius. -/
theorem norm_finiteERootPinnedPolynomial_sub_le_residual
    (A : ℝ[X]) (eta : ℝ) (z w : ℂ) :
    ‖((finiteERootPinnedPolynomial A eta z).map
          Complex.ofRealHom).eval w -
        (A.map Complex.ofRealHom).eval w‖ ≤
      ‖(finiteEPolynomial A eta).eval z‖ +
        (‖(finiteEPolynomial A eta).eval z‖ / |z.im + eta|) *
          (|z.re| + ‖w‖) := by
  have hform :
      ((finiteERootPinnedPolynomial A eta z).map
            Complex.ofRealHom).eval w -
          (A.map Complex.ofRealHom).eval w =
        (finiteERootPinIntercept A eta z : ℂ) +
          (finiteERootPinSlope A eta z : ℂ) * w := by
    rw [finiteERootPinnedPolynomial_map_eval]
    ring
  rw [hform]
  calc
    ‖(finiteERootPinIntercept A eta z : ℂ) +
        (finiteERootPinSlope A eta z : ℂ) * w‖ ≤
      ‖(finiteERootPinIntercept A eta z : ℂ)‖ +
        ‖(finiteERootPinSlope A eta z : ℂ) * w‖ :=
      norm_add_le _ _
    _ = |finiteERootPinIntercept A eta z| +
        |finiteERootPinSlope A eta z| * ‖w‖ := by simp
    _ ≤ (‖(finiteEPolynomial A eta).eval z‖ +
          (‖(finiteEPolynomial A eta).eval z‖ / |z.im + eta|) *
            |z.re|) +
        (‖(finiteEPolynomial A eta).eval z‖ / |z.im + eta|) *
          ‖w‖ := by
      gcongr
      · exact abs_finiteERootPinIntercept_le_residual A eta z
      · exact abs_finiteERootPinSlope_le_residual A eta z
    _ = ‖(finiteEPolynomial A eta).eval z‖ +
        (‖(finiteEPolynomial A eta).eval z‖ / |z.im + eta|) *
          (|z.re| + ‖w‖) := by ring

/-- A geometric factor with ratio `1 / 2` dominates the expanding scale
`sqrt n`. -/
theorem tendsto_sqrt_nat_mul_half_pow :
    Tendsto
      (fun n : ℕ ↦ Real.sqrt (n : ℝ) * ((1 : ℝ) / 2) ^ n)
      atTop (nhds 0) := by
  apply squeeze_zero'
    (g := fun n : ℕ ↦ (n : ℝ) * ((1 : ℝ) / 2) ^ n)
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
  · exact tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)

/-- At a nondegenerate analytic homotopy root, exact affine root pinning of
the spectral-xi Taylor polynomials vanishes uniformly on every prescribed
positive `c * sqrt n` disk. -/
theorem riemannXiSpectral_taylor_pinning_preserves_expanding_sqrt
    {eta : ℝ} {z : ℂ}
    (hroot : analyticEValue riemannXiSpectral eta z = 0)
    (hden : z.im + eta ≠ 0) {c : ℝ} (hc : 0 < c) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ w : ℂ,
      ‖w‖ ≤ c * Real.sqrt (n : ℝ) →
      ‖((finiteERootPinnedPolynomial
            (riemannXiSpectralRealTaylorPolynomial n) eta z).map
              Complex.ofRealHom).eval w -
          ((riemannXiSpectralRealTaylorPolynomial n).map
              Complex.ofRealHom).eval w‖ < ε := by
  obtain ⟨A, hA, hE⟩ :=
    exists_riemannXiSpectral_taylor_finiteE_geometric_bound
  let K : ℝ := (1 + |eta|) * 2 *
    Real.exp (A * (2 * ‖z‖ + 4) ^ 2)
  let D : ℝ := |z.im + eta|
  have hD : 0 < D := abs_pos.2 hden
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hres (n : ℕ) :
      ‖(finiteEPolynomial
          (riemannXiSpectralRealTaylorPolynomial n) eta).eval z‖ ≤
        K * ((1 : ℝ) / 2) ^ n := by
    calc
      ‖(finiteEPolynomial
          (riemannXiSpectralRealTaylorPolynomial n) eta).eval z‖ =
        ‖(finiteEPolynomial
            (riemannXiSpectralRealTaylorPolynomial n) eta).eval z -
          analyticEValue riemannXiSpectral eta z‖ := by rw [hroot, sub_zero]
      _ ≤ (1 + |eta|) *
          (2 * (Real.exp (A * (2 * ‖z‖ + 4) ^ 2) *
            ((1 : ℝ) / 2) ^ n)) := hE eta z n
      _ = K * ((1 : ℝ) / 2) ^ n := by
        simp only [K]
        ring
  let U : ℕ → ℝ := fun n ↦
    K * ((1 : ℝ) / 2) ^ n +
      (K / D * |z.re|) * ((1 : ℝ) / 2) ^ n +
      (K / D * c) *
        (Real.sqrt (n : ℝ) * ((1 : ℝ) / 2) ^ n)
  have hU : Tendsto U atTop (nhds 0) := by
    have hp : Tendsto (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n)
        atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h1 := hp.const_mul K
    have h2 := hp.const_mul (K / D * |z.re|)
    have h3 := tendsto_sqrt_nat_mul_half_pow.const_mul (K / D * c)
    simpa only [U, mul_zero, add_zero] using (h1.add h2).add h3
  intro ε hε
  have hUevent : ∀ᶠ n : ℕ in atTop, U n < ε :=
    (tendsto_order.1 hU).2 ε hε
  filter_upwards [hUevent] with n hUn
  intro w hw
  have hpin := norm_finiteERootPinnedPolynomial_sub_le_residual
    (riemannXiSpectralRealTaylorPolynomial n) eta z w
  apply hpin.trans_lt
  calc
    ‖(finiteEPolynomial
          (riemannXiSpectralRealTaylorPolynomial n) eta).eval z‖ +
        (‖(finiteEPolynomial
          (riemannXiSpectralRealTaylorPolynomial n) eta).eval z‖ /
            |z.im + eta|) * (|z.re| + ‖w‖) ≤
      ‖(finiteEPolynomial
          (riemannXiSpectralRealTaylorPolynomial n) eta).eval z‖ +
        (‖(finiteEPolynomial
          (riemannXiSpectralRealTaylorPolynomial n) eta).eval z‖ /
            |z.im + eta|) *
          (|z.re| + c * Real.sqrt (n : ℝ)) := by
            apply add_le_add le_rfl
            apply mul_le_mul_of_nonneg_left
            · linarith
            · positivity
    _ ≤
      K * ((1 : ℝ) / 2) ^ n +
        (K * ((1 : ℝ) / 2) ^ n / D) *
          (|z.re| + c * Real.sqrt (n : ℝ)) := by
            apply add_le_add (hres n)
            apply mul_le_mul_of_nonneg_right
            · exact div_le_div_of_nonneg_right (hres n) (abs_nonneg _)
            · exact add_nonneg (abs_nonneg _)
                (mul_nonneg hc.le (Real.sqrt_nonneg _))
    _ = U n := by
      simp only [U, D]
      ring
    _ < ε := hUn

/-- A nondegenerate analytic homotopy root admits a sequence of exactly
root-pinned spectral-xi Taylor polynomials with local and `c * sqrt n`
expanding-disk convergence. -/
theorem exists_riemannXiSpectral_taylor_pinned_expanding_sqrt
    {eta : ℝ} {z : ℂ}
    (hroot : analyticEValue riemannXiSpectral eta z = 0)
    (hden : z.im + eta ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      TendstoLocallyUniformlyOn
        (fun n w ↦
          ((finiteERootPinnedPolynomial
            (riemannXiSpectralRealTaylorPolynomial n) eta z).map
              Complex.ofRealHom).eval w)
        riemannXiSpectral atTop Set.univ ∧
      (∀ n, (finiteEPolynomial
        (finiteERootPinnedPolynomial
          (riemannXiSpectralRealTaylorPolynomial n) eta z) eta).eval z = 0) ∧
      (∀ n, (finiteERootPinnedPolynomial
          (riemannXiSpectralRealTaylorPolynomial n) eta z).natDegree ≤
        max n 1) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ w : ℂ,
        ‖w‖ ≤ c * Real.sqrt (n : ℝ) →
        ‖((finiteERootPinnedPolynomial
              (riemannXiSpectralRealTaylorPolynomial n) eta z).map
                Complex.ofRealHom).eval w - riemannXiSpectral w‖ < ε := by
  obtain ⟨A, hA, c, hc, hTaylorPoint, hTaylorExpanding⟩ :=
    exists_riemannXiSpectral_taylor_expanding_sqrt_bound
  have hspec :=
    riemannXiSpectralRealTaylorPinnedPolynomial_spec eta hroot hden
  have hpinExpanding :=
    riemannXiSpectral_taylor_pinning_preserves_expanding_sqrt
      hroot hden hc
  refine ⟨c, hc, hspec.1, hspec.2, ?_, ?_⟩
  · intro n
    calc
      (finiteERootPinnedPolynomial
          (riemannXiSpectralRealTaylorPolynomial n) eta z).natDegree ≤
        max (riemannXiSpectralRealTaylorPolynomial n).natDegree 1 :=
          finiteERootPinnedPolynomial_natDegree_le _ _ _
      _ ≤ max n 1 := max_le_max
        (entireRealTaylorPolynomial_natDegree_le riemannXiSpectral n) le_rfl
  · intro ε hε
    have hpin := hpinExpanding (ε / 2) (by linarith)
    have hTaylor := hTaylorExpanding (ε / 2) (by linarith)
    filter_upwards [hpin, hTaylor] with n hpinn hTaylorn
    intro w hw
    have hpw := hpinn w hw
    have hTw := hTaylorn w hw
    calc
      ‖((finiteERootPinnedPolynomial
            (riemannXiSpectralRealTaylorPolynomial n) eta z).map
              Complex.ofRealHom).eval w - riemannXiSpectral w‖ =
        ‖(((finiteERootPinnedPolynomial
              (riemannXiSpectralRealTaylorPolynomial n) eta z).map
                Complex.ofRealHom).eval w -
            ((riemannXiSpectralRealTaylorPolynomial n).map
              Complex.ofRealHom).eval w) +
          (((riemannXiSpectralRealTaylorPolynomial n).map
              Complex.ofRealHom).eval w - riemannXiSpectral w)‖ := by
                congr 1
                ring
      _ ≤ ‖((finiteERootPinnedPolynomial
              (riemannXiSpectralRealTaylorPolynomial n) eta z).map
                Complex.ofRealHom).eval w -
            ((riemannXiSpectralRealTaylorPolynomial n).map
              Complex.ofRealHom).eval w‖ +
          ‖((riemannXiSpectralRealTaylorPolynomial n).map
              Complex.ofRealHom).eval w - riemannXiSpectral w‖ :=
        norm_add_le _ _
      _ < ε := by linarith

/-- A positive homotopy parameter and upper analytic root yield a separable,
exact-root polynomial sequence of degree at most `max n 3` which converges to
spectral xi both locally and uniformly on disks of radius `c * sqrt n`. -/
theorem exists_separable_riemannXiSpectral_finiteERoot_polynomial_sequence_with_expanding_sqrt
    {eta : ℝ} (heta : 0 < eta) {z : ℂ} (hz : 0 < z.im)
    (hroot : analyticEValue riemannXiSpectral eta z = 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ → ℝ[X],
      TendstoLocallyUniformlyOn
        (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
        riemannXiSpectral atTop Set.univ ∧
      (∀ n, (B n).Separable ∧
        (finiteEPolynomial (B n) eta).eval z = 0 ∧
        (B n).natDegree ≤ max n 3) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ w : ℂ,
        ‖w‖ ≤ c * Real.sqrt (n : ℝ) →
        ‖((B n).map Complex.ofRealHom).eval w -
          riemannXiSpectral w‖ < ε := by
  have hden : z.im + eta ≠ 0 := by linarith
  obtain ⟨c, hc, hAlimit, hAroot, hAdegree, hAexpanding⟩ :=
    exists_riemannXiSpectral_taylor_pinned_expanding_sqrt hroot hden
  let A : ℕ → ℝ[X] := fun n ↦
    finiteERootPinnedPolynomial
      (riemannXiSpectralRealTaylorPolynomial n) eta z
  obtain ⟨B, hBlimit, hB, hBexpanding⟩ :=
    exists_separable_finiteERoot_polynomial_sequence_preserving_expanding_convergence
      A heta hz hAlimit hAroot
        (fun n ↦ c * Real.sqrt (n : ℝ))
        (fun n ↦ mul_nonneg hc.le (Real.sqrt_nonneg _)) hAexpanding
  refine ⟨c, hc, B, hBlimit, ?_, hBexpanding⟩
  intro n
  refine ⟨(hB n).1, (hB n).2.1, ?_⟩
  calc
    (B n).natDegree ≤ max (A n).natDegree 3 := (hB n).2.2
    _ ≤ max (max n 1) 3 := max_le_max (hAdegree n) le_rfl
    _ = max n 3 := by omega

/-- If RH fails, a common upper-half-plane homotopy root supports a sequence
of canonical finite Hardy frontiers whose separable polynomials have degree
at most `max n 3` and converge to spectral xi on expanding `c * sqrt n`
disks. -/
theorem exists_expanding_canonicalFiniteHardyFrontier_sequence_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z ∧
          (B n).natDegree ≤ max n 3) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ w : ℂ,
          ‖w‖ ≤ c * Real.sqrt (n : ℝ) →
          ‖((B n).map Complex.ofRealHom).eval w -
            riemannXiSpectral w‖ < ε := by
  obtain ⟨eta, heta, z, hz, hroot⟩ :=
    exists_positive_riemannXiSpectral_analyticEValue_upper_root_of_not_rh hRH
  obtain ⟨c, hc, B, hBlimit, hB, hBexpanding⟩ :=
    exists_separable_riemannXiSpectral_finiteERoot_polynomial_sequence_with_expanding_sqrt
      heta hz hroot
  refine ⟨eta, heta, z, hz, c, hc, B, hBlimit, ?_, hBexpanding⟩
  intro n
  exact ⟨canonicalFiniteHardyFrontier_of_finiteE_root
    (hB n).1 heta hz (hB n).2.1, (hB n).2.2⟩

end

end RiemannGaussian

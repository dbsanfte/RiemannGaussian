import RiemannGaussian.FiniteToEntireRootPinning
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Real Taylor approximation of spectral xi

This file constructs explicit real-coefficient polynomial approximants for
any entire function which is real on the real axis.  It first turns the
partial sums of a complex formal power series with real coefficients into
literal polynomials in `ℝ[X]`.  It then proves that an entire function real
on `ℝ` has real derivatives of every order there, so its Cauchy/Taylor
coefficients at zero are real.

For the spectral xi function, conjugation symmetry is proved from the zeta
and Gamma-factor conjugation laws plus analytic continuation.  Consequently
the resulting real Taylor polynomials converge locally uniformly to spectral
xi.  Combining them with the affine construction from
`FiniteToEntireRootPinning` gives explicit real polynomials which retain that
limit and whose finite homotopies all contain a prescribed limiting
homotopy root exactly.
-/

open Filter Polynomial Set
open scoped ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- The first `N` coefficients of a complex formal power series, projected
to their real parts and assembled as a polynomial in `ℝ[X]`. -/
def realFormalPowerSeriesPartialPolynomial
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range N, C (p.coeff k).re * X ^ k

/-- If all formal-series coefficients are real, evaluation of the mapped
real partial polynomial is exactly the formal partial sum. -/
@[simp] theorem realFormalPowerSeriesPartialPolynomial_map_eval
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hreal : ∀ k, (p.coeff k).im = 0) (N : ℕ) (z : ℂ) :
    ((realFormalPowerSeriesPartialPolynomial p N).map
      Complex.ofRealHom).eval z = p.partialSum N z := by
  have hcoe (k : ℕ) : ((p.coeff k).re : ℂ) = p.coeff k := by
    apply Complex.ext
    · simp
    · simp [hreal]
  rw [realFormalPowerSeriesPartialPolynomial, Polynomial.map_sum,
    Polynomial.eval_finsetSum, FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp [hcoe, smul_eq_mul]
  ring

/-- A global formal power series with real coefficients yields locally
uniformly convergent real partial polynomials on the whole plane. -/
theorem realFormalPowerSeriesPartialPolynomial_tendstoLocallyUniformlyOn
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesOnBall f p 0 ⊤)
    (hreal : ∀ k, (p.coeff k).im = 0) :
    TendstoLocallyUniformlyOn
      (fun N z ↦ ((realFormalPowerSeriesPartialPolynomial p N).map
        Complex.ofRealHom).eval z)
      f atTop Set.univ := by
  have hpartial : TendstoLocallyUniformlyOn
      (fun N z ↦ p.partialSum N z) f atTop Set.univ := by
    simpa using hp.tendstoLocallyUniformlyOn'
  apply hpartial.congr
  intro N z _
  exact (realFormalPowerSeriesPartialPolynomial_map_eval p hreal N z).symm

/-- The complex derivative of an entire function real on the real axis is
again real at every real point. -/
theorem deriv_im_eq_zero_of_maps_real_to_real
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (x : ℝ) :
    (deriv f (x : ℂ)).im = 0 := by
  have hfder : HasDerivAt f (deriv f (x : ℂ)) (x : ℂ) :=
    (hf (x : ℂ)).hasDerivAt
  have hcomplex :
      HasDerivAt (fun y : ℝ ↦ f (y : ℂ)) (deriv f (x : ℂ)) x :=
    hfder.comp_ofReal
  have hofReal :
      HasDerivAt (fun y : ℝ ↦ ((f (y : ℂ)).re : ℂ))
        ((deriv f (x : ℂ)).re : ℂ) x :=
    hfder.real_of_complex.ofReal_comp
  have heq : (fun y : ℝ ↦ f (y : ℂ)) =
      fun y : ℝ ↦ ((f (y : ℂ)).re : ℂ) := by
    funext y
    apply Complex.ext
    · simp
    · simpa using hreal y
  have hderivEq :
      deriv f (x : ℂ) = ((deriv f (x : ℂ)).re : ℂ) := by
    apply hcomplex.unique
    rw [heq]
    exact hofReal
  simpa using congrArg Complex.im hderivEq

/-- Every iterated complex derivative of an entire function real on the
real axis is real at every real point. -/
theorem iteratedDeriv_im_eq_zero_of_maps_real_to_real
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) :
    ∀ n (x : ℝ), (iteratedDeriv n f (x : ℂ)).im = 0 := by
  intro n
  induction n with
  | zero =>
      intro x
      simpa only [iteratedDeriv_zero] using hreal x
  | succ n ih =>
      intro x
      rw [show n + 1 = n.succ by omega, iteratedDeriv_succ]
      apply deriv_im_eq_zero_of_maps_real_to_real
      · exact ContDiff.differentiable_iteratedDeriv' n hf.contDiff
      · exact ih

/-- Every coefficient of a global formal power series for an entire function
real on the real axis is real. -/
theorem formalPowerSeries_coeff_im_eq_zero_of_maps_real_to_real
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0)
    (hp : HasFPowerSeriesOnBall f p 0 ⊤) (n : ℕ) :
    (p.coeff n).im = 0 := by
  have hfac := hp.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at hfac
  simp only [Finset.prod_const_one, one_smul] at hfac
  have him := congrArg Complex.im hfac
  have hiter : (iteratedDeriv n f (0 : ℂ)).im = 0 := by
    simpa using
      iteratedDeriv_im_eq_zero_of_maps_real_to_real hf hreal n (0 : ℝ)
  rw [hiter] at him
  simp only [nsmul_eq_mul, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, zero_mul, add_zero] at him
  exact (mul_eq_zero.mp him).resolve_left (by
    exact_mod_cast n.factorial_ne_zero)

/-- The real Taylor polynomial of order `N` obtained from the global Cauchy
power series of `f` at zero. -/
def entireRealTaylorPolynomial (f : ℂ → ℂ) (N : ℕ) : ℝ[X] :=
  realFormalPowerSeriesPartialPolynomial
    (cauchyPowerSeries f 0 1) N

/-- The real Taylor polynomials of an entire function real on the real axis
converge to it locally uniformly on all of `ℂ`. -/
theorem entireRealTaylorPolynomial_tendstoLocallyUniformlyOn
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) :
    TendstoLocallyUniformlyOn
      (fun N z ↦ ((entireRealTaylorPolynomial f N).map
        Complex.ofRealHom).eval z)
      f atTop Set.univ := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    cauchyPowerSeries f 0 1
  have hp : HasFPowerSeriesOnBall f p 0 ⊤ :=
    hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)
  apply realFormalPowerSeriesPartialPolynomial_tendstoLocallyUniformlyOn hp
  intro n
  exact formalPowerSeries_coeff_im_eq_zero_of_maps_real_to_real
    hf hreal hp n

/-- The real Taylor approximants can be corrected without changing their
limit so that every finite homotopy contains a prescribed limiting root. -/
theorem entireRealTaylorPinnedPolynomial_spec
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0)
    (eta : ℝ) {z : ℂ} (hroot : analyticEValue f eta z = 0)
    (hz : z.im + eta ≠ 0) :
    TendstoLocallyUniformlyOn
        (fun N w ↦
          ((finiteERootPinnedPolynomial
            (entireRealTaylorPolynomial f N) eta z).map
              Complex.ofRealHom).eval w)
        f atTop Set.univ ∧
      ∀ N, (finiteEPolynomial
        (finiteERootPinnedPolynomial
          (entireRealTaylorPolynomial f N) eta z) eta).eval z = 0 := by
  exact finiteERootPinnedPolynomial_spec
    (entireRealTaylorPolynomial f) eta
    (entireRealTaylorPolynomial_tendstoLocallyUniformlyOn hf hreal)
    hroot hz

/-- Conjugation symmetry of the completed real Gamma factor. -/
@[simp] theorem Gammaℝ_conj (s : ℂ) :
    Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
  have hGamma : Complex.Gamma (conj s / 2) =
      conj (Complex.Gamma (s / 2)) := by
    simpa only [map_div₀, Complex.conj_ofNat] using
      Complex.Gamma_conj (s / 2)
  rw [hGamma]
  congr 1
  have harg : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)]
    exact ne_of_lt Real.pi_pos
  simpa only [map_div₀, map_neg, Complex.conj_ofNat,
    Complex.conj_ofReal] using
      Complex.cpow_conj (Real.pi : ℂ) (-s / 2) harg

/-- Conjugation symmetry of the pole-cleared entire xi normalization. -/
@[simp] theorem riemannXi_conj (s : ℂ) :
    riemannXi (conj s) = conj (riemannXi s) := by
  have hg_an : AnalyticOnNhd ℂ
      (fun z ↦ conj (riemannXi (conj z))) Set.univ :=
    DifferentiableOn.analyticOnNhd
      (fun z _ ↦ (differentiableAt_conj_conj_iff.mpr
        (differentiable_riemannXi (conj z))).differentiableWithinAt)
      isOpen_univ
  have hgz (z : ℂ) (hz : 1 < z.re) :
      conj (riemannXi (conj z)) = riemannXi z := by
    have hzconj : 1 < (conj z).re := by simpa
    rw [riemannXi_eq_mul_Gammaℝ_riemannZeta_of_one_lt_re hzconj,
      riemannXi_eq_mul_Gammaℝ_riemannZeta_of_one_lt_re hz]
    simp
  have heq : Set.EqOn (fun z ↦ conj (riemannXi (conj z)))
      riemannXi Set.univ :=
    hg_an.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_riemannXi isPreconnected_univ (mem_univ (2 : ℂ))
      (eventuallyEq_of_mem
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)) hgz)
  have h := congrArg conj (heq (mem_univ s))
  simpa using h

/-- The spectral xi function is even. -/
@[simp] theorem riemannXiSpectral_neg (z : ℂ) :
    riemannXiSpectral (-z) = riemannXiSpectral z := by
  unfold riemannXiSpectral
  rw [completedSpectralCoordinate_neg, riemannXi_one_sub]

/-- Conjugation symmetry of xi in the spectral coordinate. -/
@[simp] theorem riemannXiSpectral_conj (z : ℂ) :
    riemannXiSpectral (conj z) = conj (riemannXiSpectral z) := by
  have hcoord : completedSpectralCoordinate (-conj z) =
      conj (completedSpectralCoordinate z) := by
    unfold completedSpectralCoordinate
    apply Complex.ext
    · simp
    · simp
  calc
    riemannXiSpectral (conj z) = riemannXiSpectral (-conj z) := by
      rw [riemannXiSpectral_neg]
    _ = riemannXi (conj (completedSpectralCoordinate z)) := by
      rw [riemannXiSpectral, hcoord]
    _ = conj (riemannXi (completedSpectralCoordinate z)) :=
      riemannXi_conj _
    _ = conj (riemannXiSpectral z) := rfl

/-- Spectral xi is real-valued on the real axis. -/
theorem riemannXiSpectral_ofReal_im (x : ℝ) :
    (riemannXiSpectral (x : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  symm
  simpa using riemannXiSpectral_conj (x : ℂ)

/-- The explicit real Taylor polynomial sequence for spectral xi. -/
def riemannXiSpectralRealTaylorPolynomial (N : ℕ) : ℝ[X] :=
  entireRealTaylorPolynomial riemannXiSpectral N

/-- The real Taylor polynomials of spectral xi converge locally uniformly
to spectral xi on the whole complex plane. -/
theorem riemannXiSpectralRealTaylorPolynomial_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn
      (fun N z ↦ ((riemannXiSpectralRealTaylorPolynomial N).map
        Complex.ofRealHom).eval z)
      riemannXiSpectral atTop Set.univ := by
  exact entireRealTaylorPolynomial_tendstoLocallyUniformlyOn
    differentiable_riemannXiSpectral riemannXiSpectral_ofReal_im

/-- Given a root of the spectral-xi homotopy, the explicit real Taylor
approximants support vanishing affine corrections which preserve local uniform
convergence and put that exact root in every finite homotopy. -/
theorem riemannXiSpectralRealTaylorPinnedPolynomial_spec
    (eta : ℝ) {z : ℂ}
    (hroot : analyticEValue riemannXiSpectral eta z = 0)
    (hz : z.im + eta ≠ 0) :
    TendstoLocallyUniformlyOn
        (fun N w ↦
          ((finiteERootPinnedPolynomial
            (riemannXiSpectralRealTaylorPolynomial N) eta z).map
              Complex.ofRealHom).eval w)
        riemannXiSpectral atTop Set.univ ∧
      ∀ N, (finiteEPolynomial
        (finiteERootPinnedPolynomial
          (riemannXiSpectralRealTaylorPolynomial N) eta z) eta).eval z = 0 := by
  exact finiteERootPinnedPolynomial_spec
    riemannXiSpectralRealTaylorPolynomial eta
    riemannXiSpectralRealTaylorPolynomial_tendstoLocallyUniformlyOn
    hroot hz

end

end RiemannGaussian

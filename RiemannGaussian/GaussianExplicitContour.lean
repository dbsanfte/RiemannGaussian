import RiemannGaussian.GaussianCompletedLogDerivative

/-!
# Safe-line Gaussian contour identities

This file begins the analytic explicit-formula bridge on the line
`re s = 3 / 2`, where Mathlib's von Mangoldt Dirichlet series for
`-zeta'/zeta` converges absolutely.  The spectral coordinate of that line is
`u - I`.  Shifting the entire Gaussian to this line produces the factor
`exp x` which changes the Dirichlet weight `n^(-3/2)` into the certificate's
`n^(-1/2)` weight.
-/

namespace RiemannGaussian

noncomputable section

open MeasureTheory

lemma complexTranslatedGaussian_safeLine_mul_cexp_eq_quadratic
    (ε t x u : ℝ) :
    complexTranslatedGaussian ε t ((u : ℂ) - Complex.I) *
        Complex.exp (-Complex.I * (u : ℂ) * x) =
      Complex.exp
        (-((ε : ℂ)) * (u : ℂ) ^ 2 +
          (2 * (ε : ℂ) * ((t : ℂ) + Complex.I) -
            Complex.I * x) * u -
          (ε : ℂ) * ((t : ℂ) + Complex.I) ^ 2) := by
  rw [complexTranslatedGaussian, ← Complex.exp_add]
  congr 1
  ring

theorem integrable_complexTranslatedGaussian_safeLine_mul_cexp
    {ε : ℝ} (hε : 0 < ε) (t x : ℝ) :
    Integrable (fun u : ℝ =>
      complexTranslatedGaussian ε t ((u : ℂ) - Complex.I) *
        Complex.exp (-Complex.I * (u : ℂ) * x)) := by
  have hquad := integrable_cexp_quadratic
    (b := (ε : ℂ)) (by simpa using hε)
    (2 * (ε : ℂ) * ((t : ℂ) + Complex.I) - Complex.I * x)
    (-(ε : ℂ) * ((t : ℂ) + Complex.I) ^ 2)
  exact hquad.congr (Filter.Eventually.of_forall fun u =>
    (by
      dsimp only
      rw [complexTranslatedGaussian_safeLine_mul_cexp_eq_quadratic]
      congr 1
      ring))

/-- Exact Fourier transform of a translated entire Gaussian on the safe
spectral line `u - I`. -/
theorem integral_complexTranslatedGaussian_safeLine_mul_cexp
    {ε : ℝ} (hε : 0 < ε) (t x : ℝ) :
    (∫ u : ℝ,
      complexTranslatedGaussian ε t ((u : ℂ) - Complex.I) *
        Complex.exp (-Complex.I * (u : ℂ) * x)) =
      (Real.sqrt (Real.pi / ε) : ℂ) *
        Complex.exp
          ((x - x ^ 2 / (4 * ε) : ℝ) -
            Complex.I * (t * x)) := by
  have hεne : ε ≠ 0 := hε.ne'
  rw [integral_congr_ae (Filter.Eventually.of_forall fun u =>
    complexTranslatedGaussian_safeLine_mul_cexp_eq_quadratic ε t x u)]
  rw [show
    (fun u : ℝ => Complex.exp
      (-((ε : ℂ)) * (u : ℂ) ^ 2 +
        (2 * (ε : ℂ) * ((t : ℂ) + Complex.I) -
          Complex.I * x) * u -
        (ε : ℂ) * ((t : ℂ) + Complex.I) ^ 2)) =
    fun u : ℝ => Complex.exp
      ((-(ε : ℂ)) * (u : ℂ) ^ 2 +
        (2 * (ε : ℂ) * ((t : ℂ) + Complex.I) -
          Complex.I * x) * u +
        (-(ε : ℂ)) * ((t : ℂ) + Complex.I) ^ 2) by
      funext u
      congr 1
      ring]
  rw [integral_cexp_quadratic
    (b := (-ε : ℂ)) (by simpa using neg_lt_zero.mpr hε)
    (2 * (ε : ℂ) * ((t : ℂ) + Complex.I) - Complex.I * x)
    (-(ε : ℂ) * ((t : ℂ) + Complex.I) ^ 2)]
  have hsqrt :
      (Real.sqrt (Real.pi / ε) : ℂ) =
        ((Real.pi / ε : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa using Complex.ofReal_cpow
      (div_nonneg Real.pi_pos.le hε.le) (1 / 2 : ℝ)
  have hbase :
      (((Real.pi : ℂ) / -(-(ε : ℂ))) : ℂ) ^ (1 / 2 : ℂ) =
        (Real.sqrt (Real.pi / ε) : ℂ) := by
    rw [hsqrt]
    congr 2
    push_cast
    field_simp [hεne]
  have hexponent :
      -(ε : ℂ) * ((t : ℂ) + Complex.I) ^ 2 -
          (2 * (ε : ℂ) * ((t : ℂ) + Complex.I) -
            Complex.I * x) ^ 2 /
            (4 * (-((ε : ℂ)))) =
        ((x - x ^ 2 / (4 * ε) : ℝ) : ℂ) -
          Complex.I * (t * x) := by
    have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hεne
    push_cast
    field_simp [hεc]
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [hbase, hexponent]

/-- The even Gaussian produces exactly the real cosine weight occurring in
the prime-power term of the certificate. -/
theorem integral_complexSymmetricGaussian_safeLine_mul_cexp
    {ε : ℝ} (hε : 0 < ε) (t x : ℝ) :
    (∫ u : ℝ,
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        Complex.exp (-Complex.I * (u : ℂ) * x)) =
      (2 * Real.sqrt (Real.pi / ε) *
        Real.exp (x - x ^ 2 / (4 * ε)) * Real.cos (t * x) : ℝ) := by
  have hfirst :=
    integrable_complexTranslatedGaussian_safeLine_mul_cexp hε t x
  have hsecond :=
    integrable_complexTranslatedGaussian_safeLine_mul_cexp hε (-t) x
  rw [show
    (fun u : ℝ =>
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        Complex.exp (-Complex.I * (u : ℂ) * x)) =
      fun u : ℝ =>
        complexTranslatedGaussian ε t ((u : ℂ) - Complex.I) *
            Complex.exp (-Complex.I * (u : ℂ) * x) +
          complexTranslatedGaussian ε (-t) ((u : ℂ) - Complex.I) *
            Complex.exp (-Complex.I * (u : ℂ) * x) by
      funext u
      unfold complexSymmetricGaussian
      ring]
  rw [integral_add hfirst hsecond,
    integral_complexTranslatedGaussian_safeLine_mul_cexp hε t x,
    integral_complexTranslatedGaussian_safeLine_mul_cexp hε (-t) x]
  let A : ℝ := x - x ^ 2 / (4 * ε)
  have hminus :
      ((A : ℝ) : ℂ) - Complex.I * (t * x) =
        (A : ℂ) + ((-(t * x) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hplus :
      ((A : ℝ) : ℂ) - Complex.I *
          (((-t : ℝ) : ℂ) * (x : ℂ)) =
        (A : ℂ) + ((t * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [show x - x ^ 2 / (4 * ε) = A by rfl]
  rw [hminus, hplus, Complex.exp_add, Complex.exp_add,
    Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

theorem integrable_complexSymmetricGaussian_safeLine_mul_cexp
    {ε : ℝ} (hε : 0 < ε) (t x : ℝ) :
    Integrable (fun u : ℝ =>
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        Complex.exp (-Complex.I * (u : ℂ) * x)) := by
  have hfirst :=
    integrable_complexTranslatedGaussian_safeLine_mul_cexp hε t x
  have hsecond :=
    integrable_complexTranslatedGaussian_safeLine_mul_cexp hε (-t) x
  rw [show
    (fun u : ℝ =>
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        Complex.exp (-Complex.I * (u : ℂ) * x)) =
      fun u : ℝ =>
        complexTranslatedGaussian ε t ((u : ℂ) - Complex.I) *
            Complex.exp (-Complex.I * (u : ℂ) * x) +
          complexTranslatedGaussian ε (-t) ((u : ℂ) - Complex.I) *
            Complex.exp (-Complex.I * (u : ℂ) * x) by
      funext u
      unfold complexSymmetricGaussian
      ring]
  exact hfirst.add hsecond

/-- On `re s = 3/2`, an individual L-series term separates into a fixed
Dirichlet coefficient and a pure Fourier character. -/
theorem vonMangoldt_LSeriesTerm_safeLine
    {n : ℕ} (hn : n ≠ 0) (u : ℝ) :
    LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        (3 / 2 + Complex.I * (u : ℂ)) n =
      ((ArithmeticFunction.vonMangoldt n *
        Real.exp (-(3 / 2 : ℝ) * Real.log n) : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (u : ℂ) * Real.log n) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hncast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv,
    Complex.cpow_def_of_ne_zero hnc, ← Complex.exp_neg]
  rw [hncast, ← Complex.ofReal_log hnpos.le]
  rw [show
    -((Real.log n : ℂ) *
      (3 / 2 + Complex.I * (u : ℂ))) =
      ((-(3 / 2 : ℝ) * Real.log n : ℝ) : ℂ) +
        (-Complex.I * (u : ℂ) * Real.log n) by
      push_cast
      ring]
  rw [Complex.exp_add, ← Complex.ofReal_exp]
  push_cast
  ring

/-- Term-by-term, the safe-line contour integral is precisely the Gaussian
prime-power summand, with its full normalization. -/
theorem integral_complexSymmetricGaussian_mul_vonMangoldt_LSeriesTerm
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) (n : ℕ) :
    (∫ u : ℝ,
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        LSeries.term
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          (3 / 2 + Complex.I * (u : ℂ)) n) =
      (2 * Real.sqrt (Real.pi / ε) *
        gaussianPrimeSummand ε t n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [gaussianPrimeSummand]
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  let C : ℝ := ArithmeticFunction.vonMangoldt n *
    Real.exp (-(3 / 2 : ℝ) * Real.log n)
  rw [integral_congr_ae (Filter.Eventually.of_forall fun u => by
    rw [vonMangoldt_LSeriesTerm_safeLine hn])]
  change
    (∫ u : ℝ,
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        ((C : ℂ) *
          Complex.exp (-Complex.I * (u : ℂ) * Real.log n))) = _
  rw [show
    (fun u : ℝ =>
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        ((C : ℂ) *
          Complex.exp (-Complex.I * (u : ℂ) * Real.log n))) =
      fun u : ℝ => (C : ℂ) *
        (complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
          Complex.exp (-Complex.I * (u : ℂ) * Real.log n)) by
      funext u
      ring]
  rw [integral_const_mul,
    integral_complexSymmetricGaussian_safeLine_mul_cexp hε t (Real.log n)]
  have hInvSqrt :
      Real.exp (-(1 / 2 : ℝ) * Real.log n) =
        1 / Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnpos]
    rw [eq_div_iff (Real.exp_ne_zero _), ← Real.exp_add]
    simp only [Real.exp_eq_one_iff]
    ring
  have hweight :
      Real.exp (-(3 / 2 : ℝ) * Real.log n) *
          Real.exp (Real.log n - (Real.log n) ^ 2 / (4 * ε)) =
        1 / Real.sqrt n *
          Real.exp (-(Real.log n) ^ 2 / (4 * ε)) := by
    rw [← Real.exp_add]
    rw [show
      -(3 / 2 : ℝ) * Real.log n +
          (Real.log n - (Real.log n) ^ 2 / (4 * ε)) =
        -(1 / 2 : ℝ) * Real.log n +
          (-(Real.log n) ^ 2 / (4 * ε)) by ring]
    rw [Real.exp_add, hInvSqrt]
  unfold C gaussianPrimeSummand
  norm_cast
  calc
    ArithmeticFunction.vonMangoldt n *
          Real.exp (-(3 / 2 : ℝ) * Real.log n) *
        (2 * Real.sqrt (Real.pi / ε) *
          Real.exp (Real.log n - (Real.log n) ^ 2 / (4 * ε)) *
            Real.cos (t * Real.log n)) =
        2 * Real.sqrt (Real.pi / ε) *
          ArithmeticFunction.vonMangoldt n *
            (Real.exp (-(3 / 2 : ℝ) * Real.log n) *
              Real.exp (Real.log n - (Real.log n) ^ 2 / (4 * ε))) *
                Real.cos (t * Real.log n) := by ring
    _ = 2 * Real.sqrt (Real.pi / ε) *
          ArithmeticFunction.vonMangoldt n *
            (1 / Real.sqrt n *
              Real.exp (-(Real.log n) ^ 2 / (4 * ε))) *
                Real.cos (t * Real.log n) := by rw [hweight]
    _ = 2 * Real.sqrt (Real.pi / ε) *
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          Real.exp (-(Real.log n) ^ 2 / (4 * ε)) *
            Real.cos (t * Real.log n)) := by ring

/-- Every individual safe-line von Mangoldt term is integrable against the
even entire Gaussian. -/
theorem integrable_complexSymmetricGaussian_mul_vonMangoldt_LSeriesTerm
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) (n : ℕ) :
    Integrable (fun u : ℝ =>
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        LSeries.term
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          (3 / 2 + Complex.I * (u : ℂ)) n) := by
  by_cases hn : n = 0
  · subst n
    simp
  let C : ℂ := ArithmeticFunction.vonMangoldt n *
    Real.exp (-(3 / 2 : ℝ) * Real.log n)
  have hbase :=
    integrable_complexSymmetricGaussian_safeLine_mul_cexp
      hε t (Real.log n)
  have hscaled : Integrable (fun u : ℝ => C *
      (complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        Complex.exp (-Complex.I * (u : ℂ) * Real.log n))) :=
    hbase.const_mul C
  exact hscaled.congr (Filter.Eventually.of_forall fun u => by
    dsimp only
    rw [vonMangoldt_LSeriesTerm_safeLine hn]
    unfold C
    push_cast
    ring)

lemma norm_vonMangoldt_LSeriesTerm_safeLine (u : ℝ) (n : ℕ) :
    ‖LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        (3 / 2 + Complex.I * (u : ℂ)) n‖ =
      ‖LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        (3 / 2 : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  congr 1
  simp

theorem integrable_complexSymmetricGaussian_safeLine
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun u : ℝ =>
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I)) := by
  simpa using
    (integrable_complexSymmetricGaussian_safeLine_mul_cexp hε t 0)

/-- The absolute integrals of the safe-line Dirichlet terms form a
summable series.  This is the Fubini hypothesis needed below. -/
theorem summable_integral_norm_complexSymmetricGaussian_mul_vonMangoldtTerm
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Summable (fun n : ℕ => ∫ u : ℝ,
      ‖complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        LSeries.term
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          (3 / 2 + Complex.I * (u : ℂ)) n‖) := by
  have hL := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (3 / 2 : ℂ)) (by norm_num)
  have hH := integrable_complexSymmetricGaussian_safeLine hε t
  let A : ℝ := ∫ u : ℝ,
    ‖complexSymmetricGaussian ε t ((u : ℂ) - Complex.I)‖
  have hsummable : Summable (fun n : ℕ => A *
      ‖LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        (3 / 2 : ℂ) n‖) := hL.norm.mul_left A
  refine hsummable.congr fun n => ?_
  rw [show A = ∫ u : ℝ,
      ‖complexSymmetricGaussian ε t ((u : ℂ) - Complex.I)‖ by rfl]
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    dsimp only
    rw [norm_mul, norm_vonMangoldt_LSeriesTerm_safeLine]

/-- The full safe-line von Mangoldt L-series is absolutely integrable
against the translated Gaussian.  This is the integrability statement
behind the termwise Fubini identity below. -/
theorem integrable_complexSymmetricGaussian_mul_vonMangoldt_LSeries
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun u : ℝ =>
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        LSeries
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          (3 / 2 + Complex.I * (u : ℂ))) := by
  let F := fun n : ℕ => fun u : ℝ =>
    complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
      LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        (3 / 2 + Complex.I * (u : ℂ)) n
  let C : ℝ := ∑' n : ℕ,
    ‖LSeries.term
      (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
      (3 / 2 : ℂ) n‖
  have hL := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (3 / 2 : ℂ)) (by norm_num)
  have hLnorm : Summable (fun n : ℕ =>
      ‖LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        (3 / 2 : ℂ) n‖) := hL.norm
  have hFint : ∀ n : ℕ, Integrable (F n) := by
    intro n
    exact integrable_complexSymmetricGaussian_mul_vonMangoldt_LSeriesTerm
      hε t n
  have hmajorant : Integrable (fun u : ℝ =>
      ‖complexSymmetricGaussian ε t ((u : ℂ) - Complex.I)‖ * C) :=
    (integrable_complexSymmetricGaussian_safeLine hε t).norm.mul_const C
  have htsum : Integrable (fun u : ℝ => ∑' n : ℕ, F n u) := by
    refine hmajorant.mono' (AEStronglyMeasurable.tsum fun n =>
      (hFint n).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun u => by
      have hsumNorm : Summable (fun n : ℕ => ‖F n u‖) := by
        refine hLnorm.mul_left
          ‖complexSymmetricGaussian ε t ((u : ℂ) - Complex.I)‖ |>.congr ?_
        intro n
        unfold F
        rw [norm_mul, norm_vonMangoldt_LSeriesTerm_safeLine]
      calc
        ‖∑' n : ℕ, F n u‖ ≤ ∑' n : ℕ, ‖F n u‖ :=
          norm_tsum_le_tsum_norm hsumNorm
        _ = ‖complexSymmetricGaussian ε t ((u : ℂ) - Complex.I)‖ * C := by
          unfold F C
          simp_rw [norm_mul, norm_vonMangoldt_LSeriesTerm_safeLine]
          exact tsum_mul_left
  exact htsum.congr (Filter.Eventually.of_forall fun u => by
    unfold F LSeries
    exact tsum_mul_left)

/-- The full absolutely convergent von Mangoldt L-series on `re s = 3/2`
integrates to exactly the Gaussian prime-power sum. -/
theorem integral_complexSymmetricGaussian_mul_vonMangoldt_LSeries
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ u : ℝ,
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        LSeries
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          (3 / 2 + Complex.I * (u : ℂ))) =
      (2 * Real.sqrt (Real.pi / ε) * gaussianPrimeSum ε t : ℝ) := by
  let F := fun n : ℕ => fun u : ℝ =>
    complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
      LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        (3 / 2 + Complex.I * (u : ℂ)) n
  have hFint : ∀ n : ℕ, Integrable (F n) := by
    intro n
    exact integrable_complexSymmetricGaussian_mul_vonMangoldt_LSeriesTerm
      hε t n
  have hFnorm : Summable (fun n : ℕ => ∫ u : ℝ, ‖F n u‖) := by
    simpa only [F] using
      summable_integral_norm_complexSymmetricGaussian_mul_vonMangoldtTerm
        hε t
  have hinterchange :
      (∑' n : ℕ, ∫ u : ℝ, F n u) =
        ∫ u : ℝ, ∑' n : ℕ, F n u :=
    integral_tsum_of_summable_integral_norm hFint hFnorm
  calc
    (∫ u : ℝ,
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        LSeries
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          (3 / 2 + Complex.I * (u : ℂ))) =
        ∫ u : ℝ, ∑' n : ℕ, F n u := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        unfold F LSeries
        exact tsum_mul_left.symm
    _ = ∑' n : ℕ, ∫ u : ℝ, F n u := hinterchange.symm
    _ = ∑' n : ℕ,
        ((2 * Real.sqrt (Real.pi / ε) *
          gaussianPrimeSummand ε t n : ℝ) : ℂ) := by
      apply tsum_congr
      intro n
      unfold F
      exact
        integral_complexSymmetricGaussian_mul_vonMangoldt_LSeriesTerm
          hε t n
    _ = (2 * Real.sqrt (Real.pi / ε) * gaussianPrimeSum ε t : ℝ) := by
      push_cast
      rw [tsum_mul_left]
      rw [gaussianPrimeSum, Complex.ofReal_tsum]

/-- The safe-line negative logarithmic derivative of zeta is absolutely
integrable against the translated Gaussian. -/
theorem integrable_complexSymmetricGaussian_mul_negLogDeriv_riemannZeta
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun u : ℝ =>
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        (-deriv riemannZeta
            (3 / 2 + Complex.I * (u : ℂ)) /
          riemannZeta (3 / 2 + Complex.I * (u : ℂ)))) := by
  refine (integrable_complexSymmetricGaussian_mul_vonMangoldt_LSeries
    hε t).congr (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (by norm_num)]

/-- Mathlib identifies the safe-line von Mangoldt series with the negative
logarithmic derivative of the Riemann zeta function. -/
theorem integral_complexSymmetricGaussian_mul_negLogDeriv_riemannZeta
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ u : ℝ,
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        (-deriv riemannZeta
            (3 / 2 + Complex.I * (u : ℂ)) /
          riemannZeta (3 / 2 + Complex.I * (u : ℂ)))) =
      (2 * Real.sqrt (Real.pi / ε) * gaussianPrimeSum ε t : ℝ) := by
  calc
    (∫ u : ℝ,
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        (-deriv riemannZeta
            (3 / 2 + Complex.I * (u : ℂ)) /
          riemannZeta (3 / 2 + Complex.I * (u : ℂ)))) =
        ∫ u : ℝ,
          complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
            LSeries
              (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
              (3 / 2 + Complex.I * (u : ℂ)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        dsimp only
        rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
          (by norm_num)]
    _ = (2 * Real.sqrt (Real.pi / ε) * gaussianPrimeSum ε t : ℝ) :=
      integral_complexSymmetricGaussian_mul_vonMangoldt_LSeries hε t

lemma gaussianPrime_safeLine_normalization
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    2 * Real.sqrt (Real.pi / ε) * gaussianPrimeSum ε t =
      Real.pi * gaussianPrimeContribution ε t := by
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hsqrtε : Real.sqrt ε ≠ 0 :=
    (Real.sqrt_pos.2 hε).ne'
  have hsqrtPiSq : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt hpi
  unfold gaussianPrimeContribution
  rw [Real.sqrt_div hpi, Real.sqrt_mul hpi]
  field_simp [hsqrtPi, hsqrtε]
  rw [hsqrtPiSq]
  ring

/-- In the certificate normalization, the safe-line prime contour is
`pi` times the Gaussian prime contribution. -/
theorem integral_complexSymmetricGaussian_mul_negLogDeriv_eq_primeContribution
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ u : ℝ,
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        (-deriv riemannZeta
            (3 / 2 + Complex.I * (u : ℂ)) /
          riemannZeta (3 / 2 + Complex.I * (u : ℂ)))) =
      (Real.pi * gaussianPrimeContribution ε t : ℝ) := by
  rw [integral_complexSymmetricGaussian_mul_negLogDeriv_riemannZeta hε t]
  exact_mod_cast gaussianPrime_safeLine_normalization hε t

/-- After completing zeta, the same safe-line contour is the sum of the xi
logarithmic derivative, the two elementary pole terms, and the exact
Archimedean `log pi` and digamma terms.  This is the normalized starting
identity for the subsequent contour shift. -/
theorem integral_completedZeta_safeLine_decomposition_eq_primeContribution
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ u : ℝ,
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        (-deriv riemannXi (3 / 2 + Complex.I * (u : ℂ)) /
            riemannXi (3 / 2 + Complex.I * (u : ℂ)) +
          1 / (3 / 2 + Complex.I * (u : ℂ)) +
          1 / (3 / 2 + Complex.I * (u : ℂ) - 1) -
          Complex.log Real.pi / 2 +
          Complex.digamma
            ((3 / 2 + Complex.I * (u : ℂ)) / 2) / 2)) =
      (Real.pi * gaussianPrimeContribution ε t : ℝ) := by
  calc
    (∫ u : ℝ,
      complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
        (-deriv riemannXi (3 / 2 + Complex.I * (u : ℂ)) /
            riemannXi (3 / 2 + Complex.I * (u : ℂ)) +
          1 / (3 / 2 + Complex.I * (u : ℂ)) +
          1 / (3 / 2 + Complex.I * (u : ℂ) - 1) -
          Complex.log Real.pi / 2 +
          Complex.digamma
            ((3 / 2 + Complex.I * (u : ℂ)) / 2) / 2)) =
        ∫ u : ℝ,
          complexSymmetricGaussian ε t ((u : ℂ) - Complex.I) *
            (-deriv riemannZeta (3 / 2 + Complex.I * (u : ℂ)) /
              riemannZeta (3 / 2 + Complex.I * (u : ℂ))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        dsimp only
        rw [negLogDeriv_riemannZeta_safeLine_decomposition]
    _ = (Real.pi * gaussianPrimeContribution ε t : ℝ) :=
      integral_complexSymmetricGaussian_mul_negLogDeriv_eq_primeContribution
        hε t

end

end RiemannGaussian

import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation
import RiemannGaussian.GaussianDigammaTransform

/-!
# The finite paired-eta Gaussian Gram identity

This module joins the finite paired-eta arithmetic branch to a genuine
Gaussian Gram form. A general finite exponential sum is squared against a
translated Gaussian, expanded through only finite sums, and evaluated by the
checked Gaussian Fourier transform. The resulting double sum is proved real
and nonnegative because it is exactly the original norm integral.

The general identity is then specialized to the actual first `2N` alternating
eta atoms. Lean proves that their finite exponential sum is exactly
`pairedEtaCorePartialSum` on every vertical line, so the arithmetic double sum
is an unconditional Gram realization of the finite eta polynomial. No
symmetry under `sigma ↦ 1 - sigma` is asserted here; deriving a completed or
eta-specific complementary coupling remains the frontier.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

variable {ι : Type*}

/-- A finite Fourier--Laplace sum with complex coefficients and real
frequencies. -/
def finiteExponentialSum (S : Finset ι) (c : ι → ℂ)
    (frequency : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ j ∈ S, c j * Complex.exp (-Complex.I * (t * frequency j))

/-- The Gaussian-weighted square of a finite exponential sum. -/
def finiteGaussianExponentialEnergy (S : Finset ι) (c : ι → ℂ)
    (frequency : ι → ℝ) (tau x : ℝ) : ℂ :=
  ∫ t : ℝ,
    (translatedGaussian tau x t : ℂ) *
      finiteExponentialSum S c frequency t *
        starRingEnd ℂ (finiteExponentialSum S c frequency t)

/-- The explicit finite Gaussian Gram quadratic associated to a coefficient
family and its real frequencies. -/
def finiteGaussianGramQuadratic (S : Finset ι) (c : ι → ℂ)
    (frequency : ι → ℝ) (tau x : ℝ) : ℂ :=
  (Real.sqrt (Real.pi / tau) : ℂ) *
    ∑ k ∈ S, ∑ j ∈ S,
      c j * starRingEnd ℂ (c k) *
        Complex.exp
          (((-(frequency k - frequency j) ^ 2 / (4 * tau) : ℝ) : ℂ) +
            Complex.I * (x * (frequency k - frequency j)))

private theorem finiteGaussianExponentialEnergyIntegrand_eq_sum
    (S : Finset ι) (c : ι → ℂ) (frequency : ι → ℝ)
    (tau x t : ℝ) :
    (translatedGaussian tau x t : ℂ) *
        finiteExponentialSum S c frequency t *
          starRingEnd ℂ (finiteExponentialSum S c frequency t) =
      ∑ k ∈ S, ∑ j ∈ S,
        c j * starRingEnd ℂ (c k) *
          complexTranslatedGaussianOscillation tau x
            (frequency k - frequency j) t := by
  unfold finiteExponentialSum
  rw [map_sum]
  change
    (translatedGaussian tau x t : ℂ) *
          (∑ j ∈ S,
            c j * Complex.exp (-Complex.I * (t * frequency j))) *
        (∑ k ∈ S,
          starRingEnd ℂ
            (c k * Complex.exp (-Complex.I * (t * frequency k)))) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
    neg_neg, neg_mul]
  unfold complexTranslatedGaussianOscillation translatedGaussian
  rw [Complex.ofReal_exp]
  rw [show
      Complex.exp (((-tau * (t - x) ^ 2 : ℝ) : ℂ)) *
            (c j * Complex.exp (-(Complex.I * (t * frequency j)))) *
            (starRingEnd ℂ (c k) *
              Complex.exp (Complex.I * (t * frequency k))) =
        c j * starRingEnd ℂ (c k) *
          (Complex.exp (((-tau * (t - x) ^ 2 : ℝ) : ℂ)) *
            Complex.exp (-(Complex.I * (t * frequency j))) *
            Complex.exp (Complex.I * (t * frequency k))) by ring]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- The Gaussian-weighted square of every finite exponential sum is genuinely
integrable at positive Gaussian time. -/
theorem integrable_finiteGaussianExponentialEnergy
    (S : Finset ι) (c : ι → ℂ) (frequency : ι → ℝ)
    {tau : ℝ} (htau : 0 < tau) (x : ℝ) :
    Integrable (fun t : ℝ =>
      (translatedGaussian tau x t : ℂ) *
        finiteExponentialSum S c frequency t *
          starRingEnd ℂ (finiteExponentialSum S c frequency t)) := by
  have hsum : Integrable (fun t : ℝ =>
      ∑ k ∈ S, ∑ j ∈ S,
        c j * starRingEnd ℂ (c k) *
          complexTranslatedGaussianOscillation tau x
            (frequency k - frequency j) t) := by
    apply integrable_finsetSum S
    intro k hk
    apply integrable_finsetSum S
    intro j hj
    exact (integrable_complexTranslatedGaussianOscillation htau x
      (frequency k - frequency j)).const_mul
        (c j * starRingEnd ℂ (c k))
  rw [show
      (fun t : ℝ =>
        (translatedGaussian tau x t : ℂ) *
          finiteExponentialSum S c frequency t *
            starRingEnd ℂ (finiteExponentialSum S c frequency t)) =
        (fun t : ℝ =>
          ∑ k ∈ S, ∑ j ∈ S,
            c j * starRingEnd ℂ (c k) *
              complexTranslatedGaussianOscillation tau x
                (frequency k - frequency j) t) by
      funext t
      exact finiteGaussianExponentialEnergyIntegrand_eq_sum
        S c frequency tau x t]
  exact hsum

/-- Exact finite Gaussian Fourier identity: the weighted square integral is
the explicit arithmetic Gram quadratic. -/
theorem finiteGaussianExponentialEnergy_eq_gramQuadratic
    (S : Finset ι) (c : ι → ℂ) (frequency : ι → ℝ)
    {tau : ℝ} (htau : 0 < tau) (x : ℝ) :
    finiteGaussianExponentialEnergy S c frequency tau x =
      finiteGaussianGramQuadratic S c frequency tau x := by
  unfold finiteGaussianExponentialEnergy finiteGaussianGramQuadratic
  rw [integral_congr_ae (Eventually.of_forall fun t =>
    finiteGaussianExponentialEnergyIntegrand_eq_sum
      S c frequency tau x t)]
  have hterm (k j : ι) : Integrable (fun t : ℝ =>
      c j * starRingEnd ℂ (c k) *
        complexTranslatedGaussianOscillation tau x
          (frequency k - frequency j) t) :=
    (integrable_complexTranslatedGaussianOscillation htau x
      (frequency k - frequency j)).const_mul
        (c j * starRingEnd ℂ (c k))
  have hinner (k : ι) : Integrable (fun t : ℝ =>
      ∑ j ∈ S,
        c j * starRingEnd ℂ (c k) *
          complexTranslatedGaussianOscillation tau x
            (frequency k - frequency j) t) := by
    apply integrable_finsetSum S
    intro j hj
    exact hterm k j
  rw [integral_finsetSum S (fun k _ => hinner k), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_finsetSum S (fun j _ => hterm k j), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul,
    integral_complexTranslatedGaussianOscillation htau]
  push_cast
  ring

/-- The energy integrand is the real nonnegative Gaussian weight times the
squared modulus of the finite exponential sum. -/
theorem finiteGaussianExponentialEnergyIntegrand_re
    (S : Finset ι) (c : ι → ℂ) (frequency : ι → ℝ)
    (tau x t : ℝ) :
    ((translatedGaussian tau x t : ℂ) *
        finiteExponentialSum S c frequency t *
          starRingEnd ℂ (finiteExponentialSum S c frequency t)).re =
      translatedGaussian tau x t *
        Complex.normSq (finiteExponentialSum S c frequency t) := by
  rw [show
      (translatedGaussian tau x t : ℂ) *
          finiteExponentialSum S c frequency t *
            starRingEnd ℂ (finiteExponentialSum S c frequency t) =
        ((translatedGaussian tau x t *
          Complex.normSq (finiteExponentialSum S c frequency t) : ℝ) : ℂ) by
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      ring]
  simp

/-- Every explicit finite Gaussian Gram quadratic has nonnegative real part. -/
theorem finiteGaussianGramQuadratic_re_nonneg
    (S : Finset ι) (c : ι → ℂ) (frequency : ι → ℝ)
    {tau : ℝ} (htau : 0 < tau) (x : ℝ) :
    0 ≤ (finiteGaussianGramQuadratic S c frequency tau x).re := by
  rw [← finiteGaussianExponentialEnergy_eq_gramQuadratic
    S c frequency htau x]
  unfold finiteGaussianExponentialEnergy
  have hre := integral_re
    (integrable_finiteGaussianExponentialEnergy S c frequency htau x)
  rw [RCLike.re_eq_complex_re] at hre
  rw [← hre]
  apply integral_nonneg
  intro t
  change 0 ≤ ((translatedGaussian tau x t : ℂ) *
    finiteExponentialSum S c frequency t *
      starRingEnd ℂ (finiteExponentialSum S c frequency t)).re
  rw [finiteGaussianExponentialEnergyIntegrand_re]
  exact mul_nonneg (by
    unfold translatedGaussian
    positivity) (Complex.normSq_nonneg _)

/-- Every explicit finite Gaussian Gram quadratic is real. -/
theorem finiteGaussianGramQuadratic_im
    (S : Finset ι) (c : ι → ℂ) (frequency : ι → ℝ)
    {tau : ℝ} (htau : 0 < tau) (x : ℝ) :
    (finiteGaussianGramQuadratic S c frequency tau x).im = 0 := by
  rw [← finiteGaussianExponentialEnergy_eq_gramQuadratic
    S c frequency htau x]
  unfold finiteGaussianExponentialEnergy
  have him := integral_im
    (integrable_finiteGaussianExponentialEnergy S c frequency htau x)
  rw [RCLike.im_eq_complex_im] at him
  rw [← him]
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun t => by
    change ((translatedGaussian tau x t : ℂ) *
      finiteExponentialSum S c frequency t *
        starRingEnd ℂ (finiteExponentialSum S c frequency t)).im = 0
    rw [show
      (translatedGaussian tau x t : ℂ) *
          finiteExponentialSum S c frequency t *
            starRingEnd ℂ (finiteExponentialSum S c frequency t) =
        ((translatedGaussian tau x t *
          Complex.normSq (finiteExponentialSum S c frequency t) : ℝ) : ℂ) by
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      ring]
    simp

/-! ## Specialization to the finite paired-eta polynomials -/

/-- The real-tilt coefficient of the `k`th alternating eta atom, indexed
from zero. -/
def pairedEtaGaussianCoefficient (sigma : ℝ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k *
    ((((k + 1 : ℕ) : ℝ) : ℂ)) ^ (-(sigma : ℂ))

/-- The logarithmic frequency of the `k`th alternating eta atom. -/
def pairedEtaLogFrequency (k : ℕ) : ℝ :=
  Real.log (k + 1)

/-- Separating real tilt from vertical oscillation recovers the corresponding
complex Dirichlet atom exactly. -/
theorem pairedEtaGaussianCoefficient_mul_oscillation
    (sigma t : ℝ) (k : ℕ) :
    pairedEtaGaussianCoefficient sigma k *
        Complex.exp (-Complex.I * (t * pairedEtaLogFrequency k)) =
      (-1 : ℂ) ^ k *
        ((((k + 1 : ℕ) : ℝ) : ℂ)) ^
          (-((sigma : ℂ) + (t : ℂ) * Complex.I)) := by
  let a : ℝ := (k : ℝ) + 1
  have haPos : 0 < a := by dsimp [a]; positivity
  have ha : 0 ≤ a := haPos.le
  have hane : (a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr haPos.ne'
  unfold pairedEtaGaussianCoefficient pairedEtaLogFrequency
  simp only [Nat.cast_add, Nat.cast_one]
  change (-1 : ℂ) ^ k * (a : ℂ) ^ (-(sigma : ℂ)) *
      Complex.exp (-Complex.I * (t * Real.log a)) =
    (-1 : ℂ) ^ k *
      (a : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * Complex.I))
  rw [mul_assoc]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hane,
    Complex.cpow_def_of_ne_zero hane,
    ← Complex.ofReal_log ha, ← Complex.exp_add]
  congr 1
  ring_nf

/-- The first `2N` alternating atoms are exactly the first `N` paired-eta
summands on every vertical line. -/
theorem finiteExponentialSum_pairedEta_eq_partialSum
    (N : ℕ) (sigma t : ℝ) :
    finiteExponentialSum (Finset.range (2 * N))
        (pairedEtaGaussianCoefficient sigma) pairedEtaLogFrequency t =
      pairedEtaCorePartialSum N
        ((sigma : ℂ) + (t : ℂ) * Complex.I) := by
  induction N with
  | zero =>
      simp [finiteExponentialSum, pairedEtaCorePartialSum]
  | succ N ih =>
      unfold finiteExponentialSum pairedEtaCorePartialSum at ih ⊢
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih,
        pairedEtaGaussianCoefficient_mul_oscillation,
        pairedEtaGaussianCoefficient_mul_oscillation]
      unfold pairedEtaCoreSummand
      have heven : (-1 : ℂ) ^ (2 * N) = 1 := by
        rw [pow_mul]
        norm_num
      have hodd : (-1 : ℂ) ^ (2 * N + 1) = -1 := by
        rw [pow_succ, heven]
        ring
      rw [heven, hodd]
      push_cast
      ring_nf

/-- The Gaussian `L²` norm of the actual finite paired-eta polynomial on a
vertical line. -/
def pairedEtaFiniteGaussianNorm
    (N : ℕ) (sigma tau x : ℝ) : ℝ :=
  ∫ t : ℝ,
    translatedGaussian tau x t *
      Complex.normSq (pairedEtaCorePartialSum N
        ((sigma : ℂ) + (t : ℂ) * Complex.I))

/-- The completely explicit finite arithmetic Gaussian Gram quadratic for
the first `2N` alternating eta atoms. -/
def pairedEtaFiniteGaussianGramQuadratic
    (N : ℕ) (sigma tau x : ℝ) : ℂ :=
  finiteGaussianGramQuadratic (Finset.range (2 * N))
    (pairedEtaGaussianCoefficient sigma) pairedEtaLogFrequency tau x

/-- The real eta norm integrand is genuinely integrable at positive Gaussian
time. -/
theorem integrable_pairedEtaFiniteGaussianNorm
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) (x : ℝ) :
    Integrable (fun t : ℝ =>
      translatedGaussian tau x t *
        Complex.normSq (pairedEtaCorePartialSum N
          ((sigma : ℂ) + (t : ℂ) * Complex.I))) := by
  have hcomplex := integrable_finiteGaussianExponentialEnergy
    (Finset.range (2 * N)) (pairedEtaGaussianCoefficient sigma)
      pairedEtaLogFrequency htau x
  have hre := hcomplex.re
  rw [RCLike.re_eq_complex_re] at hre
  apply hre.congr
  exact Eventually.of_forall fun t => by
    change ((translatedGaussian tau x t : ℂ) *
      finiteExponentialSum (Finset.range (2 * N))
        (pairedEtaGaussianCoefficient sigma) pairedEtaLogFrequency t *
      starRingEnd ℂ
        (finiteExponentialSum (Finset.range (2 * N))
          (pairedEtaGaussianCoefficient sigma) pairedEtaLogFrequency t)).re =
      translatedGaussian tau x t *
        Complex.normSq (pairedEtaCorePartialSum N
          ((sigma : ℂ) + (t : ℂ) * Complex.I))
    rw [finiteGaussianExponentialEnergyIntegrand_re,
      finiteExponentialSum_pairedEta_eq_partialSum]

/-- Exact finite eta Gaussian--Gram identity. The left side is a genuine
nonnegative real integral; the right side is a finite arithmetic double sum. -/
theorem pairedEtaFiniteGaussianNorm_eq_gramQuadratic
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) (x : ℝ) :
    (pairedEtaFiniteGaussianNorm N sigma tau x : ℂ) =
      pairedEtaFiniteGaussianGramQuadratic N sigma tau x := by
  unfold pairedEtaFiniteGaussianNorm pairedEtaFiniteGaussianGramQuadratic
  rw [← integral_complex_ofReal]
  rw [show
      (fun t : ℝ =>
        ((translatedGaussian tau x t *
          Complex.normSq (pairedEtaCorePartialSum N
            ((sigma : ℂ) + (t : ℂ) * Complex.I)) : ℝ) : ℂ)) =
      (fun t : ℝ =>
        (translatedGaussian tau x t : ℂ) *
          finiteExponentialSum (Finset.range (2 * N))
            (pairedEtaGaussianCoefficient sigma)
              pairedEtaLogFrequency t *
          starRingEnd ℂ
            (finiteExponentialSum (Finset.range (2 * N))
              (pairedEtaGaussianCoefficient sigma)
                pairedEtaLogFrequency t)) by
      funext t
      rw [finiteExponentialSum_pairedEta_eq_partialSum]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      ring]
  exact finiteGaussianExponentialEnergy_eq_gramQuadratic
    (Finset.range (2 * N)) (pairedEtaGaussianCoefficient sigma)
      pairedEtaLogFrequency htau x

/-- Expanded form of the exact eta Gaussian--Gram identity. -/
theorem pairedEtaFiniteGaussianNorm_eq_doubleSum
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) (x : ℝ) :
    (pairedEtaFiniteGaussianNorm N sigma tau x : ℂ) =
      (Real.sqrt (Real.pi / tau) : ℂ) *
        ∑ k ∈ Finset.range (2 * N),
          ∑ j ∈ Finset.range (2 * N),
            pairedEtaGaussianCoefficient sigma j *
              starRingEnd ℂ (pairedEtaGaussianCoefficient sigma k) *
              Complex.exp
                (((-(pairedEtaLogFrequency k -
                    pairedEtaLogFrequency j) ^ 2 /
                    (4 * tau) : ℝ) : ℂ) +
                  Complex.I * (x * (pairedEtaLogFrequency k -
                    pairedEtaLogFrequency j))) := by
  rw [pairedEtaFiniteGaussianNorm_eq_gramQuadratic N sigma htau x]
  rfl

/-- The finite eta Gaussian norm is nonnegative by construction. -/
theorem pairedEtaFiniteGaussianNorm_nonneg
    (N : ℕ) (sigma tau x : ℝ) :
    0 ≤ pairedEtaFiniteGaussianNorm N sigma tau x := by
  unfold pairedEtaFiniteGaussianNorm
  apply integral_nonneg
  intro t
  exact mul_nonneg (by
    unfold translatedGaussian
    positivity) (Complex.normSq_nonneg _)

/-- The explicit eta Gaussian Gram quadratic is real and nonnegative. -/
theorem pairedEtaFiniteGaussianGramQuadratic_re_nonneg
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) (x : ℝ) :
    0 ≤ (pairedEtaFiniteGaussianGramQuadratic N sigma tau x).re := by
  unfold pairedEtaFiniteGaussianGramQuadratic
  exact finiteGaussianGramQuadratic_re_nonneg
    (Finset.range (2 * N)) (pairedEtaGaussianCoefficient sigma)
      pairedEtaLogFrequency htau x

/-- The explicit eta Gaussian Gram quadratic has zero imaginary part. -/
theorem pairedEtaFiniteGaussianGramQuadratic_im
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) (x : ℝ) :
    (pairedEtaFiniteGaussianGramQuadratic N sigma tau x).im = 0 := by
  unfold pairedEtaFiniteGaussianGramQuadratic
  exact finiteGaussianGramQuadratic_im
    (Finset.range (2 * N)) (pairedEtaGaussianCoefficient sigma)
      pairedEtaLogFrequency htau x

end

end RiemannGaussian

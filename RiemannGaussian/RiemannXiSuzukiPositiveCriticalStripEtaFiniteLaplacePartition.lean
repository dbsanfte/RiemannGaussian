import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteZeroPersistence

/-!
# Finite eta as a positive Laplace partition function

The finite paired-eta sums now carry actual roots converging to every
nontrivial zeta zero. This module exposes the additional arithmetic structure
of those finite models. After the logarithmic change of variables, every
odd-even eta pair is the Laplace transform of Lebesgue measure on the positive
interval from `log (2n+1)` to `log (2n+2)`.

Thus `E_N(s) / s` is a finite positive-measure partition function. At every
zero with positive real part, its exponentially tilted cosine and sine
moments vanish exactly. Positivity of the underlying measure also gives an
explicit phase-spread obstruction: no nonzero finite eta sum can vanish while
its total Fourier phase across `[0, log (2N)]` is smaller than a quarter turn.

These are unconditional finite arithmetic constraints, not an RH theorem.
Their purpose is to turn the remaining zero-location problem into a concrete
positive-measure Fourier rigidity problem amenable to moment, entropy, and
Lee--Yang methods.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The positive-measure finite Laplace partition function underlying the
first `N` paired-eta summands. -/
def pairedEtaFiniteLaplacePartition (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N,
    ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
      Complex.exp (-s * t)

/-- The exponentially tilted cosine moment of the finite positive eta
measure. -/
def pairedEtaFiniteTiltedCosineMoment
    (N : ℕ) (sigma y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
      Real.exp (-sigma * t) * Real.cos (y * t)

/-- The exponentially tilted sine moment of the finite positive eta
measure. -/
def pairedEtaFiniteTiltedSineMoment
    (N : ℕ) (sigma y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
      Real.exp (-sigma * t) * Real.sin (y * t)

/-- One odd-even eta pair is `s` times its positive logarithmic-time
Laplace interval. -/
theorem pairedEtaCoreSummand_eq_mul_logLaplaceInterval
    (s : ℂ) (n : ℕ) :
    pairedEtaCoreSummand s n =
      s * ∫ t : ℝ in
        Real.log (2 * n + 1)..Real.log (2 * n + 2),
          Complex.exp (-s * t) := by
  by_cases hs : s = 0
  · subst s
    simp [pairedEtaCoreSummand]
  · have hoddNonneg : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      positivity
    have hevenNonneg : (0 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by
      positivity
    have hodd : ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
    have heven : ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show 2 * n + 2 ≠ 0 by omega)
    have hoddPow :
        Complex.exp (-s * Real.log (2 * n + 1)) =
          ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
      rw [Complex.cpow_def_of_ne_zero hodd,
        ← Complex.ofReal_log hoddNonneg]
      congr 1
      push_cast
      ring
    have hevenPow :
        Complex.exp (-s * Real.log (2 * n + 2)) =
          ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
      rw [Complex.cpow_def_of_ne_zero heven,
        ← Complex.ofReal_log hevenNonneg]
      congr 1
      push_cast
      ring
    rw [integral_exp_mul_complex (c := -s) (neg_ne_zero.mpr hs)]
    rw [hoddPow, hevenPow]
    unfold pairedEtaCoreSummand
    field_simp [hs]
    simp only [Nat.mul_comm]
    abel

/-- The finite eta sum is exactly `s` times its finite positive-measure
Laplace partition function. -/
theorem pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition
    (N : ℕ) (s : ℂ) :
    pairedEtaCorePartialSum N s =
      s * pairedEtaFiniteLaplacePartition N s := by
  unfold pairedEtaCorePartialSum pairedEtaFiniteLaplacePartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact pairedEtaCoreSummand_eq_mul_logLaplaceInterval s n

/-- At positive real part, every finite eta zero is a zero of the underlying
positive-measure Laplace partition function. -/
theorem pairedEtaFiniteLaplacePartition_eq_zero_of_partialSum_eq_zero
    {N : ℕ} {s : ℂ} (hs : 0 < s.re)
    (hzero : pairedEtaCorePartialSum N s = 0) :
    pairedEtaFiniteLaplacePartition N s = 0 := by
  rw [pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (by
    intro hsZero
    subst s
    norm_num at hs)

/-- Real projection of the logarithmic-time Laplace kernel. -/
theorem pairedEtaFiniteLaplaceKernel_re (sigma y t : ℝ) :
    (Complex.exp
      (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re =
      Real.exp (-sigma * t) * Real.cos (y * t) := by
  rw [Complex.exp_re]
  norm_num [Complex.mul_re, Complex.mul_im]

/-- Imaginary projection of the logarithmic-time Laplace kernel. -/
theorem pairedEtaFiniteLaplaceKernel_im (sigma y t : ℝ) :
    (Complex.exp
      (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).im =
      -(Real.exp (-sigma * t) * Real.sin (y * t)) := by
  rw [Complex.exp_im]
  norm_num [Complex.mul_re, Complex.mul_im]

/-- The real part of one complex Laplace interval is its tilted cosine
moment. -/
theorem pairedEtaFiniteLaplaceInterval_re
    (sigma y : ℝ) (n : ℕ) :
    (∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
      Complex.exp
        (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re =
      ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
        Real.exp (-sigma * t) * Real.cos (y * t) := by
  have hcont : Continuous
      (fun t : ℝ ↦ Complex.exp
        (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)) := by
    fun_prop
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ Complex.exp
        (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t))
      MeasureSpace.volume
      (Real.log (2 * n + 1)) (Real.log (2 * n + 2)) :=
    hcont.intervalIntegrable
      (Real.log (2 * n + 1)) (Real.log (2 * n + 2))
  have hre :
      (∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
        (Complex.exp
          (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re) =
        (∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
          Complex.exp
            (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re := by
    simpa using intervalIntegral.intervalIntegral_re hint
  rw [← hre]
  apply intervalIntegral.integral_congr
  intro t _
  exact pairedEtaFiniteLaplaceKernel_re sigma y t

/-- The imaginary part of one complex Laplace interval is the negative of
its tilted sine moment. -/
theorem pairedEtaFiniteLaplaceInterval_im
    (sigma y : ℝ) (n : ℕ) :
    (∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
      Complex.exp
        (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).im =
      -(∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
        Real.exp (-sigma * t) * Real.sin (y * t)) := by
  have hcont : Continuous
      (fun t : ℝ ↦ Complex.exp
        (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)) := by
    fun_prop
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ Complex.exp
        (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t))
      MeasureSpace.volume
      (Real.log (2 * n + 1)) (Real.log (2 * n + 2)) :=
    hcont.intervalIntegrable
      (Real.log (2 * n + 1)) (Real.log (2 * n + 2))
  have him :
      (∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
        (Complex.exp
          (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).im) =
        (∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
          Complex.exp
            (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).im := by
    simpa using intervalIntegral.intervalIntegral_im hint
  rw [← him]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t _
  exact pairedEtaFiniteLaplaceKernel_im sigma y t

/-- The finite positive Laplace partition function splits exactly into its
tilted cosine and sine moments. -/
theorem pairedEtaFiniteLaplacePartition_eq_cosine_sub_I_sine
    (N : ℕ) (sigma y : ℝ) :
    pairedEtaFiniteLaplacePartition N
        ((sigma : ℂ) + (y : ℂ) * Complex.I) =
      (pairedEtaFiniteTiltedCosineMoment N sigma y : ℂ) -
        (pairedEtaFiniteTiltedSineMoment N sigma y : ℂ) * Complex.I := by
  apply Complex.ext
  · have hrhs :
        ((pairedEtaFiniteTiltedCosineMoment N sigma y : ℂ) -
          (pairedEtaFiniteTiltedSineMoment N sigma y : ℂ) *
            Complex.I).re =
          pairedEtaFiniteTiltedCosineMoment N sigma y := by
      norm_num [Complex.mul_re]
    rw [hrhs]
    unfold pairedEtaFiniteLaplacePartition
      pairedEtaFiniteTiltedCosineMoment
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    exact pairedEtaFiniteLaplaceInterval_re sigma y n
  · have hrhs :
        ((pairedEtaFiniteTiltedCosineMoment N sigma y : ℂ) -
          (pairedEtaFiniteTiltedSineMoment N sigma y : ℂ) *
            Complex.I).im =
          -pairedEtaFiniteTiltedSineMoment N sigma y := by
      norm_num [Complex.mul_im]
    rw [hrhs]
    unfold pairedEtaFiniteLaplacePartition
      pairedEtaFiniteTiltedSineMoment
    rw [Complex.im_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n _
    exact pairedEtaFiniteLaplaceInterval_im sigma y n

/-- Every positive-real-part zero of a finite eta sum satisfies two exact
real Fourier cancellation identities for the underlying positive measure. -/
theorem pairedEtaFiniteTiltedMoments_eq_zero_of_partialSum_eq_zero
    {N : ℕ} {sigma y : ℝ} (hsigma : 0 < sigma)
    (hzero : pairedEtaCorePartialSum N
      ((sigma : ℂ) + (y : ℂ) * Complex.I) = 0) :
    pairedEtaFiniteTiltedCosineMoment N sigma y = 0 ∧
      pairedEtaFiniteTiltedSineMoment N sigma y = 0 := by
  have hsRe :
      0 < (((sigma : ℂ) + (y : ℂ) * Complex.I).re) := by
    norm_num
    exact hsigma
  have hpartition :=
    pairedEtaFiniteLaplacePartition_eq_zero_of_partialSum_eq_zero
      hsRe hzero
  rw [pairedEtaFiniteLaplacePartition_eq_cosine_sub_I_sine] at hpartition
  constructor
  · have hre := congrArg Complex.re hpartition
    norm_num [Complex.mul_re] at hre
    exact hre
  · have him := congrArg Complex.im hpartition
    norm_num [Complex.mul_im] at him
    exact him

/-- The logarithmic interval supporting one paired eta summand has positive
length. -/
theorem pairedEtaFiniteLogInterval_pos (n : ℕ) :
    Real.log (2 * n + 1) < Real.log (2 * n + 2) := by
  apply Real.log_lt_log
  · positivity
  · exact_mod_cast (show 2 * n + 1 < 2 * n + 2 by omega)

/-- If the Fourier phase stays in `(-π/2, π/2)` throughout a paired eta
interval, its tilted cosine integral is strictly positive. -/
theorem pairedEtaFiniteTiltedCosineInterval_pos_of_phase_lt_halfPi
    {N n : ℕ} (hn : n < N) (sigma y : ℝ)
    (hphase : |y| * Real.log (2 * N) < Real.pi / 2) :
    0 < ∫ t : ℝ in
        Real.log (2 * n + 1)..Real.log (2 * n + 2),
      Real.exp (-sigma * t) * Real.cos (y * t) := by
  have hcont : Continuous (fun t : ℝ ↦
      Real.exp (-sigma * t) * Real.cos (y * t)) := by
    fun_prop
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont.intervalIntegrable _ _)
  · intro t htMem
    have hoddNonneg : 0 ≤ Real.log (2 * n + 1) := by
      apply Real.log_nonneg
      norm_num
    have hargUpper : (2 : ℝ) * n + 2 ≤ 2 * N := by
      exact_mod_cast (show 2 * n + 2 ≤ 2 * N by omega)
    have hlogUpper : Real.log (2 * n + 2) ≤ Real.log (2 * N) := by
      exact Real.log_le_log (by positivity) hargUpper
    have htNonneg : 0 ≤ t := hoddNonneg.trans htMem.1.le
    have htUpper : t ≤ Real.log (2 * N) :=
      htMem.2.le.trans hlogUpper
    have htAbs : |t| ≤ Real.log (2 * N) := by
      rwa [abs_of_nonneg htNonneg]
    have hphaseAt : |y * t| < Real.pi / 2 := by
      rw [abs_mul]
      exact
        (mul_le_mul_of_nonneg_left htAbs (abs_nonneg y)).trans_lt
          hphase
    exact mul_pos (Real.exp_pos _) <|
      Real.cos_pos_of_mem_Ioo (abs_lt.mp hphaseAt)
  · exact pairedEtaFiniteLogInterval_pos n

/-- A finite eta partition with at least one interval has positive tilted
cosine moment whenever its entire uncentered phase spread is below `π/2`. -/
theorem pairedEtaFiniteTiltedCosineMoment_pos_of_phase_lt_halfPi
    {N : ℕ} (hN : 0 < N) (sigma y : ℝ)
    (hphase : |y| * Real.log (2 * N) < Real.pi / 2) :
    0 < pairedEtaFiniteTiltedCosineMoment N sigma y := by
  unfold pairedEtaFiniteTiltedCosineMoment
  apply Finset.sum_pos
  · intro n hn
    exact
      pairedEtaFiniteTiltedCosineInterval_pos_of_phase_lt_halfPi
        (Finset.mem_range.mp hn) sigma y hphase
  · exact Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)

/-- Every positive-real-part zero of a nonempty finite eta sum must accumulate
at least a quarter turn of Fourier phase over its logarithmic support. -/
theorem halfPi_le_abs_y_mul_log_of_pairedEtaCorePartialSum_eq_zero
    {N : ℕ} (hN : 0 < N) {sigma y : ℝ} (hsigma : 0 < sigma)
    (hzero : pairedEtaCorePartialSum N
      ((sigma : ℂ) + (y : ℂ) * Complex.I) = 0) :
    Real.pi / 2 ≤ |y| * Real.log (2 * N) := by
  by_contra hphase
  have hphaseLt : |y| * Real.log (2 * N) < Real.pi / 2 :=
    lt_of_not_ge hphase
  have hpositive :=
    pairedEtaFiniteTiltedCosineMoment_pos_of_phase_lt_halfPi
      hN sigma y hphaseLt
  have hmomentZero :=
    (pairedEtaFiniteTiltedMoments_eq_zero_of_partialSum_eq_zero
      hsigma hzero).1
  exact hpositive.ne' hmomentZero

/-- Every nontrivial zeta zero is approached by genuine finite positive
Laplace partition zeros which, eventually, satisfy both exact tilted Fourier
cancellations and the quantitative quarter-turn phase obstruction. -/
theorem exists_pairedEtaFiniteLaplaceMomentZero_sequence_tendsto
    (rho : NontrivialZetaZero) :
    ∃ N : ℕ → ℕ, ∃ z : ℕ → ℂ,
      Tendsto N atTop atTop ∧
      Tendsto z atTop (nhds rho.1) ∧
      (∀ n, n ≤ N n) ∧
      (∀ n, dist (z n) rho.1 <
        pairedEtaBoundaryHeatFluxDiagonalTolerance n) ∧
      (∀ n, pairedEtaCorePartialSum (N n) (z n) = 0) ∧
      ∀ᶠ n : ℕ in atTop,
        0 < (z n).re ∧
        pairedEtaFiniteTiltedCosineMoment
          (N n) (z n).re (z n).im = 0 ∧
        pairedEtaFiniteTiltedSineMoment
          (N n) (z n).re (z n).im = 0 ∧
        Real.pi / 2 ≤ |(z n).im| * Real.log (2 * N n) := by
  obtain ⟨N, z, hNtendsto, hztendsto, hNge, hzDist, hzZero⟩ :=
    exists_pairedEtaCorePartialSum_zero_sequence_tendsto rho
  refine ⟨N, z, hNtendsto, hztendsto, hNge, hzDist, hzZero, ?_⟩
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < (z n).re :=
    hztendsto.eventually <|
      (Complex.isOpen_re_gt 0).mem_nhds
        (NontrivialZetaZero.zero_lt_re rho)
  filter_upwards [hpositive, eventually_ge_atTop 1] with n hnRe hnOne
  have hNpos : 0 < N n := by
    have hnLe := hNge n
    omega
  have hzZeroCoordinates :
      pairedEtaCorePartialSum (N n)
        (((z n).re : ℂ) + ((z n).im : ℂ) * Complex.I) = 0 := by
    simpa only [Complex.re_add_im] using hzZero n
  have hmoments :=
    pairedEtaFiniteTiltedMoments_eq_zero_of_partialSum_eq_zero
      hnRe hzZeroCoordinates
  exact ⟨hnRe, hmoments.1, hmoments.2,
    halfPi_le_abs_y_mul_log_of_pairedEtaCorePartialSum_eq_zero
      hNpos hnRe hzZeroCoordinates⟩

end

end RiemannGaussian

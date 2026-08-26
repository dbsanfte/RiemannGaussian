import RiemannGaussian.GaussianPositivityCertificate

/-!
# Gaussian prime discrepancy after the continuous main-term cancellation

The positive prime energy is exponentially large at broad Gaussian widths,
but so is the elementary boundary drop.  Their leading continuous-PNT terms
cancel exactly.  This file exposes the remaining RH-strength object without
discarding either of the two small quantities which numerical falsification
shows are essential: the endpoint margin and the positive digamma gain.

It also supplies a finite phase-block interface.  Any lower bound for the
weighted von-Mangoldt mass in regions where `1 - cos (t * log n)` has a
uniform floor gives a rigorous lower bound for the full prime energy.
-/

namespace RiemannGaussian

noncomputable section

open MeasureTheory
open scoped BigOperators Topology

/-! ## Exact cancellation variables -/

/-- The elementary boundary channel occurring inside the Archimedean term. -/
def gaussianElementaryBoundaryTerm (ε t : ℝ) : ℝ :=
  4 * Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t)

/-- Continuous-PNT main term for the positive prime energy.  Its integral
interpretation is the bilateral Gaussian transform of `exp (u / 2) du`; the
closed form is chosen here so the exact arithmetic cancellation is explicit. -/
def gaussianPrimeEnergyMainTerm (ε t : ℝ) : ℝ :=
  gaussianElementaryBoundaryTerm ε 0 -
    gaussianElementaryBoundaryTerm ε t

/-- Bilateral continuous-PNT comparison energy.  It replaces the atomic
von-Mangoldt mass at `u = log n` by the continuous density `exp (u / 2) du`,
while retaining the same normalized Gaussian oscillation kernel. -/
def gaussianContinuousPrimeOscillationEnergy (ε t : ℝ) : ℝ :=
  2 / Real.sqrt (Real.pi * ε) *
    ∫ u : ℝ,
      Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
        (1 - Real.cos (t * u))

theorem gaussianContinuousPrimeOscillationEnergy_nonnegative
    (ε t : ℝ) :
    0 ≤ gaussianContinuousPrimeOscillationEnergy ε t := by
  unfold gaussianContinuousPrimeOscillationEnergy
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro u
  exact mul_nonneg (Real.exp_pos _).le
    (sub_nonneg.mpr (Real.cos_le_one _))

/-- Gaussian-smoothed von-Mangoldt discrepancy after subtracting the
continuous prime-energy main term. -/
def gaussianPrimeEnergyDiscrepancy (ε t : ℝ) : ℝ :=
  gaussianPrimeOscillationEnergy ε t -
    gaussianPrimeEnergyMainTerm ε t

/-- The non-elementary Archimedean gain away from center zero. -/
def gaussianDigammaGain (ε t : ℝ) : ℝ :=
  gaussianDigammaIntegral ε t - gaussianDigammaIntegral ε 0

theorem gaussianPrimeEnergyMainTerm_eq
    (ε t : ℝ) :
    gaussianPrimeEnergyMainTerm ε t =
      4 * Real.exp (ε / 4) -
        4 * Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t) := by
  unfold gaussianPrimeEnergyMainTerm gaussianElementaryBoundaryTerm
  norm_num

/-! ## The continuous-PNT Gaussian transform -/

/-- Complex completion-of-the-square evaluation underlying the continuous
prime-energy comparison. -/
theorem gaussianContinuousPrimeComplexTransform
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ u : ℝ, Complex.exp
      (((u / 2 - u ^ 2 / (4 * ε) : ℝ) : ℂ) +
        Complex.I * (t * u))) =
      (Real.sqrt (Real.pi / (1 / (4 * ε))) : ℂ) *
        Complex.exp
          (((ε / 4 - ε * t ^ 2 : ℝ) : ℂ) +
            Complex.I * (ε * t)) := by
  have hεne : ε ≠ 0 := hε.ne'
  let a : ℝ := 1 / (4 * ε)
  have ha : 0 < a := by dsimp only [a]; positivity
  let c : ℂ := (1 / 2 : ℝ) + Complex.I * t
  have hquad : ((-(a : ℂ))).re < 0 := by
    simpa using neg_lt_zero.mpr ha
  have hintegrand :
      (fun u : ℝ => Complex.exp
        (((u / 2 - u ^ 2 / (4 * ε) : ℝ) : ℂ) +
          Complex.I * (t * u))) =
        (fun u : ℝ => Complex.exp
          (-(a : ℂ) * (u : ℂ) ^ 2 + c * (u : ℂ) + 0)) := by
    funext u
    congr 1
    dsimp only [a, c]
    push_cast
    field_simp [hεne]
    ring
  rw [hintegrand]
  rw [integral_cexp_quadratic hquad c 0]
  have hsqrt :
      (Real.sqrt (Real.pi / a) : ℂ) =
        (((Real.pi / a : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
    rw [Real.sqrt_eq_rpow]
    simpa using Complex.ofReal_cpow
      (div_nonneg Real.pi_pos.le ha.le) (1 / 2 : ℝ)
  have hbase :
      (((Real.pi : ℂ) / -(-(a : ℂ))) : ℂ) ^ (1 / 2 : ℂ) =
        (Real.sqrt (Real.pi / a) : ℂ) := by
    rw [hsqrt]
    congr 2
    push_cast
    field_simp [ha.ne']
  have hexponent :
      (0 : ℂ) - c ^ 2 / (4 * (-(a : ℂ))) =
        ((ε / 4 - ε * t ^ 2 : ℝ) : ℂ) +
          Complex.I * (ε * t) := by
    dsimp only [a, c]
    have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hεne
    push_cast
    field_simp [hεc]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hbase, hexponent]

theorem gaussianContinuousPrimeComplexIntegrable
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun u : ℝ => Complex.exp
      (((u / 2 - u ^ 2 / (4 * ε) : ℝ) : ℂ) +
        Complex.I * (t * u))) := by
  let a : ℝ := 1 / (4 * ε)
  have ha : 0 < a := by dsimp only [a]; positivity
  let c : ℂ := (1 / 2 : ℝ) + Complex.I * t
  have hquad : ((-(a : ℂ))).re < 0 := by
    simpa using neg_lt_zero.mpr ha
  have hintegrand :
      (fun u : ℝ => Complex.exp
        (((u / 2 - u ^ 2 / (4 * ε) : ℝ) : ℂ) +
          Complex.I * (t * u))) =
        (fun u : ℝ => Complex.exp
          (-(a : ℂ) * (u : ℂ) ^ 2 + c * (u : ℂ) + 0)) := by
    funext u
    congr 1
    dsimp only [a, c]
    push_cast
    field_simp [hε.ne']
    ring
  rw [hintegrand]
  exact integrable_cexp_quadratic' hquad c 0

theorem gaussianContinuousPrimeComplexIntegrand_re
    (ε t u : ℝ) :
    (Complex.exp
      (((u / 2 - u ^ 2 / (4 * ε) : ℝ) : ℂ) +
        Complex.I * (t * u))).re =
      Real.exp (u / 2 - u ^ 2 / (4 * ε)) * Real.cos (t * u) := by
  rw [Complex.exp_add, ← Complex.ofReal_exp]
  rw [mul_comm Complex.I]
  rw [← Complex.ofReal_mul]
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    add_zero, sub_zero, mul_one]

theorem gaussianContinuousPrimeCosineIntegrable
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun u : ℝ =>
      Real.exp (u / 2 - u ^ 2 / (4 * ε)) * Real.cos (t * u)) := by
  have hre := (gaussianContinuousPrimeComplexIntegrable hε t).re
  apply hre.congr
  filter_upwards with u
  exact gaussianContinuousPrimeComplexIntegrand_re ε t u

theorem gaussianContinuousPrimeCosineTransform
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ u : ℝ,
      Real.exp (u / 2 - u ^ 2 / (4 * ε)) * Real.cos (t * u)) =
      Real.sqrt (Real.pi / (1 / (4 * ε))) *
        Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t) := by
  have hresult :
      ((Real.sqrt (Real.pi / (1 / (4 * ε))) : ℂ) *
        Complex.exp
          (((ε / 4 - ε * t ^ 2 : ℝ) : ℂ) +
            Complex.I * (ε * t))).re =
        Real.sqrt (Real.pi / (1 / (4 * ε))) *
          Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp]
    rw [mul_comm Complex.I]
    rw [← Complex.ofReal_mul]
    rw [Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      add_zero, sub_zero, mul_one]
    ring
  have hre := integral_re
    (gaussianContinuousPrimeComplexIntegrable hε t)
  rw [gaussianContinuousPrimeComplexTransform hε t] at hre
  change
    (∫ u : ℝ,
      (Complex.exp
        (((u / 2 - u ^ 2 / (4 * ε) : ℝ) : ℂ) +
          Complex.I * (t * u))).re) =
      ((Real.sqrt (Real.pi / (1 / (4 * ε))) : ℂ) *
        Complex.exp
          (((ε / 4 - ε * t ^ 2 : ℝ) : ℂ) +
            Complex.I * (ε * t))).re at hre
  rw [integral_congr_ae (Filter.Eventually.of_forall fun u =>
    gaussianContinuousPrimeComplexIntegrand_re ε t u)] at hre
  rw [hresult] at hre
  exact hre

theorem gaussianContinuousPrimeSqrt_normalization
    {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt (Real.pi / (1 / (4 * ε))) =
      2 * Real.sqrt (Real.pi * ε) := by
  have hquotient : Real.pi / (1 / (4 * ε)) =
      4 * (Real.pi * ε) := by
    field_simp [hε.ne']
  rw [hquotient, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hsqrtFour : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  rw [hsqrtFour]

theorem gaussianContinuousPrimeCosineTransform_normalized
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ u : ℝ,
      Real.exp (u / 2 - u ^ 2 / (4 * ε)) * Real.cos (t * u)) =
      2 * Real.sqrt (Real.pi * ε) *
        Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t) := by
  rw [gaussianContinuousPrimeCosineTransform hε t,
    gaussianContinuousPrimeSqrt_normalization hε]

theorem gaussianContinuousPrimeDensityIntegrable
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun u : ℝ =>
      Real.exp (u / 2 - u ^ 2 / (4 * ε))) := by
  simpa using gaussianContinuousPrimeCosineIntegrable hε 0

theorem gaussianContinuousPrimeDensityIntegral
    {ε : ℝ} (hε : 0 < ε) :
    (∫ u : ℝ, Real.exp (u / 2 - u ^ 2 / (4 * ε))) =
      2 * Real.sqrt (Real.pi * ε) * Real.exp (ε / 4) := by
  simpa using gaussianContinuousPrimeCosineTransform_normalized hε 0

theorem gaussianContinuousPrimeOscillationIntegrable
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun u : ℝ =>
      Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
        (1 - Real.cos (t * u))) := by
  have hsub := (gaussianContinuousPrimeDensityIntegrable hε).sub
    (gaussianContinuousPrimeCosineIntegrable hε t)
  apply hsub.congr
  filter_upwards with u
  change
    Real.exp (u / 2 - u ^ 2 / (4 * ε)) -
        Real.exp (u / 2 - u ^ 2 / (4 * ε)) * Real.cos (t * u) =
      Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
        (1 - Real.cos (t * u))
  ring

theorem gaussianContinuousPrimeOscillationIntegral
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ u : ℝ,
      Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
        (1 - Real.cos (t * u))) =
      2 * Real.sqrt (Real.pi * ε) *
        (Real.exp (ε / 4) -
          Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t)) := by
  have hfun :
      (fun u : ℝ =>
        Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
          (1 - Real.cos (t * u))) =
        (fun u : ℝ =>
          Real.exp (u / 2 - u ^ 2 / (4 * ε)) -
            Real.exp (u / 2 - u ^ 2 / (4 * ε)) * Real.cos (t * u)) := by
    funext u
    ring
  rw [hfun, integral_sub (gaussianContinuousPrimeDensityIntegrable hε)
    (gaussianContinuousPrimeCosineIntegrable hε t)]
  rw [gaussianContinuousPrimeDensityIntegral hε,
    gaussianContinuousPrimeCosineTransform_normalized hε t]
  ring

theorem gaussianContinuousPrimeOscillationEnergy_eq
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianContinuousPrimeOscillationEnergy ε t =
      4 * Real.exp (ε / 4) -
        4 * Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t) := by
  unfold gaussianContinuousPrimeOscillationEnergy
  rw [gaussianContinuousPrimeOscillationIntegral hε t]
  have hsqrt : 0 < Real.sqrt (Real.pi * ε) :=
    Real.sqrt_pos.2 (mul_pos Real.pi_pos hε)
  field_simp [hsqrt.ne']
  ring

/-- The previously closed-form main term is exactly the continuous-PNT
Gaussian energy, rather than merely an algebraically convenient surrogate. -/
theorem gaussianPrimeEnergyMainTerm_eq_continuousPrimeOscillationEnergy
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianPrimeEnergyMainTerm ε t =
      gaussianContinuousPrimeOscillationEnergy ε t := by
  rw [gaussianPrimeEnergyMainTerm_eq,
    gaussianContinuousPrimeOscillationEnergy_eq hε t]

/-- The prime discrepancy is literally atomic von-Mangoldt energy minus its
continuous-PNT comparison energy. -/
theorem gaussianPrimeEnergyDiscrepancy_eq_atomic_sub_continuous
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianPrimeEnergyDiscrepancy ε t =
      gaussianPrimeOscillationEnergy ε t -
        gaussianContinuousPrimeOscillationEnergy ε t := by
  unfold gaussianPrimeEnergyDiscrepancy
  rw [gaussianPrimeEnergyMainTerm_eq_continuousPrimeOscillationEnergy hε t]

/-- Pulling out the common normalization leaves one exact signed comparison
between atomic prime-power mass and continuous density. -/
theorem gaussianPrimeEnergyDiscrepancy_eq_normalized_atomic_sub_continuous
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianPrimeEnergyDiscrepancy ε t =
      2 / Real.sqrt (Real.pi * ε) *
        ((∑' n : ℕ, gaussianPrimeOscillationSummand ε t n) -
          ∫ u : ℝ,
            Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
              (1 - Real.cos (t * u))) := by
  rw [gaussianPrimeEnergyDiscrepancy_eq_atomic_sub_continuous hε t]
  unfold gaussianPrimeOscillationEnergy
    gaussianContinuousPrimeOscillationEnergy
  ring

/-- Expanded measure-discrepancy form: the remaining frontier compares the
Gaussian test kernel against von-Mangoldt atoms at `log n` and against the
continuous density `exp (u / 2) du`. -/
theorem gaussianPrimeEnergyDiscrepancy_eq_vonMangoldtSum_sub_continuousIntegral
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianPrimeEnergyDiscrepancy ε t =
      2 / Real.sqrt (Real.pi * ε) *
        ((∑' n : ℕ,
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            Real.exp (-(Real.log n) ^ 2 / (4 * ε))) *
              (1 - Real.cos (t * Real.log n))) -
          ∫ u : ℝ,
            Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
              (1 - Real.cos (t * u))) := by
  rw [gaussianPrimeEnergyDiscrepancy_eq_normalized_atomic_sub_continuous
    hε t]
  simp_rw [gaussianPrimeOscillationSummand_eq]

/-- After the leading exponential cancellation, the full formula is exactly
endpoint plus digamma gain plus prime discrepancy. -/
theorem gaussianArithmeticExplicitFormula_eq_endpoint_add_digammaGain_add_primeDiscrepancy
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianArithmeticExplicitFormula ε t =
      gaussianArithmeticExplicitFormula ε 0 +
        gaussianDigammaGain ε t +
          gaussianPrimeEnergyDiscrepancy ε t := by
  rw [gaussianArithmeticExplicitFormula_eq_endpoint_add_archimedeanDifference_add_primeEnergy
    hε t]
  unfold gaussianDigammaGain gaussianPrimeEnergyDiscrepancy
    gaussianPrimeEnergyMainTerm gaussianElementaryBoundaryTerm
    gaussianArchimedeanContribution
  norm_num
  ring

/-- Exact pointwise discrepancy budget.  Neither the endpoint nor the
digamma gain may be dropped: broad numerical tests show that both can be the
entire surviving margin after cancellation. -/
theorem gaussianArithmeticExplicitFormula_nonnegative_iff_primeDiscrepancyBudget
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ gaussianArithmeticExplicitFormula ε t ↔
      -gaussianArithmeticExplicitFormula ε 0 ≤
        gaussianDigammaGain ε t +
          gaussianPrimeEnergyDiscrepancy ε t := by
  rw [gaussianArithmeticExplicitFormula_eq_endpoint_add_digammaGain_add_primeDiscrepancy
    hε t]
  constructor <;> intro h <;> linarith

/-- One width satisfies the exact discrepancy budget at every center. -/
def GaussianPrimeDiscrepancyGoodWidth (ε : ℝ) : Prop :=
  0 < ε ∧
    ∀ t : ℝ,
      -gaussianArithmeticExplicitFormula ε 0 ≤
        gaussianDigammaGain ε t +
          gaussianPrimeEnergyDiscrepancy ε t

theorem gaussianPrimeDiscrepancyGoodWidth_iff_gaussianArithmeticGoodWidth
    (ε : ℝ) :
    GaussianPrimeDiscrepancyGoodWidth ε ↔
      GaussianArithmeticGoodWidth ε := by
  constructor
  · rintro ⟨hε, hbudget⟩
    exact ⟨hε, fun t =>
      (gaussianArithmeticExplicitFormula_nonnegative_iff_primeDiscrepancyBudget
        hε t).2 (hbudget t)⟩
  · rintro ⟨hε, hnonnegative⟩
    exact ⟨hε, fun t =>
      (gaussianArithmeticExplicitFormula_nonnegative_iff_primeDiscrepancyBudget
        hε t).1 (hnonnegative t)⟩

/-- Cofinal validity of the cancellation-aware discrepancy budget. -/
def GaussianPrimeDiscrepancyGoodWidthsUnbounded : Prop :=
  ∀ B : ℝ, ∃ ε : ℝ, B < ε ∧ GaussianPrimeDiscrepancyGoodWidth ε

theorem gaussianPrimeDiscrepancyGoodWidthsUnbounded_iff_arithmetic :
    GaussianPrimeDiscrepancyGoodWidthsUnbounded ↔
      GaussianArithmeticGoodWidthsUnbounded := by
  unfold GaussianPrimeDiscrepancyGoodWidthsUnbounded
    GaussianArithmeticGoodWidthsUnbounded
  constructor
  · intro hunbounded B
    obtain ⟨ε, hBε, hε⟩ := hunbounded B
    exact ⟨ε, hBε,
      (gaussianPrimeDiscrepancyGoodWidth_iff_gaussianArithmeticGoodWidth ε).1 hε⟩
  · intro hunbounded B
    obtain ⟨ε, hBε, hε⟩ := hunbounded B
    exact ⟨ε, hBε,
      (gaussianPrimeDiscrepancyGoodWidth_iff_gaussianArithmeticGoodWidth ε).2 hε⟩

/-- The precise cancellation-aware final frontier is still RH-strength. -/
theorem gaussianPrimeDiscrepancyGoodWidthsUnbounded_iff_riemannHypothesis :
    GaussianPrimeDiscrepancyGoodWidthsUnbounded ↔ RiemannHypothesis :=
  gaussianPrimeDiscrepancyGoodWidthsUnbounded_iff_arithmetic.trans
    gaussianArithmeticGoodWidthsUnbounded_iff_riemannHypothesis

/-! ## Finite phase-block lower bounds -/

/-- Normalized positive coefficient of one `1 - cos` energy channel. -/
def gaussianPrimeEnergyWeight (ε : ℝ) (n : ℕ) : ℝ :=
  2 / Real.sqrt (Real.pi * ε) *
    (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      Real.exp (-(Real.log n) ^ 2 / (4 * ε)))

theorem gaussianPrimeEnergyWeight_nonnegative
    (ε : ℝ) (n : ℕ) :
    0 ≤ gaussianPrimeEnergyWeight ε n := by
  unfold gaussianPrimeEnergyWeight
  positivity

/-- Weighted mass of an arbitrary finite prime-power phase block. -/
def gaussianPrimePhaseBlockMass
    (ε : ℝ) (indices : Finset ℕ) : ℝ :=
  ∑ n ∈ indices, gaussianPrimeEnergyWeight ε n

theorem gaussianPrimePartialOscillationEnergy_eq_phaseSum
    (ε t : ℝ) (indices : Finset ℕ) :
    gaussianPrimePartialOscillationEnergy ε t indices =
      ∑ n ∈ indices,
        gaussianPrimeEnergyWeight ε n *
          (1 - Real.cos (t * Real.log n)) := by
  unfold gaussianPrimePartialOscillationEnergy gaussianPrimeEnergyWeight
  simp_rw [gaussianPrimeOscillationSummand_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- If a phase block has the uniform oscillation floor `floor`, its weighted
mass times that floor is a certified lower bound for its energy. -/
theorem gaussianPrimePhaseFloor_mul_mass_le_partialEnergy
    (ε t floor : ℝ) (indices : Finset ℕ)
    (hfloor : ∀ n ∈ indices,
      floor ≤ 1 - Real.cos (t * Real.log n)) :
    floor * gaussianPrimePhaseBlockMass ε indices ≤
      gaussianPrimePartialOscillationEnergy ε t indices := by
  rw [gaussianPrimePartialOscillationEnergy_eq_phaseSum]
  unfold gaussianPrimePhaseBlockMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  calc
    floor * gaussianPrimeEnergyWeight ε n =
        gaussianPrimeEnergyWeight ε n * floor := by ring
    _ ≤ gaussianPrimeEnergyWeight ε n *
        (1 - Real.cos (t * Real.log n)) :=
      mul_le_mul_of_nonneg_left (hfloor n hn)
        (gaussianPrimeEnergyWeight_nonnegative ε n)

/-- Discrepancy formed from a selected finite positive prime block. -/
def gaussianPrimePartialEnergyDiscrepancy
    (ε t : ℝ) (indices : Finset ℕ) : ℝ :=
  gaussianPrimePartialOscillationEnergy ε t indices -
    gaussianPrimeEnergyMainTerm ε t

theorem gaussianPrimePartialEnergyDiscrepancy_le
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) (indices : Finset ℕ) :
    gaussianPrimePartialEnergyDiscrepancy ε t indices ≤
      gaussianPrimeEnergyDiscrepancy ε t := by
  unfold gaussianPrimePartialEnergyDiscrepancy
    gaussianPrimeEnergyDiscrepancy
  exact sub_le_sub_right
    (gaussianPrimePartialOscillationEnergy_le hε t indices) _

/-- A finite phase-block discrepancy budget is sufficient for actual
positivity at the center. -/
theorem gaussianArithmeticExplicitFormula_nonnegative_of_partialDiscrepancyBudget
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) (indices : Finset ℕ)
    (hbudget :
      -gaussianArithmeticExplicitFormula ε 0 ≤
        gaussianDigammaGain ε t +
          gaussianPrimePartialEnergyDiscrepancy ε t indices) :
    0 ≤ gaussianArithmeticExplicitFormula ε t := by
  apply (gaussianArithmeticExplicitFormula_nonnegative_iff_primeDiscrepancyBudget
    hε t).2
  have hpartial :=
    gaussianPrimePartialEnergyDiscrepancy_le hε t indices
  linarith

/-- A lower bound on phase-block mass can be used directly, without first
materializing every individual energy summand. -/
theorem gaussianArithmeticExplicitFormula_nonnegative_of_phaseBlockBudget
    {ε : ℝ} (hε : 0 < ε) (t floor : ℝ) (indices : Finset ℕ)
    (hfloor : ∀ n ∈ indices,
      floor ≤ 1 - Real.cos (t * Real.log n))
    (hbudget :
      -gaussianArithmeticExplicitFormula ε 0 ≤
        gaussianDigammaGain ε t +
          (floor * gaussianPrimePhaseBlockMass ε indices -
            gaussianPrimeEnergyMainTerm ε t)) :
    0 ≤ gaussianArithmeticExplicitFormula ε t := by
  apply gaussianArithmeticExplicitFormula_nonnegative_of_partialDiscrepancyBudget
    hε t indices
  have hphase :=
    gaussianPrimePhaseFloor_mul_mass_le_partialEnergy ε t floor indices hfloor
  unfold gaussianPrimePartialEnergyDiscrepancy
  linarith

end

end RiemannGaussian

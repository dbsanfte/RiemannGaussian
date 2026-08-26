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

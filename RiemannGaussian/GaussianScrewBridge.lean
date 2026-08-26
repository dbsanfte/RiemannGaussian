import RiemannGaussian.GaussianPrimeAbel
import RiemannGaussian.ScrewTransport
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The Gaussian frontier in Suzuki curvature coordinates

The forward Gaussian prime discrepancy and Suzuki's screw-function curvature
use the same positive logarithmic coordinate.  This file checks their exact
algebraic and measure-theoretic compatibility.

On `u > 0`, the quarter-line digamma density splits as

`exp (-u / 2) / (1 - exp (-2u)) = exp (-u / 2) + suzukiMissingCurvature u`.

The missing-curvature energy is genuinely integrable: near zero the factor
`1 - cos (t*u)` cancels the density's simple pole, while at infinity an
explicit `exp (-5u/2)` majorant applies.  Subtracting this energy from the
forward continuous-PNT Gaussian energy gives the literal Gaussian transform
of `suzukiSmoothCurvature`.

The conditional interface exposed in this file is
`GaussianDigammaScrewTransform`.  It says that the already-defined digamma
remainder equals the checked missing-curvature integral.  It is passed
explicitly to every theorem in this dependency layer, not declared as an
axiom.  `GaussianDigammaTransform` reduces it to one pointwise quarter-line
Gauss difference formula, and `GaussianDigammaGauss` subsequently proves that
formula and discharges the interface unconditionally.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory Topology
open scoped BigOperators Topology

/-! ## The missing-curvature density and its Gaussian energy -/

/-- The positive-half-line density supplied by Gauss's quarter-line digamma
representation before its reflected exponential part is removed. -/
def gaussianSuzukiDigammaDensity (u : ℝ) : ℝ :=
  Real.exp (-u / 2) / (1 - Real.exp (-2 * u))

/-- Exact pointwise split of the quarter-line digamma density into the
reflected continuous-PNT density and Suzuki's missing curvature. -/
theorem gaussianSuzukiDigammaDensity_eq_reflected_add_missing
    {u : ℝ} (hu : 0 < u) :
    gaussianSuzukiDigammaDensity u =
      Real.exp (-u / 2) + suzukiMissingCurvature u := by
  have hden := (one_sub_exp_neg_two_mul_pos hu).ne'
  unfold gaussianSuzukiDigammaDensity suzukiMissingCurvature
  have hden' : 1 - Real.exp (-(u * 2)) ≠ 0 := by
    have harg : -(u * 2) = -2 * u := by ring
    rw [harg]
    exact hden
  field_simp [hden']
  have hexp :
      Real.exp (-(u / 2)) * Real.exp (-(u * 2)) =
        Real.exp (-(u * 5 / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_sub, mul_one, hexp]
  ring

/-- Elementary lower bound for the denominator near the origin.  Its weak
constant is chosen to make the singularity estimate completely explicit. -/
lemma two_thirds_mul_le_one_sub_exp_neg_two_mul
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    (2 / 3 : ℝ) * u ≤ 1 - Real.exp (-2 * u) := by
  have hbase : 0 < 1 + 2 * u := by linarith
  have hexp : 1 + 2 * u ≤ Real.exp (2 * u) := by
    linarith [Real.add_one_le_exp (2 * u)]
  have hinv : Real.exp (-2 * u) ≤ 1 / (1 + 2 * u) := by
    rw [show -2 * u = -(2 * u) by ring, Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le hbase hexp
  calc
    (2 / 3 : ℝ) * u ≤ 2 * u / (1 + 2 * u) := by
      rw [le_div_iff₀ hbase]
      nlinarith
    _ = 1 - 1 / (1 + 2 * u) := by
      field_simp [hbase.ne']
      ring
    _ ≤ 1 - Real.exp (-2 * u) := sub_le_sub_left hinv 1

/-- The normalized-integral kernel whose integral is the missing-curvature
energy (without its common Gaussian normalization). -/
def gaussianSuzukiMissingCurvatureIntegrand (ε t u : ℝ) : ℝ :=
  Real.exp (-u ^ 2 / (4 * ε)) *
    suzukiMissingCurvature u * (1 - Real.cos (t * u))

theorem continuousOn_gaussianSuzukiMissingCurvatureIntegrand
    (ε t : ℝ) :
    ContinuousOn (gaussianSuzukiMissingCurvatureIntegrand ε t)
      (Set.Ioi 0) := by
  intro u hu
  have hden : 1 - Real.exp (-2 * u) ≠ 0 :=
    (one_sub_exp_neg_two_mul_pos hu).ne'
  unfold gaussianSuzukiMissingCurvatureIntegrand suzukiMissingCurvature
  fun_prop

/-- The oscillation cancels the apparent `1/u` singularity at the origin. -/
lemma norm_gaussianSuzukiMissingCurvatureIntegrand_le_near_zero
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) {u : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) :
    ‖gaussianSuzukiMissingCurvatureIntegrand ε t u‖ ≤
      (3 / 2 : ℝ) * |t| := by
  have hdenpos := one_sub_exp_neg_two_mul_pos hu
  have hden := two_thirds_mul_le_one_sub_exp_neg_two_mul hu hu1
  have hgaussian : Real.exp (-u ^ 2 / (4 * ε)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg u)) (mul_nonneg (by norm_num) hε.le)
  have hnumerator : Real.exp (-(5 * u) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hoscNonneg : 0 ≤ 1 - Real.cos (t * u) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  have hosc : 1 - Real.cos (t * u) ≤ |t| * u := by
    calc
      1 - Real.cos (t * u) = |1 - Real.cos (t * u)| :=
        (abs_of_nonneg hoscNonneg).symm
      _ = |Real.cos (t * u) - Real.cos 0| := by
        rw [Real.cos_zero, abs_sub_comm]
      _ ≤ |t * u - 0| := Real.abs_cos_sub_cos_le _ _
      _ = |t| * u := by rw [sub_zero, abs_mul, abs_of_pos hu]
  unfold gaussianSuzukiMissingCurvatureIntegrand suzukiMissingCurvature
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (mul_nonneg (Real.exp_pos _).le
      (div_nonneg (Real.exp_pos _).le hdenpos.le)) hoscNonneg)]
  calc
    Real.exp (-u ^ 2 / (4 * ε)) *
          (Real.exp (-(5 * u) / 2) / (1 - Real.exp (-2 * u))) *
        (1 - Real.cos (t * u)) ≤
      1 * (1 / ((2 / 3 : ℝ) * u)) * (|t| * u) := by
        gcongr
    _ = (3 / 2 : ℝ) * |t| := by
      field_simp [hu.ne']

theorem integrableOn_gaussianSuzukiMissingCurvatureIntegrand_Ioc
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    IntegrableOn (gaussianSuzukiMissingCurvatureIntegrand ε t)
      (Set.Ioc (0 : ℝ) 1) := by
  apply IntegrableOn.of_bound measure_Ioc_lt_top
  · exact ((continuousOn_gaussianSuzukiMissingCurvatureIntegrand ε t).mono
      Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact norm_gaussianSuzukiMissingCurvatureIntegrand_le_near_zero
      hε t hu.1 hu.2

/-- Beyond one, the missing-curvature integrand is bounded by a fixed
multiple of `exp (-5u/2)`. -/
lemma norm_gaussianSuzukiMissingCurvatureIntegrand_le_tail
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    ‖gaussianSuzukiMissingCurvatureIntegrand ε t u‖ ≤
      (2 / (1 - Real.exp (-2))) *
        Real.exp (-(5 / 2 : ℝ) * u) := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hdenpos := one_sub_exp_neg_two_mul_pos hu0
  have hfixedDen : 0 < 1 - Real.exp (-2) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hden : 1 - Real.exp (-2) ≤ 1 - Real.exp (-2 * u) := by
    apply sub_le_sub_left
    apply Real.exp_le_exp.mpr
    nlinarith
  have hgaussian : Real.exp (-u ^ 2 / (4 * ε)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg u)) (mul_nonneg (by norm_num) hε.le)
  have hoscNonneg : 0 ≤ 1 - Real.cos (t * u) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  have hosc : 1 - Real.cos (t * u) ≤ 2 := by
    linarith [Real.neg_one_le_cos (t * u)]
  unfold gaussianSuzukiMissingCurvatureIntegrand suzukiMissingCurvature
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (mul_nonneg (Real.exp_pos _).le
      (div_nonneg (Real.exp_pos _).le hdenpos.le)) hoscNonneg)]
  calc
    Real.exp (-u ^ 2 / (4 * ε)) *
          (Real.exp (-(5 * u) / 2) / (1 - Real.exp (-2 * u))) *
        (1 - Real.cos (t * u)) ≤
      1 * (Real.exp (-(5 * u) / 2) /
        (1 - Real.exp (-2))) * 2 := by
        gcongr
    _ = (2 / (1 - Real.exp (-2))) *
        Real.exp (-(5 / 2 : ℝ) * u) := by
      rw [show Real.exp (-(5 * u) / 2) =
          Real.exp (-(5 / 2 : ℝ) * u) by
        congr 1
        ring]
      ring

theorem integrableOn_gaussianSuzukiMissingCurvatureIntegrand_Ioi_one
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    IntegrableOn (gaussianSuzukiMissingCurvatureIntegrand ε t)
      (Set.Ioi (1 : ℝ)) := by
  let C : ℝ := 2 / (1 - Real.exp (-2))
  have hmajor : IntegrableOn
      (fun u : ℝ => C * Real.exp (-(5 / 2 : ℝ) * u))
      (Set.Ioi (1 : ℝ)) := by
    exact (exp_neg_integrableOn_Ioi 1
      (by norm_num : (0 : ℝ) < 5 / 2)).const_mul C
  apply hmajor.mono'
  · exact ((continuousOn_gaussianSuzukiMissingCurvatureIntegrand ε t).mono
      (by
        intro u hu
        change 1 < u at hu
        exact zero_lt_one.trans hu)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 1 < u at hu
    exact norm_gaussianSuzukiMissingCurvatureIntegrand_le_tail hε t hu.le

/-- The missing-curvature kernel is integrable on the complete positive
half-line for every positive Gaussian width. -/
theorem integrableOn_gaussianSuzukiMissingCurvatureIntegrand
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    IntegrableOn (gaussianSuzukiMissingCurvatureIntegrand ε t)
      (Set.Ioi (0 : ℝ)) := by
  have h :=
    (integrableOn_gaussianSuzukiMissingCurvatureIntegrand_Ioc hε t).union
      (integrableOn_gaussianSuzukiMissingCurvatureIntegrand_Ioi_one hε t)
  rw [show Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 by
    ext u
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (hu | hu)
      · exact hu.1
      · linarith
    · intro hu
      by_cases hu1 : u ≤ 1
      · exact Or.inl ⟨hu, hu1⟩
      · exact Or.inr (lt_of_not_ge hu1)] at h
  exact h

/-- The Gaussian transform of Suzuki's missing curvature. -/
def gaussianSuzukiMissingCurvatureEnergy (ε t : ℝ) : ℝ :=
  2 / Real.sqrt (Real.pi * ε) *
    ∫ u in Set.Ioi (0 : ℝ),
      gaussianSuzukiMissingCurvatureIntegrand ε t u

theorem gaussianSuzukiMissingCurvatureEnergy_nonnegative (ε t : ℝ) :
    0 ≤ gaussianSuzukiMissingCurvatureEnergy ε t := by
  unfold gaussianSuzukiMissingCurvatureEnergy
  apply mul_nonneg (by positivity)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le
      (suzukiMissingCurvature_pos hu).le)
    (sub_nonneg.mpr (Real.cos_le_one _))

/-! ## The exact smooth-curvature transform -/

/-- The Gaussian oscillation kernel applied to Suzuki's exact smooth
curvature. -/
def gaussianSuzukiSmoothCurvatureIntegrand (ε t u : ℝ) : ℝ :=
  Real.exp (-u ^ 2 / (4 * ε)) *
    suzukiSmoothCurvature u * (1 - Real.cos (t * u))

theorem integral_gaussianSuzukiSmoothCurvatureIntegrand_eq_forward_sub_missing
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ u in Set.Ioi (0 : ℝ),
        gaussianSuzukiSmoothCurvatureIntegrand ε t u) =
      (∫ u in Set.Ioi (0 : ℝ),
        Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
          (1 - Real.cos (t * u))) -
      ∫ u in Set.Ioi (0 : ℝ),
        gaussianSuzukiMissingCurvatureIntegrand ε t u := by
  let forward : ℝ → ℝ := fun u =>
    Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
      (1 - Real.cos (t * u))
  have hforward : IntegrableOn forward (Set.Ioi (0 : ℝ)) :=
    (gaussianContinuousPrimeOscillationIntegrable hε t).integrableOn
  have hmissing :=
    integrableOn_gaussianSuzukiMissingCurvatureIntegrand hε t
  rw [← integral_sub hforward hmissing]
  apply integral_congr_ae
  filter_upwards with u
  have hfactor :
      Real.exp (-u ^ 2 / (4 * ε)) * Real.exp (u / 2) =
        Real.exp (u / 2 - u ^ 2 / (4 * ε)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold gaussianSuzukiSmoothCurvatureIntegrand
    gaussianSuzukiMissingCurvatureIntegrand forward
  unfold suzukiSmoothCurvature
  calc
    Real.exp (-u ^ 2 / (4 * ε)) *
          (Real.exp (u / 2) - suzukiMissingCurvature u) *
          (1 - Real.cos (t * u)) =
        (Real.exp (-u ^ 2 / (4 * ε)) * Real.exp (u / 2)) *
            (1 - Real.cos (t * u)) -
          Real.exp (-u ^ 2 / (4 * ε)) * suzukiMissingCurvature u *
            (1 - Real.cos (t * u)) := by ring
    _ = _ := by rw [hfactor]

/-- The literal Gaussian transform of Suzuki's smooth curvature. -/
def gaussianSuzukiSmoothCurvatureEnergy (ε t : ℝ) : ℝ :=
  2 / Real.sqrt (Real.pi * ε) *
    ∫ u in Set.Ioi (0 : ℝ),
      gaussianSuzukiSmoothCurvatureIntegrand ε t u

theorem gaussianSuzukiSmoothCurvatureEnergy_eq_forward_sub_missing
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianSuzukiSmoothCurvatureEnergy ε t =
      gaussianForwardContinuousPrimeOscillationEnergy ε t -
        gaussianSuzukiMissingCurvatureEnergy ε t := by
  unfold gaussianSuzukiSmoothCurvatureEnergy
  rw [integral_gaussianSuzukiSmoothCurvatureIntegrand_eq_forward_sub_missing
    hε t]
  change
    2 / Real.sqrt (Real.pi * ε) *
          ((∫ u in Set.Ioi (0 : ℝ),
              Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
                (1 - Real.cos (t * u))) -
            ∫ u in Set.Ioi (0 : ℝ),
              gaussianSuzukiMissingCurvatureIntegrand ε t u) =
      2 / Real.sqrt (Real.pi * ε) *
          (∫ u in Set.Ioi (0 : ℝ),
            Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
              (1 - Real.cos (t * u))) -
        2 / Real.sqrt (Real.pi * ε) *
          ∫ u in Set.Ioi (0 : ℝ),
            gaussianSuzukiMissingCurvatureIntegrand ε t u
  ring

/-- The forward atomic discrepancy plus the missing curvature is precisely
prime energy minus exact Suzuki smooth-curvature energy. -/
theorem gaussianForwardDiscrepancy_add_missing_eq_prime_sub_smooth
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianForwardPrimeEnergyDiscrepancy ε t +
        gaussianSuzukiMissingCurvatureEnergy ε t =
      gaussianPrimeOscillationEnergy ε t -
        gaussianSuzukiSmoothCurvatureEnergy ε t := by
  rw [gaussianSuzukiSmoothCurvatureEnergy_eq_forward_sub_missing hε t]
  unfold gaussianForwardPrimeEnergyDiscrepancy
  ring

/-! ## The digamma bridge interface and the RH-equivalent budget -/

/-- The precise analytic identity supplied by Gauss's integral representation
of `digamma`: after removing the reflected continuous-PNT half, the digamma
gain is Suzuki's positive missing-curvature energy.

This dependency layer exposes it as a proposition, not an axiom; all dependent
results below take its proof as an explicit argument.  It is proved in
`GaussianDigammaGauss`. -/
def GaussianDigammaScrewTransform : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ∀ t : ℝ,
    gaussianDigammaRemainderGain ε t =
      gaussianSuzukiMissingCurvatureEnergy ε t

/-- Conditional only on the named digamma transform, the complete arithmetic
formula is endpoint plus atomic prime energy minus exact smooth curvature. -/
theorem gaussianArithmeticExplicitFormula_eq_endpoint_add_primeEnergy_sub_suzukiSmooth
    (htransform : GaussianDigammaScrewTransform)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianArithmeticExplicitFormula ε t =
      gaussianArithmeticExplicitFormula ε 0 +
        gaussianPrimeOscillationEnergy ε t -
          gaussianSuzukiSmoothCurvatureEnergy ε t := by
  calc
    gaussianArithmeticExplicitFormula ε t =
        gaussianArithmeticExplicitFormula ε 0 +
          (gaussianDigammaGain ε t +
            gaussianPrimeEnergyDiscrepancy ε t) := by
      rw [gaussianArithmeticExplicitFormula_eq_endpoint_add_digammaGain_add_primeDiscrepancy
        hε t]
      ring
    _ = gaussianArithmeticExplicitFormula ε 0 +
          (gaussianForwardPrimeEnergyDiscrepancy ε t +
            gaussianDigammaRemainderGain ε t) := by
      rw [gaussianDigammaGain_add_primeEnergyDiscrepancy_eq_forward_add_remainder
        hε t]
    _ = gaussianArithmeticExplicitFormula ε 0 +
          (gaussianForwardPrimeEnergyDiscrepancy ε t +
            gaussianSuzukiMissingCurvatureEnergy ε t) := by
      rw [htransform hε t]
    _ = _ := by
      rw [gaussianForwardDiscrepancy_add_missing_eq_prime_sub_smooth hε t]
      ring

/-- Equivalent one-sided form of the same identity, before the continuous
PNT density and missing curvature are recombined into smooth curvature. -/
theorem gaussianArithmeticExplicitFormula_eq_endpoint_add_forwardDiscrepancy_add_missing
    (htransform : GaussianDigammaScrewTransform)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianArithmeticExplicitFormula ε t =
      gaussianArithmeticExplicitFormula ε 0 +
        gaussianForwardPrimeEnergyDiscrepancy ε t +
          gaussianSuzukiMissingCurvatureEnergy ε t := by
  rw [gaussianArithmeticExplicitFormula_eq_endpoint_add_primeEnergy_sub_suzukiSmooth
      htransform hε t,
    gaussianSuzukiSmoothCurvatureEnergy_eq_forward_sub_missing hε t]
  unfold gaussianForwardPrimeEnergyDiscrepancy
  ring

/-- The complete conditional chain from the improper Chebyshev-error
integrals to the arithmetic Gaussian value.  The only hypothesis beyond
positive width is the named digamma transform. -/
theorem tendsto_gaussianArithmeticExplicitFormula_from_chebyshevError_add_missing
    (htransform : GaussianDigammaScrewTransform)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        gaussianArithmeticExplicitFormula ε 0 +
          gaussianSuzukiMissingCurvatureEnergy ε t +
          2 / Real.sqrt (Real.pi * ε) *
            ∫ x in Set.Ioc (1 : ℝ) (n : ℝ),
              gaussianPrimeAbelKernelDerivative ε t x *
                (x - Chebyshev.psi x))
      atTop (𝓝 (gaussianArithmeticExplicitFormula ε t)) := by
  have hconstant : Tendsto
      (fun _ : ℕ => gaussianArithmeticExplicitFormula ε 0 +
        gaussianSuzukiMissingCurvatureEnergy ε t)
      atTop
      (𝓝 (gaussianArithmeticExplicitFormula ε 0 +
        gaussianSuzukiMissingCurvatureEnergy ε t)) :=
    tendsto_const_nhds
  have h := hconstant.add
    (tendsto_gaussianPrimeExplicitChebyshevErrorIntegral hε t)
  rw [gaussianArithmeticExplicitFormula_eq_endpoint_add_forwardDiscrepancy_add_missing
    htransform hε t]
  convert h using 1
  congr 1
  ring

/-- At one width, the Suzuki formulation asks whether exact smooth curvature
is paid for by the endpoint margin plus the positive atomic prime energy. -/
def GaussianSuzukiEnergyGoodWidth (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ t : ℝ,
    gaussianSuzukiSmoothCurvatureEnergy ε t ≤
      gaussianArithmeticExplicitFormula ε 0 +
        gaussianPrimeOscillationEnergy ε t

theorem gaussianSuzukiEnergyGoodWidth_iff_gaussianArithmeticGoodWidth
    (htransform : GaussianDigammaScrewTransform) (ε : ℝ) :
    GaussianSuzukiEnergyGoodWidth ε ↔ GaussianArithmeticGoodWidth ε := by
  constructor
  · rintro ⟨hε, hbudget⟩
    refine ⟨hε, fun t => ?_⟩
    rw [gaussianArithmeticExplicitFormula_eq_endpoint_add_primeEnergy_sub_suzukiSmooth
      htransform hε t]
    linarith [hbudget t]
  · rintro ⟨hε, hnonnegative⟩
    refine ⟨hε, fun t => ?_⟩
    have ht := hnonnegative t
    rw [gaussianArithmeticExplicitFormula_eq_endpoint_add_primeEnergy_sub_suzukiSmooth
      htransform hε t] at ht
    linarith

/-- Cofinal validity of the exact Suzuki smooth-curvature energy budget. -/
def GaussianSuzukiEnergyGoodWidthsUnbounded : Prop :=
  ∀ B : ℝ, ∃ ε : ℝ, B < ε ∧ GaussianSuzukiEnergyGoodWidth ε

theorem gaussianSuzukiEnergyGoodWidthsUnbounded_iff_arithmetic
    (htransform : GaussianDigammaScrewTransform) :
    GaussianSuzukiEnergyGoodWidthsUnbounded ↔
      GaussianArithmeticGoodWidthsUnbounded := by
  unfold GaussianSuzukiEnergyGoodWidthsUnbounded
    GaussianArithmeticGoodWidthsUnbounded
  constructor
  · intro h B
    obtain ⟨ε, hBε, hε⟩ := h B
    exact ⟨ε, hBε,
      (gaussianSuzukiEnergyGoodWidth_iff_gaussianArithmeticGoodWidth
        htransform ε).1 hε⟩
  · intro h B
    obtain ⟨ε, hBε, hε⟩ := h B
    exact ⟨ε, hBε,
      (gaussianSuzukiEnergyGoodWidth_iff_gaussianArithmeticGoodWidth
        htransform ε).2 hε⟩

/-- Once Gauss's digamma transform is supplied, cofinal Suzuki energy
budgets are exactly RH.  This does not prove either side. -/
theorem gaussianSuzukiEnergyGoodWidthsUnbounded_iff_riemannHypothesis
    (htransform : GaussianDigammaScrewTransform) :
    GaussianSuzukiEnergyGoodWidthsUnbounded ↔ RiemannHypothesis :=
  (gaussianSuzukiEnergyGoodWidthsUnbounded_iff_arithmetic htransform).trans
    gaussianArithmeticGoodWidthsUnbounded_iff_riemannHypothesis

end

end RiemannGaussian

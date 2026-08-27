import RiemannGaussian.RiemannXiSuzukiCoefficientHilbert

/-!
# Infinite Suzuki spectral evaluation at the safe point

Suzuki's meromorphic spectral function has terms

`m_alpha * coefficient(t, alpha) / (z - alpha)`.

At the fixed point `z = i`, its Cauchy denominator is exactly `i` times the
first-order resolvent denominator already used by the screw-growth attack.
This file proves that the corresponding conjugate evaluation coordinates form
an unconditional `ℓ²` vector.  Pairing that vector with the complete Suzuki
coefficient vector therefore produces an absolutely convergent infinite
spectral value `P_t(i)`.  Genuine symmetric zeta-zero windows converge to this
value, and the value obeys the exact Hilbert-space Cauchy--Schwarz bound.

This is the first infinite Suzuki `P_t` quantity in the formal chain.  It is
still defined from the spectral zero expansion.  Identifying it with Suzuki's
prime/gamma arithmetic formula, and lifting one-point evaluation to the full
arithmetic `L²(R)` signal, remain separate theorems that are not assumed here.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The Cauchy denominator at Suzuki's safe evaluation point `z = i`. -/
def suzukiXiSafeEvaluationDenominator (alpha : ℂ) : ℂ :=
  Complex.I - alpha

/-- Evaluation at `i` is exactly the existing first-order screw resolvent,
up to the unit scalar `i`. -/
theorem suzukiXiSafeEvaluationDenominator_eq_resolvent
    (alpha : ℂ) :
    suzukiXiSafeEvaluationDenominator alpha =
      Complex.I * spectralScrewResolventDenominator alpha := by
  unfold suzukiXiSafeEvaluationDenominator
    spectralScrewResolventDenominator
  calc
    Complex.I - alpha = Complex.I + (-1) * alpha := by ring
    _ = Complex.I + Complex.I ^ 2 * alpha := by rw [Complex.I_sq]
    _ = Complex.I * (1 + Complex.I * alpha) := by ring

/-- The safe Cauchy denominator and screw resolvent have identical squared
norm. -/
theorem normSq_suzukiXiSafeEvaluationDenominator
    (alpha : ℂ) :
    Complex.normSq (suzukiXiSafeEvaluationDenominator alpha) =
      Complex.normSq (spectralScrewResolventDenominator alpha) := by
  rw [suzukiXiSafeEvaluationDenominator_eq_resolvent,
    Complex.normSq_mul, Complex.normSq_I, one_mul]

/-- The safe denominator is nonzero at every genuine nontrivial zeta zero. -/
theorem normSq_suzukiXiSafeEvaluationDenominator_pos
    (rho : NontrivialZetaZero) :
    0 < Complex.normSq
      (suzukiXiSafeEvaluationDenominator
        (zetaSpectralCoordinate rho.1)) := by
  rw [normSq_suzukiXiSafeEvaluationDenominator]
  exact spectralScrewResolventDenominator_normSq_pos rho

/-- The conjugate Cauchy-evaluation coordinate used as the first argument of
the complex Hilbert inner product. -/
def zetaSuzukiSafeEvaluationFeature
    (rho : NontrivialZetaZero) : ℂ :=
  (Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) /
    starRingEnd ℂ
      (suzukiXiSafeEvaluationDenominator
        (zetaSpectralCoordinate rho.1))

/-- The positive squared-norm contribution of one safe-evaluation
coordinate. -/
def zetaSuzukiSafeEvaluationEnergy
    (rho : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity rho : ℝ) /
    Complex.normSq
      (suzukiXiSafeEvaluationDenominator
        (zetaSpectralCoordinate rho.1))

/-- The squared modulus of the safe-evaluation coordinate is its positive
energy. -/
theorem normSq_zetaSuzukiSafeEvaluationFeature
    (rho : NontrivialZetaZero) :
    Complex.normSq (zetaSuzukiSafeEvaluationFeature rho) =
      zetaSuzukiSafeEvaluationEnergy rho := by
  rw [zetaSuzukiSafeEvaluationFeature, Complex.normSq_div,
    Complex.normSq_ofReal, Complex.normSq_conj,
    Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rfl

/-- Every safe-evaluation energy is nonnegative. -/
theorem zetaSuzukiSafeEvaluationEnergy_nonneg
    (rho : NontrivialZetaZero) :
    0 ≤ zetaSuzukiSafeEvaluationEnergy rho := by
  unfold zetaSuzukiSafeEvaluationEnergy
  exact div_nonneg (Nat.cast_nonneg _)
    (normSq_suzukiXiSafeEvaluationDenominator_pos rho).le

/-- Safe-evaluation energy is dominated by four times the summable
inverse-square xi-divisor weight. -/
theorem zetaSuzukiSafeEvaluationEnergy_le_inverseSquare
    (rho : NontrivialZetaZero) :
    zetaSuzukiSafeEvaluationEnergy rho ≤
      4 * ((analyticZetaZeroMultiplicity rho : ℝ) /
        (1 + (zetaSpectralCoordinate rho.1).re ^ 2)) := by
  let m : ℝ := analyticZetaZeroMultiplicity rho
  let D : ℝ := Complex.normSq
    (suzukiXiSafeEvaluationDenominator
      (zetaSpectralCoordinate rho.1))
  let Q : ℝ := 1 + (zetaSpectralCoordinate rho.1).re ^ 2
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hD : 0 < D :=
    normSq_suzukiXiSafeEvaluationDenominator_pos rho
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  have hden : Q ≤ 4 * D := by
    dsimp [D]
    rw [normSq_suzukiXiSafeEvaluationDenominator]
    exact one_add_spectral_re_sq_le_four_mul_screwResolvent_normSq rho
  have hrecip : 1 / D ≤ 4 / Q := by
    rw [div_le_div_iff₀ hD hQ]
    simpa only [one_mul] using hden
  change m / D ≤ 4 * (m / Q)
  calc
    m / D = m * (1 / D) := by ring
    _ ≤ m * (4 / Q) := mul_le_mul_of_nonneg_left hrecip hm
    _ = 4 * (m / Q) := by ring

/-- The complete safe-evaluation energy is unconditionally summable. -/
theorem summable_zetaSuzukiSafeEvaluationEnergy :
    Summable zetaSuzukiSafeEvaluationEnergy := by
  apply
    (summable_distinct_zetaZeroInverseSquareSpectralRe.mul_left 4).of_nonneg_of_le
      zetaSuzukiSafeEvaluationEnergy_nonneg
  exact zetaSuzukiSafeEvaluationEnergy_le_inverseSquare

/-- The safe-evaluation coordinates form a square-summable family. -/
theorem summable_norm_sq_zetaSuzukiSafeEvaluationFeature :
    Summable (fun rho : NontrivialZetaZero ↦
      ‖zetaSuzukiSafeEvaluationFeature rho‖ ^ 2) := by
  simpa only [Complex.sq_norm,
    normSq_zetaSuzukiSafeEvaluationFeature] using
      summable_zetaSuzukiSafeEvaluationEnergy

/-- Safe evaluation at `z = i` as a literal vector in coefficient space. -/
def riemannXiSuzukiSafeEvaluationVector :
    ℓ²(NontrivialZetaZero, ℂ) :=
  ⟨zetaSuzukiSafeEvaluationFeature, by
    apply memℓp_gen
    simpa using summable_norm_sq_zetaSuzukiSafeEvaluationFeature⟩

/-- One term of Suzuki's spectral `P_t` evaluated at the safe point `z=i`. -/
def zetaSuzukiSpectralPAtISummand
    (t : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  (analyticZetaZeroMultiplicity rho : ℂ) *
    suzukiSpectralScrewCoefficient t
      (zetaSpectralCoordinate rho.1) /
        suzukiXiSafeEvaluationDenominator
          (zetaSpectralCoordinate rho.1)

/-- Each safe-point `P_t` summand is exactly the scalar Hilbert pairing of
the safe-evaluation coordinate with Suzuki's coefficient coordinate. -/
theorem zetaSuzukiSpectralPAtISummand_eq_inner
    (t : ℝ) (rho : NontrivialZetaZero) :
    zetaSuzukiSpectralPAtISummand t rho =
      inner ℂ (zetaSuzukiSafeEvaluationFeature rho)
        (zetaSuzukiSpectralCoefficientFeature t rho) := by
  rw [RCLike.inner_apply]
  unfold zetaSuzukiSpectralPAtISummand
    zetaSuzukiSafeEvaluationFeature
    zetaSuzukiSpectralCoefficientFeature
  simp [div_eq_mul_inv]
  have hsqrt :
      (Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) ^ 2 =
        (analyticZetaZeroMultiplicity rho : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  rw [← hsqrt]
  ring

/-- The safe-point Suzuki spectral series is absolutely summable. -/
theorem summable_zetaSuzukiSpectralPAtISummand (t : ℝ) :
    Summable (zetaSuzukiSpectralPAtISummand t) := by
  refine
    (lp.summable_inner riemannXiSuzukiSafeEvaluationVector
      (riemannXiSuzukiSpectralCoefficientVector t)).congr ?_
  intro rho
  exact (zetaSuzukiSpectralPAtISummand_eq_inner t rho).symm

/-- The first genuine infinite spectral `P_t` value, evaluated at `z=i`. -/
def riemannXiSuzukiSpectralPAtI (t : ℝ) : ℂ :=
  ∑' rho : NontrivialZetaZero,
    zetaSuzukiSpectralPAtISummand t rho

/-- The infinite safe-point spectral `P_t` is exactly a Hilbert pairing. -/
theorem riemannXiSuzukiSpectralPAtI_eq_inner (t : ℝ) :
    riemannXiSuzukiSpectralPAtI t =
      inner ℂ riemannXiSuzukiSafeEvaluationVector
        (riemannXiSuzukiSpectralCoefficientVector t) := by
  rw [riemannXiSuzukiSpectralPAtI, lp.inner_eq_tsum]
  apply tsum_congr
  exact zetaSuzukiSpectralPAtISummand_eq_inner t

/-- Genuine symmetric spectral windows converge to the infinite safe-point
Suzuki `P_t` value. -/
theorem tendsto_suzukiXiSpectralPWindow_at_I (t : ℝ) :
    Tendsto (fun T : ℝ ↦
      suzukiXiSpectralPWindow t T Complex.I) atTop
        (nhds (riemannXiSuzukiSpectralPAtI t)) := by
  have hsum := (summable_zetaSuzukiSpectralPAtISummand t).hasSum
  change Tendsto
    (fun T : ℝ ↦
      ∑ rho ∈ spectralZetaZeroWindow T,
        zetaSuzukiSpectralPAtISummand t rho) atTop
      (nhds (riemannXiSuzukiSpectralPAtI t))
  unfold riemannXiSuzukiSpectralPAtI
  exact hsum.comp tendsto_spectralZetaZeroWindow_atTop

/-- Cauchy--Schwarz controls the infinite safe-point `P_t` value by the two
explicit coefficient-space vectors. -/
theorem norm_riemannXiSuzukiSpectralPAtI_le (t : ℝ) :
    ‖riemannXiSuzukiSpectralPAtI t‖ ≤
      ‖riemannXiSuzukiSafeEvaluationVector‖ *
        ‖riemannXiSuzukiSpectralCoefficientVector t‖ := by
  rw [riemannXiSuzukiSpectralPAtI_eq_inner]
  exact norm_inner_le_norm _ _

/-- The infinite safe-point spectral `P_t` starts at zero. -/
@[simp] theorem riemannXiSuzukiSpectralPAtI_zero_time :
    riemannXiSuzukiSpectralPAtI 0 = 0 := by
  rw [riemannXiSuzukiSpectralPAtI_eq_inner]
  simp

end

end RiemannGaussian

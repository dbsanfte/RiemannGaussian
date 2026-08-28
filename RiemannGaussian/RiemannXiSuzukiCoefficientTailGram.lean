import RiemannGaussian.RiemannXiSuzukiRealZeroNormBound

/-!
# The cancellation-sensitive Suzuki coefficient-tail Gram frontier

A uniform Bessel bound for every finite coefficient family is sufficient for
the infinite Suzuki synthesis, but may be stronger than necessary.  This file
isolates the exact weaker target along Suzuki's one genuine coefficient path.

The difference of two spectral coefficient windows is represented as a
finitely supported family.  Its genuine Gram quadratic is proved equal to the
squared boundary `L²` distance of the normalized signals, while its canonical
coordinate norm is the `ℓ²` distance of the already convergent coefficient
windows.  An eventual quadratic comparison along these tails is therefore
enough for boundary convergence.  This comparison is a named proposition and
is not asserted here.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The finitely supported difference of two genuine Suzuki coefficient
windows. -/
def riemannXiSuzukiSpectralCoefficientTailFinsupp
    (t T U : ℝ) : NontrivialZetaZero →₀ ℂ :=
  riemannXiSuzukiSpectralCoefficientWindowFinsupp t T -
    riemannXiSuzukiSpectralCoefficientWindowFinsupp t U

/-- The genuine zero-function Gram quadratic of one coefficient-window
difference. -/
def suzukiXiCoefficientTailGramQuadratic (t T U : ℝ) : ℂ :=
  suzukiXiZeroFunctionFinsuppGramQuadratic
    (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U)

/-- Finite synthesis of a coefficient tail is exactly the difference of the
two normalized boundary signals. -/
theorem suzukiXiZeroFunctionFiniteSynthesis_coefficientTail
    (t T U : ℝ) :
    suzukiXiZeroFunctionFiniteSynthesis
        (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U) =
      suzukiRealAxisNormalizedSignalWindowSynthesisLp t T -
        suzukiRealAxisNormalizedSignalWindowSynthesisLp t U := by
  simp only [riemannXiSuzukiSpectralCoefficientTailFinsupp, map_sub,
    suzukiXiZeroFunctionFiniteSynthesis_window]

/-- Canonical embedding of a coefficient tail is exactly the difference of
the two `ℓ²` coefficient windows. -/
theorem suzukiXiFiniteCoefficientEmbedding_coefficientTail
    (t T U : ℝ) :
    suzukiXiFiniteCoefficientEmbedding
        (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U) =
      riemannXiSuzukiSpectralCoefficientWindowVector t T -
        riemannXiSuzukiSpectralCoefficientWindowVector t U := by
  simp only [riemannXiSuzukiSpectralCoefficientTailFinsupp, map_sub,
    suzukiXiFiniteCoefficientEmbedding_window]

/-- The real part of the coefficient-tail Gram quadratic is exactly the
squared boundary distance of the normalized signals. -/
theorem suzukiXiCoefficientTailGramQuadratic_re
    (t T U : ℝ) :
    (suzukiXiCoefficientTailGramQuadratic t T U).re =
      ‖suzukiRealAxisNormalizedSignalWindowSynthesisLp t T -
        suzukiRealAxisNormalizedSignalWindowSynthesisLp t U‖ ^ 2 := by
  unfold suzukiXiCoefficientTailGramQuadratic
  rw [suzukiXiZeroFunctionFinsuppGramQuadratic_re,
    suzukiXiZeroFunctionFiniteSynthesis_coefficientTail]

/-- Every coefficient-tail Gram quadratic has nonnegative real part. -/
theorem suzukiXiCoefficientTailGramQuadratic_re_nonneg
    (t T U : ℝ) :
    0 ≤ (suzukiXiCoefficientTailGramQuadratic t T U).re := by
  rw [suzukiXiCoefficientTailGramQuadratic_re]
  positivity

/-- The squared distance of the literal published signals is `pi` times the
normalized coefficient-tail Gram quadratic. -/
theorem norm_sq_sub_suzukiRealAxisSignalWindowLp_eq_pi_mul_tailGram_re
    (t T U : ℝ) :
    ‖suzukiRealAxisSignalWindowLp t T -
        suzukiRealAxisSignalWindowLp t U‖ ^ 2 =
      Real.pi * (suzukiXiCoefficientTailGramQuadratic t T U).re := by
  rw [suzukiRealAxisSignalWindowLp_eq_sqrtPi_smul_normalized,
    suzukiRealAxisSignalWindowLp_eq_sqrtPi_smul_normalized,
    ← smul_sub, norm_smul, suzukiXiCoefficientTailGramQuadratic_re]
  have hsqrtNorm : ‖(Real.sqrt Real.pi : ℂ)‖ = Real.sqrt Real.pi := by
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [hsqrtNorm]
  nlinarith [Real.sq_sqrt Real.pi_nonneg]

/-- Eventual Gram control only along Suzuki's coefficient-window differences.
This is strictly weaker than a Bessel bound on all finitely supported
coefficient families.  The declaration defines the proposition but does not
assert it. -/
def SuzukiXiCoefficientTailGramBound (t C : ℝ) : Prop :=
  0 < C ∧ ∃ R : ℝ, ∀ T ≥ R, ∀ U ≥ R,
    (suzukiXiCoefficientTailGramQuadratic t T U).re ≤
      C ^ 2 *
        ‖riemannXiSuzukiSpectralCoefficientWindowVector t T -
          riemannXiSuzukiSpectralCoefficientWindowVector t U‖ ^ 2

/-- The exact cancellation-sensitive frontier: the real tail Gram quadratic
vanishes uniformly over sufficiently late pairs of spectral windows. -/
def SuzukiXiCoefficientTailGramVanishing (t : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R,
      (suzukiXiCoefficientTailGramQuadratic t T U).re < epsilon

/-- Tail-Gram vanishing is exactly the Cauchy criterion for the normalized
boundary spectral signals. -/
theorem coefficientTailGramVanishing_iff_cauchySeq_normalizedSignal
    (t : ℝ) :
    SuzukiXiCoefficientTailGramVanishing t ↔
      CauchySeq (fun T : ℝ ↦
        suzukiRealAxisNormalizedSignalWindowSynthesisLp t T) := by
  constructor
  · intro hvanish
    rw [Metric.cauchySeq_iff]
    intro epsilon hepsilon
    obtain ⟨R, hR⟩ := hvanish (epsilon ^ 2) (sq_pos_of_pos hepsilon)
    refine ⟨R, ?_⟩
    intro T hT U hU
    rw [dist_eq_norm]
    apply (sq_lt_sq₀ (norm_nonneg _) hepsilon.le).1
    rw [← suzukiXiCoefficientTailGramQuadratic_re]
    exact hR T hT U hU
  · intro hcauchy
    rw [Metric.cauchySeq_iff] at hcauchy
    intro epsilon hepsilon
    obtain ⟨R, hR⟩ := hcauchy (Real.sqrt epsilon)
      (Real.sqrt_pos.2 hepsilon)
    refine ⟨R, ?_⟩
    intro T hT U hU
    rw [suzukiXiCoefficientTailGramQuadratic_re]
    have hdist := hR T hT U hU
    rw [dist_eq_norm] at hdist
    calc
      ‖suzukiRealAxisNormalizedSignalWindowSynthesisLp t T -
          suzukiRealAxisNormalizedSignalWindowSynthesisLp t U‖ ^ 2 <
          (Real.sqrt epsilon) ^ 2 :=
        (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hdist
      _ = epsilon := Real.sq_sqrt hepsilon.le

/-- A global Bessel witness supplies the weaker tail-Gram bound at every
Suzuki time. -/
theorem coefficientTailGramBound_of_besselBound
    {C : ℝ} (hC : SuzukiXiZeroFunctionBesselBound C)
    (t : ℝ) :
    SuzukiXiCoefficientTailGramBound t C := by
  have hgram := (suzukiXiZeroFunctionBesselBound_iff_gram C).1 hC
  refine ⟨hC.1, 0, ?_⟩
  intro T _hT U _hU
  have h := hgram.2
    (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U)
  rw [← norm_sq_suzukiXiFiniteCoefficientEmbedding,
    suzukiXiFiniteCoefficientEmbedding_coefficientTail] at h
  exact h

/-- The tailored tail-Gram bound gives an eventual Lipschitz estimate between
boundary signal distances and coefficient-window distances. -/
theorem eventually_norm_sub_normalizedSignal_le_of_coefficientTailGramBound
    {t C : ℝ} (hC : SuzukiXiCoefficientTailGramBound t C) :
    ∃ R : ℝ, ∀ T ≥ R, ∀ U ≥ R,
      ‖suzukiRealAxisNormalizedSignalWindowSynthesisLp t T -
          suzukiRealAxisNormalizedSignalWindowSynthesisLp t U‖ ≤
        C * ‖riemannXiSuzukiSpectralCoefficientWindowVector t T -
          riemannXiSuzukiSpectralCoefficientWindowVector t U‖ := by
  obtain ⟨hCpos, R, htail⟩ := hC
  refine ⟨R, ?_⟩
  intro T hT U hU
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hCpos.le (norm_nonneg _))).1
  rw [← suzukiXiCoefficientTailGramQuadratic_re]
  calc
    (suzukiXiCoefficientTailGramQuadratic t T U).re ≤
        C ^ 2 *
          ‖riemannXiSuzukiSpectralCoefficientWindowVector t T -
            riemannXiSuzukiSpectralCoefficientWindowVector t U‖ ^ 2 :=
      htail T hT U hU
    _ = (C *
        ‖riemannXiSuzukiSpectralCoefficientWindowVector t T -
          riemannXiSuzukiSpectralCoefficientWindowVector t U‖) ^ 2 := by
      ring

/-- The tailored coefficient-tail Gram estimate is sufficient to make the
normalized genuine Suzuki windows Cauchy in boundary `L²`. -/
theorem cauchySeq_normalizedSignal_of_coefficientTailGramBound
    {t C : ℝ} (hC : SuzukiXiCoefficientTailGramBound t C) :
    CauchySeq (fun T : ℝ ↦
      suzukiRealAxisNormalizedSignalWindowSynthesisLp t T) := by
  obtain ⟨R, htail⟩ :=
    eventually_norm_sub_normalizedSignal_le_of_coefficientTailGramBound hC
  have hcoeff : CauchySeq (fun T : ℝ ↦
      riemannXiSuzukiSpectralCoefficientWindowVector t T) :=
    (tendsto_riemannXiSuzukiSpectralCoefficientWindowVector t).cauchySeq
  rw [Metric.cauchySeq_iff] at hcoeff ⊢
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hcoeff (epsilon / C) (div_pos hepsilon hC.1)
  refine ⟨max R N, ?_⟩
  intro T hT U hU
  have hTR : R ≤ T := (le_max_left R N).trans hT
  have hTN : N ≤ T := (le_max_right R N).trans hT
  have hUR : R ≤ U := (le_max_left R N).trans hU
  have hUN : N ≤ U := (le_max_right R N).trans hU
  rw [dist_eq_norm]
  have hdist := hN T hTN U hUN
  rw [dist_eq_norm] at hdist
  calc
    ‖suzukiRealAxisNormalizedSignalWindowSynthesisLp t T -
        suzukiRealAxisNormalizedSignalWindowSynthesisLp t U‖ ≤
        C * ‖riemannXiSuzukiSpectralCoefficientWindowVector t T -
          riemannXiSuzukiSpectralCoefficientWindowVector t U‖ :=
      htail T hTR U hUR
    _ < C * (epsilon / C) := mul_lt_mul_of_pos_left hdist hC.1
    _ = epsilon := by field_simp [ne_of_gt hC.1]

/-- An eventual comparison with the convergent coefficient tails forces the
exact tail-Gram vanishing property. -/
theorem coefficientTailGramVanishing_of_bound
    {t C : ℝ} (hC : SuzukiXiCoefficientTailGramBound t C) :
    SuzukiXiCoefficientTailGramVanishing t :=
  (coefficientTailGramVanishing_iff_cauchySeq_normalizedSignal t).2
    (cauchySeq_normalizedSignal_of_coefficientTailGramBound hC)

/-- Exact tail-Gram vanishing, without a global Bessel hypothesis, is enough
for a boundary `L²` limit of the literal published signals. -/
theorem exists_tendsto_suzukiRealAxisSignalWindowLp_of_tailGramVanishing
    {t : ℝ} (hvanish : SuzukiXiCoefficientTailGramVanishing t) :
    ∃ signal : Lp ℂ 2 (volume : Measure ℝ),
      Tendsto (fun T : ℝ ↦ suzukiRealAxisSignalWindowLp t T) atTop
        (nhds signal) := by
  have hcauchy :=
    (coefficientTailGramVanishing_iff_cauchySeq_normalizedSignal t).1 hvanish
  obtain ⟨normalized, hnormalized⟩ :=
    cauchySeq_tendsto_of_complete hcauchy
  refine ⟨(Real.sqrt Real.pi : ℂ) • normalized, ?_⟩
  have hscaled :
      Tendsto (fun T : ℝ ↦
        (Real.sqrt Real.pi : ℂ) •
          suzukiRealAxisNormalizedSignalWindowSynthesisLp t T) atTop
        (nhds ((Real.sqrt Real.pi : ℂ) • normalized)) :=
    tendsto_const_nhds.smul hnormalized
  simpa only [← suzukiRealAxisSignalWindowLp_eq_sqrtPi_smul_normalized]
    using hscaled

/-- Hence a cancellation-sensitive coefficient-tail Gram bound gives a
boundary `L²` limit for the literal published Suzuki spectral signals. -/
theorem exists_tendsto_suzukiRealAxisSignalWindowLp_of_coefficientTailGramBound
    {t C : ℝ} (hC : SuzukiXiCoefficientTailGramBound t C) :
    ∃ signal : Lp ℂ 2 (volume : Measure ℝ),
      Tendsto (fun T : ℝ ↦ suzukiRealAxisSignalWindowLp t T) atTop
        (nhds signal) :=
  exists_tendsto_suzukiRealAxisSignalWindowLp_of_tailGramVanishing
    (coefficientTailGramVanishing_of_bound hC)

end

end RiemannGaussian

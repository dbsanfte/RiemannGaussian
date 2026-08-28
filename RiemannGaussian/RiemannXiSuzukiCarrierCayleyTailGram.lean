import RiemannGaussian.RiemannXiSuzukiCarrierCayleyCoefficientGram

/-!
# The explicit Cayley Gram frontier on genuine xi coefficient tails

The generic off-axis coefficient kernel is specialized here to the actual
Suzuki coefficient-window difference indexed by `(t, T, U)`. Every weighted
tail is split exactly into its off-axis synthesis and its real-node remainder.
The off-axis norm is controlled by one explicit cancellation-preserving Gram
quadratic.

Two named vanishing conditions isolate the remaining work: decay of that
off-axis quadratic and decay of the real-node remainder. Lean proves that
together they imply the established Cayley-weighted tail frontier and hence
the original coefficient-tail Gram frontier.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- The genuinely off-axis restriction of one Suzuki coefficient-window
difference. -/
def suzukiXiCoefficientTailCayleyOffAxisFinsupp
    (t T U : ℝ) : NontrivialZetaZero →₀ ℂ :=
  suzukiXiCarrierCayleyOffAxisPart
    (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U)

/-- The real-spectral restriction of one Suzuki coefficient-window
difference. -/
def suzukiXiCoefficientTailCayleyRealAxisFinsupp
    (t T U : ℝ) : NontrivialZetaZero →₀ ℂ :=
  suzukiXiCarrierCayleyRealAxisPart
    (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U)

/-- The explicit off-axis coefficient Gram quadratic of one genuine Suzuki
coefficient-window difference. -/
def suzukiXiCoefficientTailCayleyOffAxisGramQuadratic
    (t T U : ℝ) : ℂ :=
  suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic
    (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U)

/-- The off-axis component of the Cayley-weighted synthesis of one genuine
coefficient tail. -/
def suzukiXiCoefficientTailNevanlinnaCayleyOffAxisSynthesis
    (t T U : ℝ) : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis
    (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U)

/-- The literal real-node remainder in the Cayley-weighted synthesis of one
genuine coefficient tail. -/
def suzukiXiCoefficientTailNevanlinnaCayleyRealAxisRemainder
    (t T U : ℝ) : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis
    (suzukiXiCoefficientTailCayleyRealAxisFinsupp t T U)

/-- Every node in the off-axis tail restriction is genuinely nonreal in the
spectral coordinate. -/
theorem suzukiXiCoefficientTailCayleyOffAxisFinsupp_support
    (t T U : ℝ) (rho : NontrivialZetaZero)
    (hrho : rho ∈
      (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U).support) :
    (zetaSpectralCoordinate rho.1).im ≠ 0 := by
  exact suzukiXiCarrierCayleyOffAxisPart_support
    (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U) rho hrho

/-- Every genuine Cayley-weighted coefficient tail splits exactly into its
off-axis synthesis plus its real-node remainder. -/
theorem suzukiXiCoefficientTailNevanlinnaCayleyWeightedSynthesis_boundarySplit
    (t T U : ℝ) :
    suzukiXiCoefficientTailNevanlinnaCayleyWeightedSynthesis t T U =
      suzukiXiCoefficientTailNevanlinnaCayleyOffAxisSynthesis t T U +
        suzukiXiCoefficientTailNevanlinnaCayleyRealAxisRemainder t T U := by
  exact
    suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis_boundarySplit
      (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U)

/-- The off-axis tail synthesis is exactly the bounded bilateral synthesis of
its combined geometric coefficient vector. -/
theorem suzukiXiCoefficientTailNevanlinnaCayleyOffAxisSynthesis_eq_operator
    (t T U : ℝ) :
    suzukiXiCoefficientTailNevanlinnaCayleyOffAxisSynthesis t T U =
      suzukiXiCarrierCayleyBilateralSynthesisOperator
        (suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector
          (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U)) := by
  symm
  exact
    suzukiXiCarrierCayleyBilateralSynthesisOperator_weightedOffAxis
      (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U)
      (fun rho hrho ↦
        suzukiXiCoefficientTailCayleyOffAxisFinsupp_support
          t T U rho hrho)

/-- The real part of the genuine off-axis tail Gram quadratic is exactly the
squared coefficient-space norm of the combined geometric vector. -/
theorem re_suzukiXiCoefficientTailCayleyOffAxisGramQuadratic_eq_norm_sq
    (t T U : ℝ) :
    (suzukiXiCoefficientTailCayleyOffAxisGramQuadratic t T U).re =
      ‖suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector
        (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U)‖ ^ 2 := by
  exact
    re_suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic_eq_norm_sq
      (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U)
      (fun rho hrho ↦
        suzukiXiCoefficientTailCayleyOffAxisFinsupp_support
          t T U rho hrho)

/-- Every genuine off-axis tail Gram quadratic has nonnegative real part. -/
theorem re_suzukiXiCoefficientTailCayleyOffAxisGramQuadratic_nonneg
    (t T U : ℝ) :
    0 ≤ (suzukiXiCoefficientTailCayleyOffAxisGramQuadratic t T U).re := by
  exact
    re_suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic_nonneg
      (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U)
      (fun rho hrho ↦
        suzukiXiCoefficientTailCayleyOffAxisFinsupp_support
          t T U rho hrho)

/-- The off-axis part of every genuine Cayley-weighted tail is bounded by its
explicit cancellation-preserving coefficient Gram quadratic. -/
theorem norm_sq_suzukiXiCoefficientTailNevanlinnaCayleyOffAxisSynthesis_le_gram
    (t T U : ℝ) :
    ‖suzukiXiCoefficientTailNevanlinnaCayleyOffAxisSynthesis t T U‖ ^ 2 ≤
      Real.pi *
        (suzukiXiCoefficientTailCayleyOffAxisGramQuadratic t T U).re := by
  exact
    norm_sq_suzukiXiCarrierNevanlinnaCayleyWeightedFiniteSynthesis_le_coefficientGram
      (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U)
      (fun rho hrho ↦
        suzukiXiCoefficientTailCayleyOffAxisFinsupp_support
          t T U rho hrho)

/-- Vanishing of the explicit off-axis Hardy Gram quadratic along sufficiently
late pairs of genuine Suzuki coefficient windows. -/
def SuzukiXiCoefficientTailCayleyOffAxisGramVanishing (t : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R,
      (suzukiXiCoefficientTailCayleyOffAxisGramQuadratic t T U).re < epsilon

/-- Vanishing of the isolated real-node remainder along sufficiently late
pairs of genuine Suzuki coefficient windows. -/
def SuzukiXiCoefficientTailCayleyRealAxisRemainderNormVanishing
    (t : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R,
      ‖suzukiXiCoefficientTailNevanlinnaCayleyRealAxisRemainder t T U‖ ^ 2 <
        epsilon

private theorem norm_add_sq_lt_of_norm_sq_lt_quarter
    {E : Type*} [SeminormedAddCommGroup E]
    {x y : E} {epsilon : ℝ} (_hepsilon : 0 < epsilon)
    (hx : ‖x‖ ^ 2 < epsilon / 4) (hy : ‖y‖ ^ 2 < epsilon / 4) :
    ‖x + y‖ ^ 2 < epsilon := by
  calc
    ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
        (norm_add_le x y)
    _ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
    _ < epsilon := by nlinarith

/-- Decay of the explicit off-axis Gram quadratic together with decay of the
real-node remainder proves the established Cayley-weighted tail frontier. -/
theorem coefficientTailCayleyWeightedNormVanishing_of_offAxisGram_realAxisRemainder
    {t : ℝ} (hoffAxis : SuzukiXiCoefficientTailCayleyOffAxisGramVanishing t)
    (hreal : SuzukiXiCoefficientTailCayleyRealAxisRemainderNormVanishing t) :
    SuzukiXiCoefficientTailCayleyWeightedNormVanishing t := by
  intro epsilon hepsilon
  have hgramEpsilon : 0 < epsilon / (4 * Real.pi) := by positivity
  obtain ⟨Roff, hRoff⟩ := hoffAxis _ hgramEpsilon
  obtain ⟨Rreal, hRreal⟩ := hreal (epsilon / 4) (by positivity)
  refine ⟨max Roff Rreal, ?_⟩
  intro T hT U hU
  have hToff : Roff ≤ T := (le_max_left Roff Rreal).trans hT
  have hUoff : Roff ≤ U := (le_max_left Roff Rreal).trans hU
  have hTreal : Rreal ≤ T := (le_max_right Roff Rreal).trans hT
  have hUreal : Rreal ≤ U := (le_max_right Roff Rreal).trans hU
  have hoffNorm :
      ‖suzukiXiCoefficientTailNevanlinnaCayleyOffAxisSynthesis t T U‖ ^ 2 <
        epsilon / 4 := by
    calc
      ‖suzukiXiCoefficientTailNevanlinnaCayleyOffAxisSynthesis t T U‖ ^ 2 ≤
          Real.pi *
            (suzukiXiCoefficientTailCayleyOffAxisGramQuadratic t T U).re :=
        norm_sq_suzukiXiCoefficientTailNevanlinnaCayleyOffAxisSynthesis_le_gram
          t T U
      _ < Real.pi * (epsilon / (4 * Real.pi)) :=
        mul_lt_mul_of_pos_left (hRoff T hToff U hUoff) Real.pi_pos
      _ = epsilon / 4 := by field_simp [ne_of_gt Real.pi_pos]
  have hrealNorm := hRreal T hTreal U hUreal
  rw [suzukiXiCoefficientTailNevanlinnaCayleyWeightedSynthesis_boundarySplit]
  exact norm_add_sq_lt_of_norm_sq_lt_quarter hepsilon hoffNorm hrealNorm

/-- The two explicit Cayley subfrontiers are sufficient for the original
coefficient-tail Gram vanishing condition already connected to the global
proof chain. -/
theorem coefficientTailGramVanishing_of_cayleyOffAxisGram_realAxisRemainder
    {t : ℝ} (hoffAxis : SuzukiXiCoefficientTailCayleyOffAxisGramVanishing t)
    (hreal : SuzukiXiCoefficientTailCayleyRealAxisRemainderNormVanishing t) :
    SuzukiXiCoefficientTailGramVanishing t := by
  exact (coefficientTailGramVanishing_iff_cayleyWeighted t).2
    (coefficientTailCayleyWeightedNormVanishing_of_offAxisGram_realAxisRemainder
      hoffAxis hreal)

end

end RiemannGaussian

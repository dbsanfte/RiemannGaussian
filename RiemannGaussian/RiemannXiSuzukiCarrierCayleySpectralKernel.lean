import RiemannGaussian.RiemannXiSuzukiCarrierCayleyTailGram

/-!
# Spectral Cauchy form of the off-axis Cayley-Gram frontier

The Hardy coefficient kernel from the bilateral Cayley synthesis is reduced
here to its original spectral coordinates. For two upper-half-plane nodes it
is `2 * i / (w - conj z)`; for two lower-half-plane nodes it is the negative
of that Cauchy kernel; and opposite half-planes are exactly orthogonal.

The resulting finite spectral quadratic is proved equal to the established
coefficient-space Gram norm. The genuine Suzuki coefficient-tail frontier is
then restated through this explicit Cauchy quadratic, with the separate real-
axis remainder unchanged. No decay assertion is assumed or added here.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- The backward Hardy/Szegő kernel of two upper-half-plane Cayley
parameters is exactly the corresponding spectral Cauchy kernel. -/
theorem suzukiXiCarrierCayleyBackwardKernel_eq_spectral
    {z w : ℂ} (hz : z + Complex.I ≠ 0) (hw : w + Complex.I ≠ 0)
    (hzUpper : 0 < z.im) (hwUpper : 0 < w.im) :
    conj (1 - suzukiXiCarrierCayleyParameter z) *
        (1 - suzukiXiCarrierCayleyParameter w) *
          (1 - conj (suzukiXiCarrierCayleyParameter z) *
            suzukiXiCarrierCayleyParameter w)⁻¹ =
      2 * Complex.I / (w - conj z) := by
  have hzConj : conj z - Complex.I ≠ 0 := by
    intro hzero
    apply hz
    have h := congrArg conj hzero
    simpa using h
  have hcauchy : w - conj z ≠ 0 := by
    intro hzero
    have h := congrArg Complex.im hzero
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at h
    linarith
  have hconjCauchy : conj z - w ≠ 0 := by
    intro hzero
    apply hcauchy
    calc
      w - conj z = -(conj z - w) := by ring
      _ = 0 := by rw [hzero]; simp
  have hconjOne :
      conj (1 - suzukiXiCarrierCayleyParameter z) =
        (-2 * Complex.I) / (conj z - Complex.I) := by
    have halgebra :
        1 - (conj z + Complex.I) / (conj z - Complex.I) =
          (-2 * Complex.I) / (conj z - Complex.I) := by
      calc
        1 - (conj z + Complex.I) / (conj z - Complex.I) =
            (conj z - Complex.I) / (conj z - Complex.I) -
              (conj z + Complex.I) / (conj z - Complex.I) := by
          rw [div_self hzConj]
        _ = ((conj z - Complex.I) - (conj z + Complex.I)) /
            (conj z - Complex.I) :=
          (sub_div _ _ _).symm
        _ = (-2 * Complex.I) / (conj z - Complex.I) := by ring
    unfold suzukiXiCarrierCayleyParameter
    rw [map_sub, map_one, map_div₀, map_sub, map_add, conj_I]
    simpa only [sub_neg_eq_add, sub_eq_add_neg, neg_neg] using halgebra
  have hOne :
      1 - suzukiXiCarrierCayleyParameter w =
        2 * Complex.I / (w + Complex.I) := by
    unfold suzukiXiCarrierCayleyParameter
    field_simp [hw]
    ring
  have hDenom :
      1 - conj (suzukiXiCarrierCayleyParameter z) *
          suzukiXiCarrierCayleyParameter w =
        (2 * Complex.I * (conj z - w)) /
          ((conj z - Complex.I) * (w + Complex.I)) := by
    have hproduct :
        (conj z - Complex.I) * (w + Complex.I) ≠ 0 :=
      mul_ne_zero hzConj hw
    have halgebra :
        1 - ((conj z + Complex.I) / (conj z - Complex.I)) *
            ((w - Complex.I) / (w + Complex.I)) =
          (2 * Complex.I * (conj z - w)) /
            ((conj z - Complex.I) * (w + Complex.I)) := by
      rw [div_mul_div_comm]
      calc
        1 - (conj z + Complex.I) * (w - Complex.I) /
            ((conj z - Complex.I) * (w + Complex.I)) =
            ((conj z - Complex.I) * (w + Complex.I)) /
                ((conj z - Complex.I) * (w + Complex.I)) -
              (conj z + Complex.I) * (w - Complex.I) /
                ((conj z - Complex.I) * (w + Complex.I)) := by
          rw [div_self hproduct]
        _ = (((conj z - Complex.I) * (w + Complex.I)) -
              (conj z + Complex.I) * (w - Complex.I)) /
            ((conj z - Complex.I) * (w + Complex.I)) :=
          (sub_div _ _ _).symm
        _ = (2 * Complex.I * (conj z - w)) /
            ((conj z - Complex.I) * (w + Complex.I)) := by ring
    unfold suzukiXiCarrierCayleyParameter
    rw [map_div₀, map_sub, map_add, conj_I]
    simpa only [sub_neg_eq_add, sub_eq_add_neg, neg_neg] using halgebra
  rw [hconjOne, hOne, hDenom]
  rw [inv_div]
  field_simp [hzConj, hw, hcauchy, hconjCauchy]
  ring

/-- The reciprocal forward Hardy/Szegő kernel of two lower-half-plane Cayley
parameters is exactly the signed spectral Cauchy kernel. -/
theorem suzukiXiCarrierCayleyForwardKernel_eq_spectral
    {z w : ℂ} (hz : z - Complex.I ≠ 0) (hw : w - Complex.I ≠ 0)
    (hzLower : z.im < 0) (hwLower : w.im < 0) :
    conj (1 - (suzukiXiCarrierCayleyParameter z)⁻¹) *
        (1 - (suzukiXiCarrierCayleyParameter w)⁻¹) *
          (1 - conj ((suzukiXiCarrierCayleyParameter z)⁻¹) *
            (suzukiXiCarrierCayleyParameter w)⁻¹)⁻¹ =
      (-2 * Complex.I) / (w - conj z) := by
  have hzNeg : -z + Complex.I ≠ 0 := by
    intro hzero
    apply hz
    calc
      z - Complex.I = -(-z + Complex.I) := by ring
      _ = 0 := by rw [hzero]; simp
  have hwNeg : -w + Complex.I ≠ 0 := by
    intro hzero
    apply hw
    calc
      w - Complex.I = -(-w + Complex.I) := by ring
      _ = 0 := by rw [hzero]; simp
  have hzNegUpper : 0 < (-z).im := by
    simp only [Complex.neg_im, neg_pos]
    exact hzLower
  have hwNegUpper : 0 < (-w).im := by
    simp only [Complex.neg_im, neg_pos]
    exact hwLower
  have h := suzukiXiCarrierCayleyBackwardKernel_eq_spectral
    hzNeg hwNeg hzNegUpper hwNegUpper
  rw [suzukiXiCarrierCayleyParameter_neg z hz,
    suzukiXiCarrierCayleyParameter_neg w hw] at h
  calc
    conj (1 - (suzukiXiCarrierCayleyParameter z)⁻¹) *
          (1 - (suzukiXiCarrierCayleyParameter w)⁻¹) *
            (1 - conj ((suzukiXiCarrierCayleyParameter z)⁻¹) *
              (suzukiXiCarrierCayleyParameter w)⁻¹)⁻¹ =
        2 * Complex.I / (-w - conj (-z)) := h
    _ = (-2 * Complex.I) / (w - conj z) := by
      have hden : -w - conj (-z) = -(w - conj z) := by
        simp only [map_neg]
        ring
      rw [hden, div_neg]
      ring

/-- The off-axis Hardy coefficient kernel written directly in the original
spectral coordinates. Same-half-plane pairs give half-plane Cauchy kernels;
opposite-half-plane pairs are orthogonal. -/
def suzukiXiCarrierCayleyOffAxisSpectralKernel
    (rho sigma : NontrivialZetaZero) : ℂ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    if 0 < (zetaSpectralCoordinate sigma.1).im then
      2 * Complex.I /
        (zetaSpectralCoordinate sigma.1 -
          conj (zetaSpectralCoordinate rho.1))
    else 0
  else if 0 < (zetaSpectralCoordinate sigma.1).im then 0
  else
    (-2 * Complex.I) /
      (zetaSpectralCoordinate sigma.1 -
        conj (zetaSpectralCoordinate rho.1))

/-- On genuine off-axis xi nodes, the coefficient-space Hardy kernel equals
the explicit same-half-plane spectral Cauchy kernel. -/
theorem suzukiXiCarrierCayleyOffAxisCoefficientKernel_eq_spectralKernel
    (rho sigma : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0)
    (hsigma : (zetaSpectralCoordinate sigma.1).im ≠ 0) :
    suzukiXiCarrierCayleyOffAxisCoefficientKernel rho sigma =
      suzukiXiCarrierCayleyOffAxisSpectralKernel rho sigma := by
  by_cases hrhoUpper : 0 < (zetaSpectralCoordinate rho.1).im
  · by_cases hsigmaUpper : 0 < (zetaSpectralCoordinate sigma.1).im
    · simp only [suzukiXiCarrierCayleyOffAxisCoefficientKernel,
        suzukiXiCarrierCayleyOffAxisSpectralKernel, if_pos hrhoUpper,
        if_pos hsigmaUpper]
      unfold suzukiXiCarrierCayleyNodeParameter
      exact suzukiXiCarrierCayleyBackwardKernel_eq_spectral
        (zetaSpectralCoordinate_add_I_ne_zero rho)
        (zetaSpectralCoordinate_add_I_ne_zero sigma)
        hrhoUpper hsigmaUpper
    · simp only [suzukiXiCarrierCayleyOffAxisCoefficientKernel,
        suzukiXiCarrierCayleyOffAxisSpectralKernel, if_pos hrhoUpper,
        if_neg hsigmaUpper]
  · have hrhoLower : (zetaSpectralCoordinate rho.1).im < 0 :=
      lt_of_le_of_ne (not_lt.mp hrhoUpper) hrho
    by_cases hsigmaUpper : 0 < (zetaSpectralCoordinate sigma.1).im
    · simp only [suzukiXiCarrierCayleyOffAxisCoefficientKernel,
        suzukiXiCarrierCayleyOffAxisSpectralKernel, if_neg hrhoUpper,
        if_pos hsigmaUpper]
    · have hsigmaLower : (zetaSpectralCoordinate sigma.1).im < 0 :=
        lt_of_le_of_ne (not_lt.mp hsigmaUpper) hsigma
      simp only [suzukiXiCarrierCayleyOffAxisCoefficientKernel,
        suzukiXiCarrierCayleyOffAxisSpectralKernel, if_neg hrhoUpper,
        if_neg hsigmaUpper]
      unfold suzukiXiCarrierCayleyNodeParameter
      exact suzukiXiCarrierCayleyForwardKernel_eq_spectral
        (zetaSpectralCoordinate_sub_I_ne_zero rho)
        (zetaSpectralCoordinate_sub_I_ne_zero sigma)
        hrhoLower hsigmaLower

/-- The finite weighted Gram quadratic expressed solely through spectral
Cauchy kernels. -/
def suzukiXiCarrierCayleyOffAxisSpectralGramQuadratic
    (c : NontrivialZetaZero →₀ ℂ) : ℂ :=
  ∑ rho ∈ c.support, ∑ sigma ∈ c.support,
    conj (suzukiXiCarrierCayleyOffAxisWeightedCoefficient c rho) *
      suzukiXiCarrierCayleyOffAxisWeightedCoefficient c sigma *
        suzukiXiCarrierCayleyOffAxisSpectralKernel rho sigma

/-- For any finitely supported off-axis family, the original Hardy
coefficient quadratic equals the explicit spectral Cauchy quadratic. -/
theorem suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic_eq_spectral
    (c : NontrivialZetaZero →₀ ℂ)
    (hoffAxis : ∀ rho ∈ c.support,
      (zetaSpectralCoordinate rho.1).im ≠ 0) :
    suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic c =
      suzukiXiCarrierCayleyOffAxisSpectralGramQuadratic c := by
  unfold suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic
    suzukiXiCarrierCayleyOffAxisSpectralGramQuadratic
  apply Finset.sum_congr rfl
  intro rho hrho
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [suzukiXiCarrierCayleyOffAxisCoefficientKernel_eq_spectralKernel rho sigma
    (hoffAxis rho hrho) (hoffAxis sigma hsigma)]

/-- The genuine coefficient-window tail Gram quadratic, now exposed as a
finite half-plane Cauchy quadratic in the xi spectral coordinates. -/
def suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic
    (t T U : ℝ) : ℂ :=
  suzukiXiCarrierCayleyOffAxisSpectralGramQuadratic
    (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U)

/-- The off-axis Gram quadratic of every genuine Suzuki coefficient tail is
exactly its spectral Cauchy quadratic. -/
theorem suzukiXiCoefficientTailCayleyOffAxisGramQuadratic_eq_spectral
    (t T U : ℝ) :
    suzukiXiCoefficientTailCayleyOffAxisGramQuadratic t T U =
      suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic t T U := by
  exact suzukiXiCarrierCayleyOffAxisCoefficientGramQuadratic_eq_spectral
    (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U)
    (fun rho hrho ↦
      suzukiXiCoefficientTailCayleyOffAxisFinsupp_support
        t T U rho hrho)

/-- The real part of the genuine spectral Cauchy quadratic is exactly the
squared norm of the combined bilateral Hardy coefficient vector. -/
theorem re_suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic_eq_norm_sq
    (t T U : ℝ) :
    (suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic t T U).re =
      ‖suzukiXiCarrierCayleyWeightedOffAxisCoefficientVector
        (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U)‖ ^ 2 := by
  rw [← suzukiXiCoefficientTailCayleyOffAxisGramQuadratic_eq_spectral]
  exact re_suzukiXiCoefficientTailCayleyOffAxisGramQuadratic_eq_norm_sq
    t T U

/-- The genuine off-axis carrier synthesis is bounded by `pi` times the real
part of its explicit spectral Cauchy quadratic. -/
theorem norm_sq_suzukiXiCoefficientTailNevanlinnaCayleyOffAxisSynthesis_le_spectralGram
    (t T U : ℝ) :
    ‖suzukiXiCoefficientTailNevanlinnaCayleyOffAxisSynthesis t T U‖ ^ 2 ≤
      Real.pi *
        (suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic
          t T U).re := by
  rw [← suzukiXiCoefficientTailCayleyOffAxisGramQuadratic_eq_spectral]
  exact
    norm_sq_suzukiXiCoefficientTailNevanlinnaCayleyOffAxisSynthesis_le_gram
      t T U

/-- Vanishing of the explicit spectral Cauchy quadratic along late pairs of
genuine Suzuki coefficient windows. -/
def SuzukiXiCoefficientTailCayleyOffAxisSpectralGramVanishing
    (t : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R,
      (suzukiXiCoefficientTailCayleyOffAxisSpectralGramQuadratic
        t T U).re < epsilon

/-- Vanishing of the spectral Cauchy quadratic is exactly the earlier
coefficient-space Gram-vanishing condition. -/
theorem suzukiXiCoefficientTailCayleyOffAxisSpectralGramVanishing_iff
    (t : ℝ) :
    SuzukiXiCoefficientTailCayleyOffAxisSpectralGramVanishing t ↔
      SuzukiXiCoefficientTailCayleyOffAxisGramVanishing t := by
  unfold SuzukiXiCoefficientTailCayleyOffAxisSpectralGramVanishing
    SuzukiXiCoefficientTailCayleyOffAxisGramVanishing
  simp only [suzukiXiCoefficientTailCayleyOffAxisGramQuadratic_eq_spectral]

/-- Spectral Cauchy-quadratic decay together with decay of the isolated real-
axis remainder proves the original coefficient-tail Gram frontier. -/
theorem coefficientTailGramVanishing_of_cayleySpectralGram_realAxisRemainder
    {t : ℝ}
    (hoffAxis :
      SuzukiXiCoefficientTailCayleyOffAxisSpectralGramVanishing t)
    (hreal : SuzukiXiCoefficientTailCayleyRealAxisRemainderNormVanishing t) :
    SuzukiXiCoefficientTailGramVanishing t := by
  exact coefficientTailGramVanishing_of_cayleyOffAxisGram_realAxisRemainder
    ((suzukiXiCoefficientTailCayleyOffAxisSpectralGramVanishing_iff t).1
      hoffAxis)
    hreal

end

end RiemannGaussian

import RiemannGaussian.RiemannXiSuzukiCoefficientTailGram
import RiemannGaussian.RiemannXiSuzukiRealAxisSignalL2

/-!
# Identifying the Suzuki boundary limit with the arithmetic signal

The coefficient-tail Gram criterion gives convergence of the genuine finite
spectral signals to an unspecified boundary `L²` vector.  Independently, the
positive-time arithmetic formula has already been packaged as an actual
element of the same Hilbert space.  This file isolates, without asserting,
the exact remaining identification problem between those two objects.

There are two equivalent routes.  First, tail-Gram vanishing together with
weak convergence on any dense family of `L²` test vectors forces the unnamed
spectral limit to equal the arithmetic vector.  Second, the same strong
identification is equivalent to two scalar limits: convergence of the finite
spectral Gram norm and convergence of the mixed arithmetic--spectral inner
product.  An exact squared-discrepancy identity connects these formulations.

No real-boundary identity is inferred from the already proved pointwise
safe-half-plane equality.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The squared `L²` discrepancy between a genuine finite spectral window and
the complete positive-time arithmetic signal. -/
def suzukiXiArithmeticBoundaryDiscrepancy
    (t : ℝ) (ht : 0 < t) (T : ℝ) : ℝ :=
  ‖suzukiRealAxisSignalWindowLp t T -
      suzukiRealAxisArithmeticSignalPositiveLp t ht‖ ^ 2

/-- Every finite arithmetic--spectral boundary discrepancy is nonnegative. -/
theorem suzukiXiArithmeticBoundaryDiscrepancy_nonneg
    (t : ℝ) (ht : 0 < t) (T : ℝ) :
    0 ≤ suzukiXiArithmeticBoundaryDiscrepancy t ht T := by
  unfold suzukiXiArithmeticBoundaryDiscrepancy
  positivity

/-- Exact polarization of the arithmetic--spectral discrepancy.  The pure
spectral term is the genuine finite zero-function Gram quadratic, while the
only new term is an honest mixed inner product in boundary `L²`. -/
theorem suzukiXiArithmeticBoundaryDiscrepancy_eq
    (t : ℝ) (ht : 0 < t) (T : ℝ) :
    suzukiXiArithmeticBoundaryDiscrepancy t ht T =
      (suzukiXiFiniteZeroFunctionGramQuadratic t T).re -
        2 * (inner ℂ (suzukiRealAxisArithmeticSignalPositiveLp t ht)
          (suzukiRealAxisSignalWindowLp t T)).re +
        ‖suzukiRealAxisArithmeticSignalPositiveLp t ht‖ ^ 2 := by
  unfold suzukiXiArithmeticBoundaryDiscrepancy
  rw [norm_sub_sq (𝕜 := ℂ),
    ← suzukiXiFiniteZeroFunctionGramQuadratic_re,
    inner_re_symm]
  rfl

/-- The desired strong boundary identification.  This declaration names the
proposition but does not assert it. -/
def SuzukiXiArithmeticBoundaryIdentification
    (t : ℝ) (ht : 0 < t) : Prop :=
  Tendsto (fun T : ℝ ↦ suzukiRealAxisSignalWindowLp t T) atTop
    (nhds (suzukiRealAxisArithmeticSignalPositiveLp t ht))

/-- Strong arithmetic boundary identification is exactly vanishing of the
squared `L²` discrepancy. -/
theorem arithmeticBoundaryIdentification_iff_discrepancy_tendsto_zero
    (t : ℝ) (ht : 0 < t) :
    SuzukiXiArithmeticBoundaryIdentification t ht ↔
      Tendsto (fun T : ℝ ↦
        suzukiXiArithmeticBoundaryDiscrepancy t ht T) atTop (nhds 0) := by
  unfold SuzukiXiArithmeticBoundaryIdentification
  constructor
  · intro h
    simpa only [suzukiXiArithmeticBoundaryDiscrepancy, pow_two, zero_mul] using
        (tendsto_iff_norm_sub_tendsto_zero.mp h).pow 2
  · intro h
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsqrt := h.sqrt
    simpa only [suzukiXiArithmeticBoundaryDiscrepancy,
      Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

/-- Tail-Gram vanishing is equivalently the Cauchy criterion for the literal
published spectral windows, not only for their normalized versions. -/
theorem coefficientTailGramVanishing_iff_cauchySeq_signalWindowLp
    (t : ℝ) :
    SuzukiXiCoefficientTailGramVanishing t ↔
      CauchySeq (fun T : ℝ ↦ suzukiRealAxisSignalWindowLp t T) := by
  constructor
  · intro hvanish
    obtain ⟨signal, hsignal⟩ :=
      exists_tendsto_suzukiRealAxisSignalWindowLp_of_tailGramVanishing hvanish
    exact hsignal.cauchySeq
  · intro hcauchy
    obtain ⟨signal, hsignal⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hsqrt : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
    have hnormalized :
        Tendsto (fun T : ℝ ↦
          suzukiRealAxisNormalizedSignalWindowSynthesisLp t T) atTop
          (nhds ((Real.sqrt Real.pi : ℂ)⁻¹ • signal)) := by
      have hscaled :=
        tendsto_const_nhds.smul hsignal
          (c := (Real.sqrt Real.pi : ℂ)⁻¹)
      simpa only [suzukiRealAxisSignalWindowLp_eq_sqrtPi_smul_normalized,
        smul_smul, inv_mul_cancel₀ hsqrt, one_smul] using hscaled
    exact (coefficientTailGramVanishing_iff_cauchySeq_normalizedSignal t).2
      hnormalized.cauchySeq

/-- Weak arithmetic boundary identification restricted to a chosen family of
test vectors.  The proposition is deliberately parameterized by the family
that a future contour or Hardy-space argument can prove to be dense. -/
def SuzukiXiArithmeticBoundaryWeakIdentificationOn
    (t : ℝ) (ht : 0 < t)
    (tests : Set (Lp ℂ 2 (volume : Measure ℝ))) : Prop :=
  ∀ g ∈ tests,
    Tendsto (fun T : ℝ ↦
      inner ℂ g (suzukiRealAxisSignalWindowLp t T)) atTop
        (nhds (inner ℂ g
          (suzukiRealAxisArithmeticSignalPositiveLp t ht)))

/-- On any dense test family, strong arithmetic boundary identification is
equivalent to tail-Gram vanishing plus weak identification on that family. -/
theorem arithmeticBoundaryIdentification_iff_tailGramVanishing_and_weakOn
    (t : ℝ) (ht : 0 < t)
    {tests : Set (Lp ℂ 2 (volume : Measure ℝ))}
    (htests : Dense tests) :
    SuzukiXiArithmeticBoundaryIdentification t ht ↔
      SuzukiXiCoefficientTailGramVanishing t ∧
        SuzukiXiArithmeticBoundaryWeakIdentificationOn t ht tests := by
  constructor
  · intro hstrong
    refine ⟨(coefficientTailGramVanishing_iff_cauchySeq_signalWindowLp t).2
      hstrong.cauchySeq, ?_⟩
    intro g _hg
    exact Filter.Tendsto.inner tendsto_const_nhds hstrong
  · rintro ⟨hvanish, hweak⟩
    obtain ⟨signal, hsignal⟩ :=
      exists_tendsto_suzukiRealAxisSignalWindowLp_of_tailGramVanishing hvanish
    have hsignal_eq :
        signal = suzukiRealAxisArithmeticSignalPositiveLp t ht := by
      apply htests.eq_of_inner_right ℂ
      intro g hg
      exact tendsto_nhds_unique
        (Filter.Tendsto.inner tendsto_const_nhds hsignal)
        (hweak g hg)
    unfold SuzukiXiArithmeticBoundaryIdentification
    simpa only [hsignal_eq] using hsignal

/-- The pure finite-Gram norm limit required by the scalar identification
route.  This declaration names the proposition but does not assert it. -/
def SuzukiXiArithmeticBoundaryGramNormIdentification
    (t : ℝ) (ht : 0 < t) : Prop :=
  Tendsto (fun T : ℝ ↦
    (suzukiXiFiniteZeroFunctionGramQuadratic t T).re) atTop
      (nhds (‖suzukiRealAxisArithmeticSignalPositiveLp t ht‖ ^ 2))

/-- The mixed arithmetic--spectral scalar limit required by the second
identification route.  This declaration names the proposition but does not
assert it. -/
def SuzukiXiArithmeticBoundaryCrossIdentification
    (t : ℝ) (ht : 0 < t) : Prop :=
  Tendsto (fun T : ℝ ↦
    (inner ℂ (suzukiRealAxisArithmeticSignalPositiveLp t ht)
      (suzukiRealAxisSignalWindowLp t T)).re) atTop
        (nhds (‖suzukiRealAxisArithmeticSignalPositiveLp t ht‖ ^ 2))

/-- Strong boundary identification supplies the pure finite-Gram norm
limit. -/
theorem arithmeticBoundaryGramNormIdentification_of_identification
    {t : ℝ} {ht : 0 < t}
    (h : SuzukiXiArithmeticBoundaryIdentification t ht) :
    SuzukiXiArithmeticBoundaryGramNormIdentification t ht := by
  unfold SuzukiXiArithmeticBoundaryIdentification at h
  unfold SuzukiXiArithmeticBoundaryGramNormIdentification
  have hnorm := h.norm.pow 2
  simpa only [suzukiXiFiniteZeroFunctionGramQuadratic_re] using hnorm

/-- Strong boundary identification supplies the mixed arithmetic--spectral
inner-product limit. -/
theorem arithmeticBoundaryCrossIdentification_of_identification
    {t : ℝ} {ht : 0 < t}
    (h : SuzukiXiArithmeticBoundaryIdentification t ht) :
    SuzukiXiArithmeticBoundaryCrossIdentification t ht := by
  unfold SuzukiXiArithmeticBoundaryIdentification at h
  unfold SuzukiXiArithmeticBoundaryCrossIdentification
  have hinner :
      Tendsto (fun T : ℝ ↦
        inner ℂ (suzukiRealAxisArithmeticSignalPositiveLp t ht)
          (suzukiRealAxisSignalWindowLp t T)) atTop
        (nhds (inner ℂ (suzukiRealAxisArithmeticSignalPositiveLp t ht)
          (suzukiRealAxisArithmeticSignalPositiveLp t ht))) :=
    Filter.Tendsto.inner tendsto_const_nhds h
  have hre := (Complex.continuous_re.tendsto _).comp hinner
  have hnormRe :
      ((‖suzukiRealAxisArithmeticSignalPositiveLp t ht‖ : ℂ) ^ 2).re =
        ‖suzukiRealAxisArithmeticSignalPositiveLp t ht‖ ^ 2 := by
    change RCLike.re
      ((‖suzukiRealAxisArithmeticSignalPositiveLp t ht‖ : ℂ) ^ 2) = _
    exact RCLike.re_ofReal_pow _ _
  convert hre using 1
  · ext T
    rfl
  · rw [inner_self_eq_norm_sq_to_K]
    exact congrArg nhds hnormRe.symm

/-- The two scalar limits force the exact squared discrepancy to vanish and
hence identify the spectral boundary limit with the arithmetic signal. -/
theorem arithmeticBoundaryIdentification_of_gramNorm_and_cross
    {t : ℝ} {ht : 0 < t}
    (hgram : SuzukiXiArithmeticBoundaryGramNormIdentification t ht)
    (hcross : SuzukiXiArithmeticBoundaryCrossIdentification t ht) :
    SuzukiXiArithmeticBoundaryIdentification t ht := by
  unfold SuzukiXiArithmeticBoundaryGramNormIdentification at hgram
  unfold SuzukiXiArithmeticBoundaryCrossIdentification at hcross
  apply (arithmeticBoundaryIdentification_iff_discrepancy_tendsto_zero
    t ht).2
  have hcombined :=
    (hgram.sub (hcross.const_mul 2)).add_const
      (‖suzukiRealAxisArithmeticSignalPositiveLp t ht‖ ^ 2)
  have hzero :
      ‖suzukiRealAxisArithmeticSignalPositiveLp t ht‖ ^ 2 -
          2 * ‖suzukiRealAxisArithmeticSignalPositiveLp t ht‖ ^ 2 +
        ‖suzukiRealAxisArithmeticSignalPositiveLp t ht‖ ^ 2 = 0 := by
    ring
  rw [hzero] at hcombined
  apply hcombined.congr'
  exact Eventually.of_forall fun T ↦
    (suzukiXiArithmeticBoundaryDiscrepancy_eq t ht T).symm

/-- Equivalently, the complete arithmetic boundary identification problem is
precisely the conjunction of one finite Gram-norm limit and one mixed
arithmetic--spectral inner-product limit. -/
theorem arithmeticBoundaryIdentification_iff_gramNorm_and_cross
    (t : ℝ) (ht : 0 < t) :
    SuzukiXiArithmeticBoundaryIdentification t ht ↔
      SuzukiXiArithmeticBoundaryGramNormIdentification t ht ∧
        SuzukiXiArithmeticBoundaryCrossIdentification t ht := by
  constructor
  · intro h
    exact ⟨arithmeticBoundaryGramNormIdentification_of_identification h,
      arithmeticBoundaryCrossIdentification_of_identification h⟩
  · rintro ⟨hgram, hcross⟩
    exact arithmeticBoundaryIdentification_of_gramNorm_and_cross hgram hcross

end

end RiemannGaussian

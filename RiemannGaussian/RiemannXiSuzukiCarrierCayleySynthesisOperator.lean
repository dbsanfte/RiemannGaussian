import RiemannGaussian.RiemannXiSuzukiCarrierCayleyMomentBound

/-!
# The bounded infinite xi-energy Cayley synthesis operator

The finite Cauchy-reference estimate extends canonically to the full
coefficient Hilbert space `ℓ²(ℤ, ℂ)`.  This file constructs the extension as a
composition of two concrete maps:

1. the isometric synthesis map of the normalized orthonormal Cayley orbit in
   Cauchy-reference `L²`;
2. the norm-nonincreasing inclusion from reference `L²` into the dominated
   xi-energy carrier `L²`.

The resulting operator sums every square-summable bilateral Cayley series,
has norm at most `sqrt(pi)`, and agrees exactly with the previous finite
synthesis on finitely supported coefficient families.

This is a boundedness result.  It does not assert compactness or the vanishing
of the structured Suzuki coefficient tail.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-! ## The dominated-measure inclusion -/

/-- The complex-linear identity-on-representatives map from Cauchy-reference
`L²` into carrier `L²`. -/
def suzukiXiCarrierCayleyReferenceToCarrierLinearMap :
    Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure →ₗ[ℂ]
      Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure where
  toFun f := ((Lp.memLp f).mono_measure
    suzukiXiCarrierNevanlinnaMeasure_le_cayleyReferenceMeasure).toLp f
  map_add' f g := by
    ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp,
      MemLp.coeFn_toLp]
    have hac : suzukiXiCarrierNevanlinnaMeasure ≪
        suzukiXiCarrierCayleyReferenceMeasure :=
      Measure.absolutelyContinuous_of_le
        suzukiXiCarrierNevanlinnaMeasure_le_cayleyReferenceMeasure
    apply hac.ae_eq
    grw [Lp.coeFn_add]
  map_smul' c f := by
    ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
    have hac : suzukiXiCarrierNevanlinnaMeasure ≪
        suzukiXiCarrierCayleyReferenceMeasure :=
      Measure.absolutelyContinuous_of_le
        suzukiXiCarrierNevanlinnaMeasure_le_cayleyReferenceMeasure
    apply hac.ae_eq
    grw [Lp.coeFn_smul]
    rfl

/-- The dominated-measure linear map keeps the same representative almost
everywhere for the carrier measure. -/
theorem suzukiXiCarrierCayleyReferenceToCarrierLinearMap_ae
    (f : Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure) :
    suzukiXiCarrierCayleyReferenceToCarrierLinearMap f =ᵐ[
      suzukiXiCarrierNevanlinnaMeasure] f := by
  unfold suzukiXiCarrierCayleyReferenceToCarrierLinearMap
  exact MemLp.coeFn_toLp
    ((Lp.memLp f).mono_measure
      suzukiXiCarrierNevanlinnaMeasure_le_cayleyReferenceMeasure)

/-- The dominated-measure inclusion does not increase the `L²` norm. -/
theorem norm_suzukiXiCarrierCayleyReferenceToCarrierLinearMap_le
    (f : Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure) :
    ‖suzukiXiCarrierCayleyReferenceToCarrierLinearMap f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono
  · finiteness
  · calc
      eLpNorm
          (suzukiXiCarrierCayleyReferenceToCarrierLinearMap f : ℝ → ℂ)
          2 suzukiXiCarrierNevanlinnaMeasure =
          eLpNorm (f : ℝ → ℂ) 2
            suzukiXiCarrierNevanlinnaMeasure :=
        eLpNorm_congr_ae
          (suzukiXiCarrierCayleyReferenceToCarrierLinearMap_ae f)
      _ ≤ eLpNorm (f : ℝ → ℂ) 2
          suzukiXiCarrierCayleyReferenceMeasure :=
        eLpNorm_mono_measure _
          suzukiXiCarrierNevanlinnaMeasure_le_cayleyReferenceMeasure

/-- The dominated-measure inclusion as a continuous complex-linear map. -/
def suzukiXiCarrierCayleyReferenceToCarrier :
    Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure →L[ℂ]
      Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  LinearMap.mkContinuous
    suzukiXiCarrierCayleyReferenceToCarrierLinearMap 1 fun f ↦ by
      simpa only [one_mul] using
        norm_suzukiXiCarrierCayleyReferenceToCarrierLinearMap_le f

/-- The continuous inclusion has operator norm at most one. -/
theorem norm_suzukiXiCarrierCayleyReferenceToCarrier_le_one :
    ‖suzukiXiCarrierCayleyReferenceToCarrier‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The continuous inclusion keeps the same representative almost
everywhere for the carrier measure. -/
theorem suzukiXiCarrierCayleyReferenceToCarrier_ae
    (f : Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure) :
    suzukiXiCarrierCayleyReferenceToCarrier f =ᵐ[
      suzukiXiCarrierNevanlinnaMeasure] f := by
  change suzukiXiCarrierCayleyReferenceToCarrierLinearMap f =ᵐ[
    suzukiXiCarrierNevanlinnaMeasure] f
  exact suzukiXiCarrierCayleyReferenceToCarrierLinearMap_ae f

/-- The dominated-measure inclusion sends each reference Cayley monomial to
the corresponding carrier Cayley monomial. -/
theorem suzukiXiCarrierCayleyReferenceToCarrier_referenceOrbit
    (k : ℤ) :
    suzukiXiCarrierCayleyReferenceToCarrier
        (suzukiXiCarrierCayleyReferenceOrbit k) =
      suzukiXiCarrierCayleyBilateralOrbit k := by
  apply Lp.ext
  have hac : suzukiXiCarrierNevanlinnaMeasure ≪
      suzukiXiCarrierCayleyReferenceMeasure :=
    Measure.absolutelyContinuous_of_le
      suzukiXiCarrierNevanlinnaMeasure_le_cayleyReferenceMeasure
  filter_upwards [
    suzukiXiCarrierCayleyReferenceToCarrier_ae
      (suzukiXiCarrierCayleyReferenceOrbit k),
    hac.ae_eq (suzukiXiCarrierCayleyReferenceOrbit_ae k),
    suzukiXiCarrierCayleyBilateralOrbit_ae k] with x hmap href hcarrier
  rw [hmap, href, hcarrier]

/-! ## Infinite orthonormal synthesis -/

/-- Isometric synthesis of a bilateral `ℓ²` family into the normalized
reference Cayley orbit. -/
def suzukiXiCarrierCayleyNormalizedReferenceSynthesisIsometry :
    ℓ²(ℤ, ℂ) →ₗᵢ[ℂ]
      Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure :=
  orthonormal_suzukiXiCarrierCayleyNormalizedReferenceOrbit.orthogonalFamily.linearIsometry

/-- A single `ℓ²` coordinate synthesizes to the corresponding normalized
reference Cayley monomial. -/
theorem suzukiXiCarrierCayleyNormalizedReferenceSynthesisIsometry_single
    (k : ℤ) (c : ℂ) :
    suzukiXiCarrierCayleyNormalizedReferenceSynthesisIsometry
        (lp.single 2 k c) =
      c • suzukiXiCarrierCayleyNormalizedReferenceOrbit k := by
  unfold suzukiXiCarrierCayleyNormalizedReferenceSynthesisIsometry
  rw [OrthogonalFamily.linearIsometry_apply_single,
    LinearIsometry.toSpanSingleton_apply]

/-- Unnormalized reference synthesis, obtained by restoring the common
factor `sqrt(pi)` to the normalized orthonormal orbit. -/
def suzukiXiCarrierCayleyReferenceSynthesisOperator :
    ℓ²(ℤ, ℂ) →L[ℂ]
      Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure :=
  (Real.sqrt Real.pi : ℂ) •
    suzukiXiCarrierCayleyNormalizedReferenceSynthesisIsometry.toContinuousLinearMap

/-- A single coefficient is synthesized to its unnormalized reference
Cayley monomial. -/
theorem suzukiXiCarrierCayleyReferenceSynthesisOperator_single
    (k : ℤ) (c : ℂ) :
    suzukiXiCarrierCayleyReferenceSynthesisOperator (lp.single 2 k c) =
      c • suzukiXiCarrierCayleyReferenceOrbit k := by
  rw [suzukiXiCarrierCayleyReferenceSynthesisOperator,
    smul_apply]
  change (Real.sqrt Real.pi : ℂ) •
      suzukiXiCarrierCayleyNormalizedReferenceSynthesisIsometry
        (lp.single 2 k c) = _
  rw [suzukiXiCarrierCayleyNormalizedReferenceSynthesisIsometry_single]
  calc
    (Real.sqrt Real.pi : ℂ) •
        (c • suzukiXiCarrierCayleyNormalizedReferenceOrbit k) =
        c • ((Real.sqrt Real.pi : ℂ) •
          suzukiXiCarrierCayleyNormalizedReferenceOrbit k) := by
      rw [smul_smul, smul_smul, mul_comm]
    _ = c • suzukiXiCarrierCayleyReferenceOrbit k := by
      rw [←
        suzukiXiCarrierCayleyReferenceOrbit_eq_sqrtPi_smul_normalized]

/-- The full bilateral xi-energy Cayley synthesis operator on `ℓ²(ℤ,ℂ)`. -/
def suzukiXiCarrierCayleyBilateralSynthesisOperator :
    ℓ²(ℤ, ℂ) →L[ℂ]
      Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  suzukiXiCarrierCayleyReferenceToCarrier.comp
    suzukiXiCarrierCayleyReferenceSynthesisOperator

/-- A single `ℓ²` coordinate is sent to the corresponding carrier Cayley
monomial with that coefficient. -/
theorem suzukiXiCarrierCayleyBilateralSynthesisOperator_single
    (k : ℤ) (c : ℂ) :
    suzukiXiCarrierCayleyBilateralSynthesisOperator (lp.single 2 k c) =
      c • suzukiXiCarrierCayleyBilateralOrbit k := by
  rw [suzukiXiCarrierCayleyBilateralSynthesisOperator,
    ContinuousLinearMap.comp_apply,
    suzukiXiCarrierCayleyReferenceSynthesisOperator_single, map_smul,
    suzukiXiCarrierCayleyReferenceToCarrier_referenceOrbit]

/-- The continuous dominated-measure inclusion is pointwise
norm-nonincreasing. -/
theorem norm_suzukiXiCarrierCayleyReferenceToCarrier_apply_le
    (f : Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure) :
    ‖suzukiXiCarrierCayleyReferenceToCarrier f‖ ≤ ‖f‖ := by
  change ‖suzukiXiCarrierCayleyReferenceToCarrierLinearMap f‖ ≤ ‖f‖
  exact norm_suzukiXiCarrierCayleyReferenceToCarrierLinearMap_le f

/-- Pointwise operator bound for infinite bilateral Cayley synthesis. -/
theorem norm_suzukiXiCarrierCayleyBilateralSynthesisOperator_apply_le
    (a : ℓ²(ℤ, ℂ)) :
    ‖suzukiXiCarrierCayleyBilateralSynthesisOperator a‖ ≤
      Real.sqrt Real.pi * ‖a‖ := by
  rw [suzukiXiCarrierCayleyBilateralSynthesisOperator,
    ContinuousLinearMap.comp_apply]
  calc
    ‖suzukiXiCarrierCayleyReferenceToCarrier
        (suzukiXiCarrierCayleyReferenceSynthesisOperator a)‖ ≤
        ‖suzukiXiCarrierCayleyReferenceSynthesisOperator a‖ :=
      norm_suzukiXiCarrierCayleyReferenceToCarrier_apply_le _
    _ = Real.sqrt Real.pi * ‖a‖ := by
      rw [suzukiXiCarrierCayleyReferenceSynthesisOperator,
        smul_apply, norm_smul]
      change ‖(Real.sqrt Real.pi : ℂ)‖ *
          ‖suzukiXiCarrierCayleyNormalizedReferenceSynthesisIsometry a‖ =
        Real.sqrt Real.pi * ‖a‖
      rw [LinearIsometry.norm_map, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg Real.pi)]

/-- The infinite bilateral synthesis operator has norm at most `sqrt(pi)`. -/
theorem norm_suzukiXiCarrierCayleyBilateralSynthesisOperator_le_sqrtPi :
    ‖suzukiXiCarrierCayleyBilateralSynthesisOperator‖ ≤
      Real.sqrt Real.pi := by
  exact suzukiXiCarrierCayleyBilateralSynthesisOperator.opNorm_le_bound
    (Real.sqrt_nonneg Real.pi)
    norm_suzukiXiCarrierCayleyBilateralSynthesisOperator_apply_le

/-- Squared norm form of the infinite synthesis estimate. -/
theorem norm_sq_suzukiXiCarrierCayleyBilateralSynthesisOperator_apply_le
    (a : ℓ²(ℤ, ℂ)) :
    ‖suzukiXiCarrierCayleyBilateralSynthesisOperator a‖ ^ 2 ≤
      Real.pi * ‖a‖ ^ 2 := by
  calc
    ‖suzukiXiCarrierCayleyBilateralSynthesisOperator a‖ ^ 2 ≤
        (Real.sqrt Real.pi * ‖a‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_suzukiXiCarrierCayleyBilateralSynthesisOperator_apply_le a) 2
    _ = Real.pi * ‖a‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]

/-- Every square-summable bilateral coefficient sequence is summed by the
carrier synthesis operator. -/
theorem hasSum_suzukiXiCarrierCayleyBilateralSynthesisOperator
    (a : ℓ²(ℤ, ℂ)) :
    HasSum (fun k : ℤ ↦
      a k • suzukiXiCarrierCayleyBilateralOrbit k)
      (suzukiXiCarrierCayleyBilateralSynthesisOperator a) := by
  have hsingle : HasSum (fun k : ℤ ↦ lp.single 2 k (a k)) a :=
    lp.hasSum_single ENNReal.ofNat_ne_top a
  have hmapped :=
    suzukiXiCarrierCayleyBilateralSynthesisOperator.hasSum hsingle
  simpa only [suzukiXiCarrierCayleyBilateralSynthesisOperator_single] using
    hmapped

/-- The canonical embedding of a finitely supported integer coefficient
family into `ℓ²(ℤ,ℂ)`. -/
def suzukiXiCarrierCayleyFinsuppCoefficientVector
    (c : ℤ →₀ ℂ) : ℓ²(ℤ, ℂ) :=
  ∑ k ∈ c.support, lp.single 2 k (c k)

/-- A coordinate of the canonical finitely supported `ℓ²` embedding is
the original coefficient. -/
theorem suzukiXiCarrierCayleyFinsuppCoefficientVector_apply
    (c : ℤ →₀ ℂ) (k : ℤ) :
    suzukiXiCarrierCayleyFinsuppCoefficientVector c k = c k := by
  unfold suzukiXiCarrierCayleyFinsuppCoefficientVector
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply,
    Finset.sum_pi_single]
  by_cases hk : k ∈ c.support
  · rw [if_pos hk]
  · rw [if_neg hk, Finsupp.notMem_support_iff.mp hk]

/-- The finite `ℓ²` embedding preserves squared coefficient energy. -/
theorem norm_sq_suzukiXiCarrierCayleyFinsuppCoefficientVector
    (c : ℤ →₀ ℂ) :
    ‖suzukiXiCarrierCayleyFinsuppCoefficientVector c‖ ^ 2 =
      ∑ k ∈ c.support, ‖c k‖ ^ 2 := by
  have hnorm := lp.norm_sum_single
    (p := (2 : ℝ≥0∞)) (by norm_num)
    (fun k : ℤ ↦ c k) c.support
  simpa only [suzukiXiCarrierCayleyFinsuppCoefficientVector,
    ENNReal.toReal_ofNat, Real.rpow_two] using hnorm

/-- The infinite synthesis operator agrees exactly with the previously
defined finite bilateral synthesis. -/
theorem suzukiXiCarrierCayleyBilateralSynthesisOperator_finsupp
    (c : ℤ →₀ ℂ) :
    suzukiXiCarrierCayleyBilateralSynthesisOperator
        (suzukiXiCarrierCayleyFinsuppCoefficientVector c) =
      suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis c := by
  unfold suzukiXiCarrierCayleyFinsuppCoefficientVector
    suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  exact suzukiXiCarrierCayleyBilateralSynthesisOperator_single k (c k)

/-- Lipschitz squared-norm control for differences of arbitrary infinite
Cayley coefficient sequences. -/
theorem norm_sq_suzukiXiCarrierCayleyBilateralSynthesisOperator_sub_le
    (a b : ℓ²(ℤ, ℂ)) :
    ‖suzukiXiCarrierCayleyBilateralSynthesisOperator a -
        suzukiXiCarrierCayleyBilateralSynthesisOperator b‖ ^ 2 ≤
      Real.pi * ‖a - b‖ ^ 2 := by
  rw [← map_sub]
  exact
    norm_sq_suzukiXiCarrierCayleyBilateralSynthesisOperator_apply_le (a - b)

/-- Coefficient-space convergence transports to carrier `L²` convergence. -/
theorem tendsto_suzukiXiCarrierCayleyBilateralSynthesisOperator
    {A : Type*} {l : Filter A} {a : A → ℓ²(ℤ, ℂ)}
    {b : ℓ²(ℤ, ℂ)} (h : Tendsto a l (nhds b)) :
    Tendsto
      (fun j ↦ suzukiXiCarrierCayleyBilateralSynthesisOperator (a j))
      l
      (nhds (suzukiXiCarrierCayleyBilateralSynthesisOperator b)) := by
  exact suzukiXiCarrierCayleyBilateralSynthesisOperator.continuous.continuousAt.tendsto.comp h

end

end RiemannGaussian

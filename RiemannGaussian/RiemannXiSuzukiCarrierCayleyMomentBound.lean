import RiemannGaussian.RiemannXiSuzukiCarrierCayleyMomentDecay

/-!
# Cauchy-reference bounds for the xi-energy Cayley moments

The finite xi-energy carrier measure is pointwise dominated by the Cauchy
reference measure `dx / (1 + x^2)`.  In the shifted arctangent coordinate,
the bilateral Cayley characters are the ordinary Fourier characters on the
additive circle of length `pi`.  This file packages that reference measure
and proves the resulting exact orthogonality and finite-synthesis bounds.

These estimates construct a bounded Toeplitz/Hankel form.  They do not assert
weighted moment summability, compactness, coefficient-tail vanishing, or RH.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- The unnormalized Cauchy measure `dx / (1 + x^2)` on the real line. -/
def suzukiXiCarrierCayleyReferenceMeasure : Measure ℝ :=
  volume.withDensity fun x : ℝ ↦ ENNReal.ofReal ((1 + x ^ 2)⁻¹)

/-- The Cauchy reference measure is finite. -/
instance isFiniteMeasure_suzukiXiCarrierCayleyReferenceMeasure :
    IsFiniteMeasure suzukiXiCarrierCayleyReferenceMeasure := by
  unfold suzukiXiCarrierCayleyReferenceMeasure
  exact isFiniteMeasure_withDensity_ofReal
    integrable_inv_one_add_sq.hasFiniteIntegral

/-- Integration against the reference measure is ordinary Cauchy-weighted
Lebesgue integration. -/
theorem integral_suzukiXiCarrierCayleyReferenceMeasure_eq_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    ∫ x, g x ∂suzukiXiCarrierCayleyReferenceMeasure =
      ∫ x, (1 + x ^ 2)⁻¹ • g x := by
  unfold suzukiXiCarrierCayleyReferenceMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by
      change (ENNReal.ofReal ((1 + x ^ 2)⁻¹)).toReal • g x =
        (1 + x ^ 2)⁻¹ • g x
      rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 + x ^ 2)⁻¹)]
  · exact
      (measurable_const.add (measurable_id.pow_const 2)).inv.ennreal_ofReal
  · exact Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top

/-- The arithmetic xi-energy carrier measure is dominated, with constant
one, by the Cauchy reference measure. -/
theorem suzukiXiCarrierNevanlinnaMeasure_le_cayleyReferenceMeasure :
    suzukiXiCarrierNevanlinnaMeasure ≤
      suzukiXiCarrierCayleyReferenceMeasure := by
  unfold suzukiXiCarrierNevanlinnaMeasure
    suzukiXiCarrierCayleyReferenceMeasure
  apply MeasureTheory.withDensity_mono
  exact Eventually.of_forall fun x ↦
    ENNReal.ofReal_le_ofReal
      (suzukiXiCarrierNevanlinnaWeight_le_inv_one_add_sq x)

/-- Every bilateral Cayley character belongs to reference `L²`. -/
theorem memLp_two_suzukiXiCarrierCayleyBoundaryZPower_reference
    (k : ℤ) :
    MemLp (suzukiXiCarrierCayleyBoundaryZPower k) 2
      suzukiXiCarrierCayleyReferenceMeasure := by
  apply (memLp_const
    (μ := suzukiXiCarrierCayleyReferenceMeasure) (1 : ℂ)).congr_norm
  · exact
      (measurable_suzukiXiCarrierCayleyBoundaryZPower k).aestronglyMeasurable
  · exact Eventually.of_forall fun x ↦ by simp

/-- The bilateral Cayley orbit in the Cauchy reference Hilbert space. -/
def suzukiXiCarrierCayleyReferenceOrbit (k : ℤ) :
    Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure :=
  (memLp_two_suzukiXiCarrierCayleyBoundaryZPower_reference k).toLp
    (suzukiXiCarrierCayleyBoundaryZPower k)

/-- The reference orbit has its literal Cayley character representative. -/
theorem suzukiXiCarrierCayleyReferenceOrbit_ae (k : ℤ) :
    suzukiXiCarrierCayleyReferenceOrbit k =ᵐ[
      suzukiXiCarrierCayleyReferenceMeasure]
        suzukiXiCarrierCayleyBoundaryZPower k :=
  MemLp.coeFn_toLp
    (memLp_two_suzukiXiCarrierCayleyBoundaryZPower_reference k)

/-- A Fourier character has its expected unnormalized integral over one
period of length `pi`. -/
theorem integral_Ioo_fourier_pi (k : ℤ) :
    (∫ theta in Ioo (0 : ℝ) Real.pi,
      @fourier Real.pi k (theta : AddCircle Real.pi)) =
      if k = 0 then (Real.pi : ℂ) else 0 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le Real.pi_pos.le]
  by_cases hk : k = 0
  · subst k
    simp
  · have hcoeff := congrFun
      (fourierCoeff_fourier (T := Real.pi) k) 0
    rw [fourierCoeff_eq_intervalIntegral _ _ 0] at hcoeff
    simp only [hk, if_false]
    simpa [Pi.single_apply, hk] using hcoeff

/-- The exact reference moment: nonzero Cayley characters integrate to zero,
while the constant character has reference mass `pi`. -/
theorem integral_suzukiXiCarrierCayleyReferenceMeasure_zpower
    (k : ℤ) :
    ∫ x : ℝ, suzukiXiCarrierCayleyBoundaryZPower k x
        ∂suzukiXiCarrierCayleyReferenceMeasure =
      if k = 0 then (Real.pi : ℂ) else 0 := by
  rw [integral_suzukiXiCarrierCayleyReferenceMeasure_eq_smul]
  have hchange := integral_shiftedAngular_eq_arctan_jacobian
    (fun theta : ℝ ↦
      @fourier Real.pi k (theta : AddCircle Real.pi))
  rw [integral_Ioo_fourier_pi k] at hchange
  rw [hchange]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    change (1 + x ^ 2)⁻¹ •
        suzukiXiCarrierCayleyBoundaryZPower k x =
      (1 / (1 + x ^ 2)) •
        @fourier Real.pi k
          ((Real.arctan x + Real.pi / 2 : ℝ) : AddCircle Real.pi)
    rw [suzukiXiCarrierCayleyBoundaryZPower_eq_shifted_fourier]
    rw [one_div]

/-- The unnormalized reference Cayley orbit is orthogonal, with common
squared norm `pi`. -/
theorem inner_suzukiXiCarrierCayleyReferenceOrbit
    (m n : ℤ) :
    inner ℂ (suzukiXiCarrierCayleyReferenceOrbit m)
        (suzukiXiCarrierCayleyReferenceOrbit n) =
      if m = n then (Real.pi : ℂ) else 0 := by
  rw [L2.inner_def]
  calc
    (∫ x : ℝ,
        inner ℂ (suzukiXiCarrierCayleyReferenceOrbit m x)
          (suzukiXiCarrierCayleyReferenceOrbit n x)
        ∂suzukiXiCarrierCayleyReferenceMeasure) =
        ∫ x : ℝ,
          starRingEnd ℂ (suzukiXiCarrierCayleyBoundaryZPower m x) *
            suzukiXiCarrierCayleyBoundaryZPower n x
          ∂suzukiXiCarrierCayleyReferenceMeasure := by
      apply integral_congr_ae
      filter_upwards [suzukiXiCarrierCayleyReferenceOrbit_ae m,
        suzukiXiCarrierCayleyReferenceOrbit_ae n] with x hm hn
      rw [hm, hn, RCLike.inner_apply']
    _ = ∫ x : ℝ,
        suzukiXiCarrierCayleyBoundaryZPower (n - m) x
        ∂suzukiXiCarrierCayleyReferenceMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦
        star_suzukiXiCarrierCayleyBoundaryZPower_mul m n x
    _ = if n - m = 0 then (Real.pi : ℂ) else 0 :=
      integral_suzukiXiCarrierCayleyReferenceMeasure_zpower (n - m)
    _ = if m = n then (Real.pi : ℂ) else 0 := by
      simp only [sub_eq_zero, eq_comm]

/-- The reference Cayley orbit normalized by `sqrt(pi)`. -/
def suzukiXiCarrierCayleyNormalizedReferenceOrbit (k : ℤ) :
    Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure :=
  ((Real.sqrt Real.pi : ℂ)⁻¹) •
    suzukiXiCarrierCayleyReferenceOrbit k

/-- The normalized reference Cayley orbit is an orthonormal family. -/
theorem orthonormal_suzukiXiCarrierCayleyNormalizedReferenceOrbit :
    Orthonormal ℂ suzukiXiCarrierCayleyNormalizedReferenceOrbit := by
  rw [orthonormal_iff_ite]
  intro m n
  unfold suzukiXiCarrierCayleyNormalizedReferenceOrbit
  rw [inner_smul_left, inner_smul_right,
    inner_suzukiXiCarrierCayleyReferenceOrbit]
  by_cases hmn : m = n
  · simp only [hmn, if_true]
    rw [map_inv₀]
    simp only [conj_ofReal]
    have hsqrtComplex : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr Real.pi_pos)
    field_simp [hsqrtComplex]
    exact_mod_cast (Real.sq_sqrt Real.pi_pos.le).symm
  · simp only [hmn, if_false, mul_zero]

/-- Finite synthesis in the normalized reference orbit. -/
def suzukiXiCarrierCayleyNormalizedReferenceFiniteSynthesis
    (c : ℤ →₀ ℂ) :
    Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure :=
  ∑ k ∈ c.support,
    c k • suzukiXiCarrierCayleyNormalizedReferenceOrbit k

/-- Parseval for a finite normalized reference synthesis. -/
theorem norm_sq_suzukiXiCarrierCayleyNormalizedReferenceFiniteSynthesis
    (c : ℤ →₀ ℂ) :
    ‖suzukiXiCarrierCayleyNormalizedReferenceFiniteSynthesis c‖ ^ 2 =
      ∑ k ∈ c.support, ‖c k‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ
    (Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure) _ _ _]
  unfold suzukiXiCarrierCayleyNormalizedReferenceFiniteSynthesis
  rw [orthonormal_suzukiXiCarrierCayleyNormalizedReferenceOrbit.inner_sum]
  change (∑ k ∈ c.support,
      conj (c k) * c k).re =
    ∑ k ∈ c.support, ‖c k‖ ^ 2
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Complex.conj_mul']
  norm_cast

/-- Finite synthesis in the unnormalized Cauchy reference orbit. -/
def suzukiXiCarrierCayleyReferenceFiniteSynthesis
    (c : ℤ →₀ ℂ) :
    Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure :=
  ∑ k ∈ c.support, c k • suzukiXiCarrierCayleyReferenceOrbit k

/-- Each unnormalized reference vector is `sqrt(pi)` times its normalized
counterpart. -/
theorem suzukiXiCarrierCayleyReferenceOrbit_eq_sqrtPi_smul_normalized
    (k : ℤ) :
    suzukiXiCarrierCayleyReferenceOrbit k =
      (Real.sqrt Real.pi : ℂ) •
        suzukiXiCarrierCayleyNormalizedReferenceOrbit k := by
  unfold suzukiXiCarrierCayleyNormalizedReferenceOrbit
  rw [smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast (Real.sqrt_ne_zero'.mpr Real.pi_pos)

/-- The whole unnormalized finite synthesis is `sqrt(pi)` times normalized
Fourier synthesis. -/
theorem suzukiXiCarrierCayleyReferenceFiniteSynthesis_eq_sqrtPi_smul
    (c : ℤ →₀ ℂ) :
    suzukiXiCarrierCayleyReferenceFiniteSynthesis c =
      (Real.sqrt Real.pi : ℂ) •
        suzukiXiCarrierCayleyNormalizedReferenceFiniteSynthesis c := by
  unfold suzukiXiCarrierCayleyReferenceFiniteSynthesis
    suzukiXiCarrierCayleyNormalizedReferenceFiniteSynthesis
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [suzukiXiCarrierCayleyReferenceOrbit_eq_sqrtPi_smul_normalized,
    smul_smul, smul_smul, mul_comm (c k)]

/-- Exact finite Parseval identity for the unnormalized Cauchy reference
orbit. -/
theorem norm_sq_suzukiXiCarrierCayleyReferenceFiniteSynthesis
    (c : ℤ →₀ ℂ) :
    ‖suzukiXiCarrierCayleyReferenceFiniteSynthesis c‖ ^ 2 =
      Real.pi * ∑ k ∈ c.support, ‖c k‖ ^ 2 := by
  rw [suzukiXiCarrierCayleyReferenceFiniteSynthesis_eq_sqrtPi_smul,
    norm_smul, mul_pow,
    norm_sq_suzukiXiCarrierCayleyNormalizedReferenceFiniteSynthesis]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg Real.pi),
    Real.sq_sqrt Real.pi_pos.le]

/-- The literal finite Cayley/Laurent polynomial represented by a finitely
supported integer coefficient family. -/
def suzukiXiCarrierCayleyBoundaryFinitePolynomial
    (c : ℤ →₀ ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ c.support,
    c k * suzukiXiCarrierCayleyBoundaryZPower k x

/-- The carrier-space finite synthesis has the literal boundary polynomial
as an almost-everywhere representative. -/
theorem suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis_ae
    (c : ℤ →₀ ℂ) :
    suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis c =ᵐ[
      suzukiXiCarrierNevanlinnaMeasure]
        suzukiXiCarrierCayleyBoundaryFinitePolynomial c := by
  have hsum := Lp.coeFn_fun_finsetSum c.support (fun k ↦
    c k • suzukiXiCarrierCayleyBilateralOrbit k)
  have hterms : ∀ᵐ x : ℝ ∂suzukiXiCarrierNevanlinnaMeasure,
      ∀ k ∈ c.support,
        (c k • suzukiXiCarrierCayleyBilateralOrbit k) x =
          c k * suzukiXiCarrierCayleyBoundaryZPower k x := by
    apply (eventually_all_finset c.support).2
    intro k _hk
    filter_upwards [Lp.coeFn_smul (c k)
        (suzukiXiCarrierCayleyBilateralOrbit k),
      suzukiXiCarrierCayleyBilateralOrbit_ae k] with x hsmul horbit
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [horbit]
  filter_upwards [hsum, hterms] with x hsumx htermsx
  calc
    suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis c x =
        ∑ k ∈ c.support,
          (c k • suzukiXiCarrierCayleyBilateralOrbit k) x := by
      simpa [suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis] using hsumx
    _ = ∑ k ∈ c.support,
        c k * suzukiXiCarrierCayleyBoundaryZPower k x := by
      apply Finset.sum_congr rfl
      intro k hk
      exact htermsx k hk
    _ = suzukiXiCarrierCayleyBoundaryFinitePolynomial c x := rfl

/-- The reference-space finite synthesis represents the same literal
boundary polynomial. -/
theorem suzukiXiCarrierCayleyReferenceFiniteSynthesis_ae
    (c : ℤ →₀ ℂ) :
    suzukiXiCarrierCayleyReferenceFiniteSynthesis c =ᵐ[
      suzukiXiCarrierCayleyReferenceMeasure]
        suzukiXiCarrierCayleyBoundaryFinitePolynomial c := by
  have hsum := Lp.coeFn_fun_finsetSum c.support (fun k ↦
    c k • suzukiXiCarrierCayleyReferenceOrbit k)
  have hterms : ∀ᵐ x : ℝ ∂suzukiXiCarrierCayleyReferenceMeasure,
      ∀ k ∈ c.support,
        (c k • suzukiXiCarrierCayleyReferenceOrbit k) x =
          c k * suzukiXiCarrierCayleyBoundaryZPower k x := by
    apply (eventually_all_finset c.support).2
    intro k _hk
    filter_upwards [Lp.coeFn_smul (c k)
        (suzukiXiCarrierCayleyReferenceOrbit k),
      suzukiXiCarrierCayleyReferenceOrbit_ae k] with x hsmul horbit
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [horbit]
  filter_upwards [hsum, hterms] with x hsumx htermsx
  calc
    suzukiXiCarrierCayleyReferenceFiniteSynthesis c x =
        ∑ k ∈ c.support,
          (c k • suzukiXiCarrierCayleyReferenceOrbit k) x := by
      simpa [suzukiXiCarrierCayleyReferenceFiniteSynthesis] using hsumx
    _ = ∑ k ∈ c.support,
        c k * suzukiXiCarrierCayleyBoundaryZPower k x := by
      apply Finset.sum_congr rfl
      intro k hk
      exact htermsx k hk
    _ = suzukiXiCarrierCayleyBoundaryFinitePolynomial c x := rfl

/-- Domination by the Cauchy measure makes every finite carrier synthesis no
larger than the same literal polynomial in reference `L²`. -/
theorem norm_suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis_le_reference
    (c : ℤ →₀ ℂ) :
    ‖suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis c‖ ≤
      ‖suzukiXiCarrierCayleyReferenceFiniteSynthesis c‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono
  · finiteness
  · calc
      eLpNorm
          (suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis c : ℝ → ℂ)
          2 suzukiXiCarrierNevanlinnaMeasure =
          eLpNorm (suzukiXiCarrierCayleyBoundaryFinitePolynomial c)
            2 suzukiXiCarrierNevanlinnaMeasure :=
        eLpNorm_congr_ae
          (suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis_ae c)
      _ ≤ eLpNorm (suzukiXiCarrierCayleyBoundaryFinitePolynomial c)
          2 suzukiXiCarrierCayleyReferenceMeasure :=
        eLpNorm_mono_measure _
          suzukiXiCarrierNevanlinnaMeasure_le_cayleyReferenceMeasure
      _ = eLpNorm
          (suzukiXiCarrierCayleyReferenceFiniteSynthesis c : ℝ → ℂ)
          2 suzukiXiCarrierCayleyReferenceMeasure :=
        (eLpNorm_congr_ae
          (suzukiXiCarrierCayleyReferenceFiniteSynthesis_ae c)).symm

/-- Explicit unconditional finite Toeplitz synthesis bound for the arithmetic
xi-energy carrier.  The constant `pi` is the total mass of the dominating
unnormalized Cauchy reference measure. -/
theorem norm_sq_suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis_le
    (c : ℤ →₀ ℂ) :
    ‖suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis c‖ ^ 2 ≤
      Real.pi * ∑ k ∈ c.support, ‖c k‖ ^ 2 := by
  calc
    ‖suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis c‖ ^ 2 ≤
        ‖suzukiXiCarrierCayleyReferenceFiniteSynthesis c‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis_le_reference c)
        2
    _ = Real.pi * ∑ k ∈ c.support, ‖c k‖ ^ 2 :=
      norm_sq_suzukiXiCarrierCayleyReferenceFiniteSynthesis c

/-! ## One-sided Hardy synthesis bounds -/

/-- The nonpositive frequencies used by the backward Hardy orbit. -/
def suzukiXiCarrierCayleyBackwardFrequencyEmbedding : ℕ ↪ ℤ where
  toFun m := -(m : ℤ)
  inj' := by
    intro m n hmn
    exact Int.ofNat_injective (neg_injective hmn)

@[simp] theorem suzukiXiCarrierCayleyBackwardFrequencyEmbedding_apply
    (m : ℕ) :
    suzukiXiCarrierCayleyBackwardFrequencyEmbedding m = -(m : ℤ) := rfl

/-- The strictly positive frequencies used by the forward Hardy orbit. -/
def suzukiXiCarrierCayleyForwardFrequencyEmbedding : ℕ ↪ ℤ where
  toFun n := (n + 1 : ℕ)
  inj' := by
    intro m n hmn
    exact Nat.add_right_cancel (Int.ofNat_injective hmn)

@[simp] theorem suzukiXiCarrierCayleyForwardFrequencyEmbedding_apply
    (n : ℕ) :
    suzukiXiCarrierCayleyForwardFrequencyEmbedding n = (n + 1 : ℕ) := rfl

/-- Reindex a backward Hardy coefficient family into bilateral integer
frequencies. -/
def suzukiXiCarrierCayleyBackwardBilateralCoefficients
    (c : ℕ →₀ ℂ) : ℤ →₀ ℂ :=
  Finsupp.embDomain suzukiXiCarrierCayleyBackwardFrequencyEmbedding c

/-- Reindex a forward Hardy coefficient family into bilateral integer
frequencies. -/
def suzukiXiCarrierCayleyForwardBilateralCoefficients
    (d : ℕ →₀ ℂ) : ℤ →₀ ℂ :=
  Finsupp.embDomain suzukiXiCarrierCayleyForwardFrequencyEmbedding d

/-- Backward Hardy synthesis is exactly bilateral synthesis after its
injective frequency reindexing. -/
theorem suzukiXiCarrierCayleyBackwardOrbitFiniteSynthesis_eq_bilateral
    (c : ℕ →₀ ℂ) :
    suzukiXiCarrierCayleyBackwardOrbitFiniteSynthesis c =
      suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis
        (suzukiXiCarrierCayleyBackwardBilateralCoefficients c) := by
  change Finsupp.linearCombination ℂ
      suzukiXiCarrierCayleyBackwardOrbit c =
    Finsupp.linearCombination ℂ
      suzukiXiCarrierCayleyBilateralOrbit
      (Finsupp.embDomain
        suzukiXiCarrierCayleyBackwardFrequencyEmbedding c)
  rw [Finsupp.linearCombination_embDomain]
  simp only [Finsupp.linearCombination_apply, Function.comp_apply,
    suzukiXiCarrierCayleyBackwardOrbit_eq_bilateralOrbit,
    suzukiXiCarrierCayleyBackwardFrequencyEmbedding_apply]

/-- Forward Hardy synthesis is exactly bilateral synthesis after its
injective frequency reindexing. -/
theorem suzukiXiCarrierCayleyForwardOrbitFiniteSynthesis_eq_bilateral
    (d : ℕ →₀ ℂ) :
    suzukiXiCarrierCayleyForwardOrbitFiniteSynthesis d =
      suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis
        (suzukiXiCarrierCayleyForwardBilateralCoefficients d) := by
  change Finsupp.linearCombination ℂ
      suzukiXiCarrierCayleyForwardOrbit d =
    Finsupp.linearCombination ℂ
      suzukiXiCarrierCayleyBilateralOrbit
      (Finsupp.embDomain
        suzukiXiCarrierCayleyForwardFrequencyEmbedding d)
  rw [Finsupp.linearCombination_embDomain]
  simp only [Finsupp.linearCombination_apply, Function.comp_apply,
    suzukiXiCarrierCayleyForwardOrbit_eq_bilateralOrbit,
    suzukiXiCarrierCayleyForwardFrequencyEmbedding_apply]

/-- Injective backward reindexing preserves finite coefficient energy. -/
theorem sum_norm_sq_suzukiXiCarrierCayleyBackwardBilateralCoefficients
    (c : ℕ →₀ ℂ) :
    ∑ k ∈ (suzukiXiCarrierCayleyBackwardBilateralCoefficients c).support,
        ‖suzukiXiCarrierCayleyBackwardBilateralCoefficients c k‖ ^ 2 =
      ∑ m ∈ c.support, ‖c m‖ ^ 2 := by
  unfold suzukiXiCarrierCayleyBackwardBilateralCoefficients
  simp
  apply Finset.sum_congr rfl
  intro m _hm
  rw [← suzukiXiCarrierCayleyBackwardFrequencyEmbedding_apply,
    Finsupp.embDomain_apply_self]

/-- Injective forward reindexing preserves finite coefficient energy. -/
theorem sum_norm_sq_suzukiXiCarrierCayleyForwardBilateralCoefficients
    (d : ℕ →₀ ℂ) :
    ∑ k ∈ (suzukiXiCarrierCayleyForwardBilateralCoefficients d).support,
        ‖suzukiXiCarrierCayleyForwardBilateralCoefficients d k‖ ^ 2 =
      ∑ n ∈ d.support, ‖d n‖ ^ 2 := by
  unfold suzukiXiCarrierCayleyForwardBilateralCoefficients
  simp
  apply Finset.sum_congr rfl
  intro n _hn
  rw [show (n : ℤ) + 1 =
      suzukiXiCarrierCayleyForwardFrequencyEmbedding n by
        simp only [suzukiXiCarrierCayleyForwardFrequencyEmbedding_apply]
        push_cast
        rfl,
    Finsupp.embDomain_apply_self]

/-- Uniform `ℓ² → L²` bound for every finite backward Hardy-orbit
synthesis. -/
theorem norm_sq_suzukiXiCarrierCayleyBackwardOrbitFiniteSynthesis_le
    (c : ℕ →₀ ℂ) :
    ‖suzukiXiCarrierCayleyBackwardOrbitFiniteSynthesis c‖ ^ 2 ≤
      Real.pi * ∑ m ∈ c.support, ‖c m‖ ^ 2 := by
  rw [suzukiXiCarrierCayleyBackwardOrbitFiniteSynthesis_eq_bilateral]
  calc
    ‖suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis
        (suzukiXiCarrierCayleyBackwardBilateralCoefficients c)‖ ^ 2 ≤
        Real.pi *
          ∑ k ∈
              (suzukiXiCarrierCayleyBackwardBilateralCoefficients c).support,
            ‖suzukiXiCarrierCayleyBackwardBilateralCoefficients c k‖ ^ 2 :=
      norm_sq_suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis_le _
    _ = Real.pi * ∑ m ∈ c.support, ‖c m‖ ^ 2 := by
      rw [sum_norm_sq_suzukiXiCarrierCayleyBackwardBilateralCoefficients]

/-- Uniform `ℓ² → L²` bound for every finite forward Hardy-orbit
synthesis. -/
theorem norm_sq_suzukiXiCarrierCayleyForwardOrbitFiniteSynthesis_le
    (d : ℕ →₀ ℂ) :
    ‖suzukiXiCarrierCayleyForwardOrbitFiniteSynthesis d‖ ^ 2 ≤
      Real.pi * ∑ n ∈ d.support, ‖d n‖ ^ 2 := by
  rw [suzukiXiCarrierCayleyForwardOrbitFiniteSynthesis_eq_bilateral]
  calc
    ‖suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis
        (suzukiXiCarrierCayleyForwardBilateralCoefficients d)‖ ^ 2 ≤
        Real.pi *
          ∑ k ∈
              (suzukiXiCarrierCayleyForwardBilateralCoefficients d).support,
            ‖suzukiXiCarrierCayleyForwardBilateralCoefficients d k‖ ^ 2 :=
      norm_sq_suzukiXiCarrierCayleyBilateralOrbitFiniteSynthesis_le _
    _ = Real.pi * ∑ n ∈ d.support, ‖d n‖ ^ 2 := by
      rw [sum_norm_sq_suzukiXiCarrierCayleyForwardBilateralCoefficients]

/-- The finite Hardy Hankel form is uniformly bounded on coefficient
`ℓ²`, stated without square roots.  This is boundedness, not compactness. -/
theorem norm_sq_suzukiXiCarrierCayleyHardyFiniteHankelForm_le
    (c d : ℕ →₀ ℂ) :
    ‖suzukiXiCarrierCayleyHardyFiniteHankelForm c d‖ ^ 2 ≤
      Real.pi ^ 2 *
        (∑ m ∈ c.support, ‖c m‖ ^ 2) *
        (∑ n ∈ d.support, ‖d n‖ ^ 2) := by
  let B := suzukiXiCarrierCayleyBackwardOrbitFiniteSynthesis c
  let F := suzukiXiCarrierCayleyForwardOrbitFiniteSynthesis d
  have hB : ‖B‖ ^ 2 ≤
      Real.pi * ∑ m ∈ c.support, ‖c m‖ ^ 2 := by
    exact norm_sq_suzukiXiCarrierCayleyBackwardOrbitFiniteSynthesis_le c
  have hF : ‖F‖ ^ 2 ≤
      Real.pi * ∑ n ∈ d.support, ‖d n‖ ^ 2 := by
    exact norm_sq_suzukiXiCarrierCayleyForwardOrbitFiniteSynthesis_le d
  have hinner : ‖inner ℂ B F‖ ≤ ‖B‖ * ‖F‖ :=
    norm_inner_le_norm B F
  calc
    ‖suzukiXiCarrierCayleyHardyFiniteHankelForm c d‖ ^ 2 =
        ‖inner ℂ B F‖ ^ 2 := by
      rw [inner_suzukiXiCarrierCayleyBackwardForwardFiniteSynthesis_eq_hankel]
    _ ≤ (‖B‖ * ‖F‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hinner 2
    _ = ‖B‖ ^ 2 * ‖F‖ ^ 2 := by ring
    _ ≤
        (Real.pi * ∑ m ∈ c.support, ‖c m‖ ^ 2) *
          (Real.pi * ∑ n ∈ d.support, ‖d n‖ ^ 2) := by
      exact mul_le_mul hB hF (sq_nonneg ‖F‖)
        (mul_nonneg Real.pi_pos.le (by positivity))
    _ = Real.pi ^ 2 *
        (∑ m ∈ c.support, ‖c m‖ ^ 2) *
        (∑ n ∈ d.support, ‖d n‖ ^ 2) := by ring

end

end RiemannGaussian

import RiemannGaussian.RiemannXiSuzukiCarrierCayleyUnitary
import RiemannGaussian.RiemannXiSuzukiSafeEvaluation

/-!
# Elimination of the Cayley rank-one defect

The Cayley-unitary operator identity leaves one scalar finite-window defect.
This file identifies that scalar exactly with Suzuki's already-constructed
safe-point spectral window at `z = i`, after functional-equation reindexing:

`d_t(T) = (-2*i/sqrt(pi)) * P_{-t,T}(i)`.

Since the safe-point windows converge unconditionally, their two-window
differences tend to zero.  The rank-one term in the Cayley-resolved carrier
frontier therefore vanishes without any RH assumption.  The remaining norm
frontier is proved equivalent to vanishing of the Cayley-weighted synthesis
alone.

No estimate for that remaining synthesis, and no RH conclusion, is asserted
here.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- Negating both spectral frequency and real time changes the extended
Suzuki coefficient by exactly one minus sign, including at the removable
frequency zero. -/
theorem suzukiSpectralScrewCoefficient_neg_parameter
    (t : ℝ) (alpha : ℂ) :
    suzukiSpectralScrewCoefficient t (-alpha) =
      -suzukiSpectralScrewCoefficient (-t) alpha := by
  by_cases halpha : alpha = 0
  · subst alpha
    simp
  · rw [suzukiSpectralScrewCoefficient_of_ne_zero t (neg_ne_zero.mpr halpha),
      suzukiSpectralScrewCoefficient_of_ne_zero (-t) halpha]
    unfold spectralScrewExponential
    have hexponent :
        -Complex.I * -alpha * (t : ℂ) =
          -Complex.I * alpha * ((-t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hexponent]
    field_simp [halpha]

/-- Multiplying the square-root multiplicity coefficient by the normalized
zero-function factor produces multiplicity divided by `sqrt(pi)`. -/
theorem suzukiXiZeroNormalization_mul_coefficientFeature
    (t : ℝ) (rho : NontrivialZetaZero) :
    (suzukiXiZeroNormalization rho : ℂ) *
        zetaSuzukiSpectralCoefficientFeature t rho =
      ((analyticZetaZeroMultiplicity rho : ℂ) *
        suzukiSpectralScrewCoefficient t
          (zetaSpectralCoordinate rho.1)) /
        (Real.sqrt Real.pi : ℂ) := by
  have hm : 0 ≤ (analyticZetaZeroMultiplicity rho : ℝ) :=
    Nat.cast_nonneg _
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hsqrtM :
      (Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) ^ 2 =
        (analyticZetaZeroMultiplicity rho : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hm
  unfold suzukiXiZeroNormalization
    zetaSuzukiSpectralCoefficientFeature
  rw [Real.sqrt_div hm]
  push_cast
  field_simp [hsqrtPi]
  rw [← hsqrtM]
  ring

/-- The elementary scalar exposed by the Cayley transform. -/
def suzukiXiCarrierCayleySafeEvaluationScalar : ℂ :=
  (-2 * Complex.I) / (Real.sqrt Real.pi : ℂ)

/-- One minus the Cayley parameter is the safe resolvent numerator. -/
theorem one_sub_suzukiXiCarrierCayleyParameter
    (z : ℂ) (hz : z + Complex.I ≠ 0) :
    1 - suzukiXiCarrierCayleyParameter z =
      (2 * Complex.I) / (z + Complex.I) := by
  unfold suzukiXiCarrierCayleyParameter
  field_simp [hz]
  ring

/-- One scalar summand in the finite Cayley defect. -/
def suzukiXiCarrierNevanlinnaCayleyDefectSummand
    (t : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  ((suzukiXiZeroNormalization rho : ℂ) *
      zetaSuzukiSpectralCoefficientFeature t rho) *
    (1 - suzukiXiCarrierCayleyNodeParameter rho)

/-- A coordinatewise linear map defining the Cayley defect functional. -/
def suzukiXiCarrierNevanlinnaCayleyDefectCoordinateLinearMap
    (rho : NontrivialZetaZero) : ℂ →ₗ[ℂ] ℂ where
  toFun c :=
    ((suzukiXiZeroNormalization rho : ℂ) * c) *
      (1 - suzukiXiCarrierCayleyNodeParameter rho)
  map_add' c d := by ring
  map_smul' c d := by
    simp only [RingHom.id_apply, smul_eq_mul]
    ring

/-- The scalar Cayley defect as a complex-linear functional on finitely
supported coefficient families. -/
def suzukiXiCarrierNevanlinnaCayleyDefectLinearMap :
    (NontrivialZetaZero →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ
    suzukiXiCarrierNevanlinnaCayleyDefectCoordinateLinearMap

/-- The linear defect functional is exactly the finite-support formula used
by the Cayley-unitary module. -/
@[simp] theorem suzukiXiCarrierNevanlinnaCayleyDefectLinearMap_apply
    (c : NontrivialZetaZero →₀ ℂ) :
    suzukiXiCarrierNevanlinnaCayleyDefectLinearMap c =
      suzukiXiCarrierNevanlinnaCayleyFiniteDefect c := by
  rfl

/-- The Cayley defect of a difference is the difference of the two defects. -/
theorem suzukiXiCarrierNevanlinnaCayleyFiniteDefect_sub
    (c d : NontrivialZetaZero →₀ ℂ) :
    suzukiXiCarrierNevanlinnaCayleyFiniteDefect (c - d) =
      suzukiXiCarrierNevanlinnaCayleyFiniteDefect c -
        suzukiXiCarrierNevanlinnaCayleyFiniteDefect d := by
  rw [← suzukiXiCarrierNevanlinnaCayleyDefectLinearMap_apply,
    map_sub,
    suzukiXiCarrierNevanlinnaCayleyDefectLinearMap_apply,
    suzukiXiCarrierNevanlinnaCayleyDefectLinearMap_apply]

/-- Evaluating the linear defect on one coefficient window gives the literal
finite sum of its scalar defect summands. -/
theorem suzukiXiCarrierNevanlinnaCayleyFiniteDefect_window
    (t T : ℝ) :
    suzukiXiCarrierNevanlinnaCayleyFiniteDefect
        (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T) =
      ∑ rho ∈ spectralZetaZeroWindow T,
        suzukiXiCarrierNevanlinnaCayleyDefectSummand t rho := by
  rw [← suzukiXiCarrierNevanlinnaCayleyDefectLinearMap_apply]
  unfold riemannXiSuzukiSpectralCoefficientWindowFinsupp
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro rho _hrho
  simp [suzukiXiCarrierNevanlinnaCayleyDefectLinearMap,
    suzukiXiCarrierNevanlinnaCayleyDefectCoordinateLinearMap,
    suzukiXiCarrierNevanlinnaCayleyDefectSummand]

/-- Every nonnegative symmetric spectral window is invariant under
functional-equation reflection, which negates the spectral coordinate. -/
theorem functionalPartner_mem_spectralZetaZeroWindow_iff
    {T : ℝ} (hT : 0 ≤ T) (rho : NontrivialZetaZero) :
    NontrivialZetaZero.functionalPartner rho ∈ spectralZetaZeroWindow T ↔
      rho ∈ spectralZetaZeroWindow T := by
  rw [mem_spectralZetaZeroWindow hT,
    mem_spectralZetaZeroWindow hT,
    NontrivialZetaZero.spectralCoordinate_functionalPartner]
  simp

/-- After functional-equation reflection, one Cayley defect summand is
exactly the universal safe-evaluation scalar times the `P_{-t}(i)` summand. -/
theorem suzukiXiCarrierNevanlinnaCayleyDefectSummand_functionalPartner
    (t : ℝ) (rho : NontrivialZetaZero) :
    suzukiXiCarrierNevanlinnaCayleyDefectSummand t
        (NontrivialZetaZero.functionalPartner rho) =
      suzukiXiCarrierCayleySafeEvaluationScalar *
        zetaSuzukiSpectralPAtISummand (-t) rho := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  have hsafe : suzukiXiSafeEvaluationDenominator alpha ≠ 0 :=
    Complex.normSq_pos.mp
      (normSq_suzukiXiSafeEvaluationDenominator_pos rho)
  have hnegSafe : -alpha + Complex.I ≠ 0 := by
    simpa only [suzukiXiSafeEvaluationDenominator, sub_eq_add_neg,
      add_comm] using hsafe
  unfold suzukiXiCarrierNevanlinnaCayleyDefectSummand
    suzukiXiCarrierCayleyNodeParameter
  rw [suzukiXiZeroNormalization_mul_coefficientFeature]
  simp only [analyticZetaZeroMultiplicity_functionalPartner,
    NontrivialZetaZero.spectralCoordinate_functionalPartner]
  rw [suzukiSpectralScrewCoefficient_neg_parameter]
  rw [one_sub_suzukiXiCarrierCayleyParameter (-alpha) hnegSafe]
  unfold suzukiXiCarrierCayleySafeEvaluationScalar
    zetaSuzukiSpectralPAtISummand
    suzukiXiSafeEvaluationDenominator
  dsimp [alpha]
  have hsqrtPi : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp [hsqrtPi, hsafe]
  ring

/-- The finite Cayley defect is exactly a safe-point Suzuki spectral window
at reflected time.  The functional equation supplies the required
reindexing of the symmetric zero window. -/
theorem suzukiXiCarrierNevanlinnaCayleyFiniteDefect_window_eq_safeEvaluation
    {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    suzukiXiCarrierNevanlinnaCayleyFiniteDefect
        (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T) =
      suzukiXiCarrierCayleySafeEvaluationScalar *
        suzukiXiSpectralPWindow (-t) T Complex.I := by
  rw [suzukiXiCarrierNevanlinnaCayleyFiniteDefect_window]
  calc
    (∑ rho ∈ spectralZetaZeroWindow T,
        suzukiXiCarrierNevanlinnaCayleyDefectSummand t rho) =
        ∑ rho ∈ spectralZetaZeroWindow T,
          suzukiXiCarrierNevanlinnaCayleyDefectSummand t
            (NontrivialZetaZero.functionalPartner rho) := by
      symm
      refine Finset.sum_bij
        (fun rho _hrho ↦ NontrivialZetaZero.functionalPartner rho)
        ?_ ?_ ?_ ?_
      · intro rho hrho
        exact
          (functionalPartner_mem_spectralZetaZeroWindow_iff hT rho).2 hrho
      · intro rho₁ _hrho₁ rho₂ _hrho₂ heq
        exact NontrivialZetaZero.functionalPartnerEquiv.injective heq
      · intro rho hrho
        refine ⟨NontrivialZetaZero.functionalPartner rho, ?_, ?_⟩
        · exact
            (functionalPartner_mem_spectralZetaZeroWindow_iff hT rho).2 hrho
        · simp
      · intro rho _hrho
        rfl
    _ = ∑ rho ∈ spectralZetaZeroWindow T,
          suzukiXiCarrierCayleySafeEvaluationScalar *
            zetaSuzukiSpectralPAtISummand (-t) rho := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      exact
        suzukiXiCarrierNevanlinnaCayleyDefectSummand_functionalPartner
          t rho
    _ = suzukiXiCarrierCayleySafeEvaluationScalar *
        ∑ rho ∈ spectralZetaZeroWindow T,
          zetaSuzukiSpectralPAtISummand (-t) rho := by
      rw [Finset.mul_sum]
    _ = suzukiXiCarrierCayleySafeEvaluationScalar *
        suzukiXiSpectralPWindow (-t) T Complex.I := by
      rfl

/-- The scalar Cayley defect of a two-window coefficient tail is the
corresponding difference of safe-point Suzuki windows. -/
theorem suzukiXiCoefficientTailNevanlinnaCayleyDefect_eq_safeEvaluation_sub
    (t : ℝ) {T U : ℝ} (hT : 0 ≤ T) (hU : 0 ≤ U) :
    suzukiXiCoefficientTailNevanlinnaCayleyDefect t T U =
      suzukiXiCarrierCayleySafeEvaluationScalar *
        (suzukiXiSpectralPWindow (-t) T Complex.I -
          suzukiXiSpectralPWindow (-t) U Complex.I) := by
  unfold suzukiXiCoefficientTailNevanlinnaCayleyDefect
    riemannXiSuzukiSpectralCoefficientTailFinsupp
  rw [suzukiXiCarrierNevanlinnaCayleyFiniteDefect_sub,
    suzukiXiCarrierNevanlinnaCayleyFiniteDefect_window_eq_safeEvaluation hT,
    suzukiXiCarrierNevanlinnaCayleyFiniteDefect_window_eq_safeEvaluation hU]
  ring

/-- The finite-window Cayley defects converge unconditionally because they
are eventually identical to a fixed scalar multiple of the convergent
safe-point Suzuki windows. -/
theorem tendsto_suzukiXiCarrierNevanlinnaCayleyFiniteDefect_window
    (t : ℝ) :
    Tendsto (fun T : ℝ ↦
      suzukiXiCarrierNevanlinnaCayleyFiniteDefect
        (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T)) atTop
      (nhds (suzukiXiCarrierCayleySafeEvaluationScalar *
        riemannXiSuzukiSpectralPAtI (-t))) := by
  refine (tendsto_const_nhds.mul
    (tendsto_suzukiXiSpectralPWindow_at_I (-t))).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact
    (suzukiXiCarrierNevanlinnaCayleyFiniteDefect_window_eq_safeEvaluation
      hT t).symm

/-- The rank-one Cayley vector attached to one finite coefficient window. -/
def suzukiXiCoefficientWindowNevanlinnaCayleyDefectVector
    (t T : ℝ) : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  suzukiXiCarrierNevanlinnaCayleyFiniteDefect
      (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T) •
    suzukiXiCarrierCayleyUnitary suzukiXiCarrierNevanlinnaOneLp

/-- The rank-one window vectors themselves converge in the finite-measure
carrier Hilbert space. -/
theorem tendsto_suzukiXiCoefficientWindowNevanlinnaCayleyDefectVector
    (t : ℝ) :
    Tendsto (suzukiXiCoefficientWindowNevanlinnaCayleyDefectVector t) atTop
      (nhds ((suzukiXiCarrierCayleySafeEvaluationScalar *
          riemannXiSuzukiSpectralPAtI (-t)) •
        suzukiXiCarrierCayleyUnitary
          suzukiXiCarrierNevanlinnaOneLp)) := by
  exact
    (tendsto_suzukiXiCarrierNevanlinnaCayleyFiniteDefect_window t).smul_const _

/-- The rank-one vector of a coefficient tail is exactly the difference of
the two convergent window vectors. -/
theorem suzukiXiCoefficientTailNevanlinnaCayleyDefect_smul_eq_sub
    (t T U : ℝ) :
    suzukiXiCoefficientTailNevanlinnaCayleyDefect t T U •
        suzukiXiCarrierCayleyUnitary suzukiXiCarrierNevanlinnaOneLp =
      suzukiXiCoefficientWindowNevanlinnaCayleyDefectVector t T -
        suzukiXiCoefficientWindowNevanlinnaCayleyDefectVector t U := by
  unfold suzukiXiCoefficientTailNevanlinnaCayleyDefect
    riemannXiSuzukiSpectralCoefficientTailFinsupp
    suzukiXiCoefficientWindowNevanlinnaCayleyDefectVector
  rw [suzukiXiCarrierNevanlinnaCayleyFiniteDefect_sub, sub_smul]

/-- The formerly unresolved rank-one Cayley term has uniformly vanishing
squared norm along all sufficiently late pairs of genuine spectral windows. -/
def SuzukiXiCoefficientTailCayleyDefectNormVanishing (t : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R,
      ‖suzukiXiCoefficientTailNevanlinnaCayleyDefect t T U •
        suzukiXiCarrierCayleyUnitary
          suzukiXiCarrierNevanlinnaOneLp‖ ^ 2 < epsilon

/-- Safe-point absolute convergence eliminates the rank-one Cayley defect
without an RH hypothesis. -/
theorem suzukiXiCoefficientTailCayleyDefectNormVanishing
    (t : ℝ) :
    SuzukiXiCoefficientTailCayleyDefectNormVanishing t := by
  have hcauchy : CauchySeq
      (suzukiXiCoefficientWindowNevanlinnaCayleyDefectVector t) :=
    (tendsto_suzukiXiCoefficientWindowNevanlinnaCayleyDefectVector t).cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  intro epsilon hepsilon
  obtain ⟨R, hR⟩ := hcauchy (Real.sqrt epsilon)
    (Real.sqrt_pos.2 hepsilon)
  refine ⟨R, ?_⟩
  intro T hT U hU
  have hdist := hR T hT U hU
  rw [dist_eq_norm] at hdist
  rw [suzukiXiCoefficientTailNevanlinnaCayleyDefect_smul_eq_sub]
  calc
    ‖suzukiXiCoefficientWindowNevanlinnaCayleyDefectVector t T -
        suzukiXiCoefficientWindowNevanlinnaCayleyDefectVector t U‖ ^ 2 <
        (Real.sqrt epsilon) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hdist
    _ = epsilon := Real.sq_sqrt hepsilon.le

/-! ## Removing the convergent rank-one perturbation -/

/-- Uniform two-sided tail vanishing in norm for a family indexed by two
real window parameters. -/
def TwoSidedTailNormVanishing
    {E : Type*} [NormedAddCommGroup E] (F : ℝ → ℝ → E) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R, ‖F T U‖ < epsilon

/-- Uniform two-sided tail vanishing in squared norm. -/
def TwoSidedTailNormSqVanishing
    {E : Type*} [NormedAddCommGroup E] (F : ℝ → ℝ → E) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R, ‖F T U‖ ^ 2 < epsilon

/-- Squared-norm tail vanishing is equivalent to ordinary norm tail
vanishing. -/
theorem twoSidedTailNormSqVanishing_iff_normVanishing
    {E : Type*} [NormedAddCommGroup E] (F : ℝ → ℝ → E) :
    TwoSidedTailNormSqVanishing F ↔ TwoSidedTailNormVanishing F := by
  constructor
  · intro hsquared epsilon hepsilon
    obtain ⟨R, hR⟩ := hsquared (epsilon ^ 2) (sq_pos_of_pos hepsilon)
    refine ⟨R, ?_⟩
    intro T hT U hU
    exact (sq_lt_sq₀ (norm_nonneg _) hepsilon.le).1 (hR T hT U hU)
  · intro hnorm epsilon hepsilon
    obtain ⟨R, hR⟩ := hnorm (Real.sqrt epsilon)
      (Real.sqrt_pos.2 hepsilon)
    refine ⟨R, ?_⟩
    intro T hT U hU
    calc
      ‖F T U‖ ^ 2 < (Real.sqrt epsilon) ^ 2 :=
        (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2
          (hR T hT U hU)
      _ = epsilon := Real.sq_sqrt hepsilon.le

/-- Adding a uniformly vanishing tail does not change whether another tail
vanishes. -/
theorem twoSidedTailNormVanishing_add_iff_left
    {E : Type*} [NormedAddCommGroup E] (F G : ℝ → ℝ → E)
    (hG : TwoSidedTailNormVanishing G) :
    TwoSidedTailNormVanishing (fun T U ↦ F T U + G T U) ↔
      TwoSidedTailNormVanishing F := by
  constructor
  · intro hsum epsilon hepsilon
    obtain ⟨RF, hF⟩ := hsum (epsilon / 2) (half_pos hepsilon)
    obtain ⟨RG, hGtail⟩ := hG (epsilon / 2) (half_pos hepsilon)
    refine ⟨max RF RG, ?_⟩
    intro T hT U hU
    have hTF : RF ≤ T := (le_max_left RF RG).trans hT
    have hTG : RG ≤ T := (le_max_right RF RG).trans hT
    have hUF : RF ≤ U := (le_max_left RF RG).trans hU
    have hUG : RG ≤ U := (le_max_right RF RG).trans hU
    calc
      ‖F T U‖ = ‖(F T U + G T U) - G T U‖ := by
        congr 1
        abel
      _ ≤ ‖F T U + G T U‖ + ‖G T U‖ := norm_sub_le _ _
      _ < epsilon / 2 + epsilon / 2 :=
        add_lt_add (hF T hTF U hUF) (hGtail T hTG U hUG)
      _ = epsilon := by ring
  · intro hF epsilon hepsilon
    obtain ⟨RF, hFtail⟩ := hF (epsilon / 2) (half_pos hepsilon)
    obtain ⟨RG, hGtail⟩ := hG (epsilon / 2) (half_pos hepsilon)
    refine ⟨max RF RG, ?_⟩
    intro T hT U hU
    have hTF : RF ≤ T := (le_max_left RF RG).trans hT
    have hTG : RG ≤ T := (le_max_right RF RG).trans hT
    have hUF : RF ≤ U := (le_max_left RF RG).trans hU
    have hUG : RG ≤ U := (le_max_right RF RG).trans hU
    calc
      ‖F T U + G T U‖ ≤ ‖F T U‖ + ‖G T U‖ := norm_add_le _ _
      _ < epsilon / 2 + epsilon / 2 :=
        add_lt_add (hFtail T hTF U hUF) (hGtail T hTG U hUG)
      _ = epsilon := by ring

/-- The same perturbation principle in the squared-norm formulation used by
the Suzuki frontier. -/
theorem twoSidedTailNormSqVanishing_add_iff_left
    {E : Type*} [NormedAddCommGroup E] (F G : ℝ → ℝ → E)
    (hG : TwoSidedTailNormSqVanishing G) :
    TwoSidedTailNormSqVanishing (fun T U ↦ F T U + G T U) ↔
      TwoSidedTailNormSqVanishing F := by
  have hGnorm :=
    (twoSidedTailNormSqVanishing_iff_normVanishing G).1 hG
  simpa only [twoSidedTailNormSqVanishing_iff_normVanishing] using
    twoSidedTailNormVanishing_add_iff_left F G hGnorm

/-- The sharpened frontier after the safe-point rank-one term has been
eliminated: only the Cayley-weighted synthesis remains. -/
def SuzukiXiCoefficientTailCayleyWeightedNormVanishing (t : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R,
      ‖suzukiXiCoefficientTailNevanlinnaCayleyWeightedSynthesis t T U‖ ^ 2 <
        epsilon

/-- The Cayley-resolved frontier is equivalent to the weighted synthesis
frontier alone; the exact rank-one term has now been discharged. -/
theorem coefficientTailCayleyResolvedNormVanishing_iff_cayleyWeighted
    (t : ℝ) :
    SuzukiXiCoefficientTailCayleyResolvedNormVanishing t ↔
      SuzukiXiCoefficientTailCayleyWeightedNormVanishing t := by
  change TwoSidedTailNormSqVanishing (fun T U ↦
      suzukiXiCoefficientTailNevanlinnaCayleyWeightedSynthesis t T U +
        suzukiXiCoefficientTailNevanlinnaCayleyDefect t T U •
          suzukiXiCarrierCayleyUnitary
            suzukiXiCarrierNevanlinnaOneLp) ↔
    TwoSidedTailNormSqVanishing (fun T U ↦
      suzukiXiCoefficientTailNevanlinnaCayleyWeightedSynthesis t T U)
  apply twoSidedTailNormSqVanishing_add_iff_left
  exact suzukiXiCoefficientTailCayleyDefectNormVanishing t

/-- The original coefficient-tail Gram frontier is therefore exactly the
vanishing problem for the Cayley-weighted synthesis, with no residual
rank-one term. -/
theorem coefficientTailGramVanishing_iff_cayleyWeighted
    (t : ℝ) :
    SuzukiXiCoefficientTailGramVanishing t ↔
      SuzukiXiCoefficientTailCayleyWeightedNormVanishing t := by
  rw [coefficientTailGramVanishing_iff_cayleyResolved,
    coefficientTailCayleyResolvedNormVanishing_iff_cayleyWeighted]

end

end RiemannGaussian

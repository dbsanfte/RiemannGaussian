import RiemannGaussian.RiemannXiSuzukiCarrierCayleyTimeTrace

/-!
# Spectral decomposition of the finite Cayley time traces

This file separates the finite upper and lower Cayley time traces into two
pieces.  The first is the multiplicity-weighted, unregularized Suzuki screw
trace.  The second is a half-plane restriction of Suzuki's finite spectral
`P_t` window.  The elementary identity

`(alpha - i) / (alpha + i) = 1 + 2 i / (-i - alpha)`

gives the decomposition at the otherwise unsafe point `-i`.  Functional-
equation reflection then moves each restricted `-i` term to the genuinely
safe point `i` in the opposite spectral half-plane.  Thus no convergence at
`-i` is assumed or used.

The safe restricted windows are also proved convergent from the existing
absolutely summable `P_t(i)` series.  The only pointwise convergence left in
the finite time traces is consequently the unregularized half-divisor screw
trace.  This is an exact reduction, not an assertion that this final trace
converges.
-/

open Complex Filter Set Topology
open scoped Classical ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- One multiplicity-weighted term of the unregularized Suzuki screw trace. -/
def zetaSuzukiSpectralScrewTraceSummand
    (t : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  (analyticZetaZeroMultiplicity rho : ℂ) *
    suzukiSpectralScrewCoefficient t
      (zetaSpectralCoordinate rho.1)

/-- The finite upper-half-plane part of the unregularized Suzuki screw
trace. -/
def suzukiXiUpperScrewTraceWindow (t T : ℝ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    if 0 < (zetaSpectralCoordinate rho.1).im then
      zetaSuzukiSpectralScrewTraceSummand t rho
    else 0

/-- The finite lower-half-plane part of the unregularized Suzuki screw
trace. -/
def suzukiXiLowerScrewTraceWindow (t T : ℝ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    if (zetaSpectralCoordinate rho.1).im < 0 then
      zetaSuzukiSpectralScrewTraceSummand t rho
    else 0

/-- The upper-half-plane restriction of a finite spectral `P_t(z)` window. -/
def suzukiXiUpperRestrictedSpectralPWindow
    (t T : ℝ) (z : ℂ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    if 0 < (zetaSpectralCoordinate rho.1).im then
      zetaSuzukiSpectralPSummand t z rho
    else 0

/-- The lower-half-plane restriction of a finite spectral `P_t(z)` window. -/
def suzukiXiLowerRestrictedSpectralPWindow
    (t T : ℝ) (z : ℂ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    if (zetaSpectralCoordinate rho.1).im < 0 then
      zetaSuzukiSpectralPSummand t z rho
    else 0

/-- The universal normalization multiplying both finite trace
decompositions. -/
def suzukiXiCarrierCayleyTimeTraceScale : ℂ :=
  (Real.sqrt 2 : ℂ) / (Real.sqrt Real.pi : ℂ)

/-- The Cayley parameter is one plus twice the Cauchy resolvent at `-i`. -/
theorem suzukiXiCarrierCayleyParameter_eq_one_add_negI_resolvent
    (z : ℂ) (hz : z + Complex.I ≠ 0) :
    suzukiXiCarrierCayleyParameter z =
      1 + (2 * Complex.I) / (-Complex.I - z) := by
  unfold suzukiXiCarrierCayleyParameter
  have hneg : -Complex.I - z ≠ 0 := by
    intro hzero
    apply hz
    linear_combination -hzero
  field_simp [hz, hneg]
  ring

/-- One normalized Cayley time coefficient is exactly an unregularized
screw-trace term plus twice the corresponding spectral `P_t(-i)` term. -/
theorem suzukiXiCarrierCayleyTimeCoefficient_eq_screwTrace_add_negI
    (t : ℝ) (rho : NontrivialZetaZero) :
    suzukiXiCarrierCayleyTimeCoefficient t rho =
      (1 / (Real.sqrt Real.pi : ℂ)) *
        (zetaSuzukiSpectralScrewTraceSummand t rho +
          2 * Complex.I *
            zetaSuzukiSpectralPSummand t (-Complex.I) rho) := by
  have hnode := zetaSpectralCoordinate_add_I_ne_zero rho
  have hsqrtPi : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  unfold suzukiXiCarrierCayleyTimeCoefficient
  rw [suzukiXiZeroNormalization_mul_coefficientFeature]
  unfold suzukiXiCarrierCayleyNodeParameter
  rw [suzukiXiCarrierCayleyParameter_eq_one_add_negI_resolvent _ hnode]
  unfold zetaSuzukiSpectralScrewTraceSummand
    zetaSuzukiSpectralPSummand
    suzukiXiUpperEvaluationDenominator
  have hneg :
      -Complex.I - zetaSpectralCoordinate rho.1 ≠ 0 := by
    intro hzero
    apply hnode
    linear_combination -hzero
  field_simp [hsqrtPi, hneg]

/-- The finite upper Cayley trace is the normalized sum of its upper screw
trace and twice its upper restricted `P_t(-i)` window. -/
theorem suzukiXiCarrierCayleyUpperTimeTraceWindow_eq_screwTrace_add_negI
    (t T : ℝ) :
    suzukiXiCarrierCayleyUpperTimeTraceWindow t T =
      suzukiXiCarrierCayleyTimeTraceScale *
        (suzukiXiUpperScrewTraceWindow t T +
          2 * Complex.I *
            suzukiXiUpperRestrictedSpectralPWindow
              t T (-Complex.I)) := by
  rw [suzukiXiCarrierCayleyUpperTimeTraceWindow_eq_sum]
  unfold suzukiXiCarrierCayleyTimeTraceScale
    suzukiXiUpperScrewTraceWindow
    suzukiXiUpperRestrictedSpectralPWindow
  simp only [mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _hrho
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · simp only [if_pos hupper]
    rw [suzukiXiCarrierCayleyTimeCoefficient_eq_screwTrace_add_negI]
    ring
  · simp only [if_neg hupper, mul_zero, add_zero]

/-- The finite lower Cayley trace is the normalized sum of its lower screw
trace and twice its lower restricted `P_t(-i)` window. -/
theorem suzukiXiCarrierCayleyLowerTimeTraceWindow_eq_screwTrace_add_negI
    (t T : ℝ) :
    suzukiXiCarrierCayleyLowerTimeTraceWindow t T =
      suzukiXiCarrierCayleyTimeTraceScale *
        (suzukiXiLowerScrewTraceWindow t T +
          2 * Complex.I *
            suzukiXiLowerRestrictedSpectralPWindow
              t T (-Complex.I)) := by
  rw [suzukiXiCarrierCayleyLowerTimeTraceWindow_eq_sum]
  unfold suzukiXiCarrierCayleyTimeTraceScale
    suzukiXiLowerScrewTraceWindow
    suzukiXiLowerRestrictedSpectralPWindow
  simp only [mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _hrho
  by_cases hlower : (zetaSpectralCoordinate rho.1).im < 0
  · simp only [if_pos hlower]
    rw [suzukiXiCarrierCayleyTimeCoefficient_eq_screwTrace_add_negI]
    ring
  · simp only [if_neg hlower, mul_zero, add_zero]

/-- Functional-equation reflection changes an unregularized screw-trace
summand by time reversal and one minus sign. -/
theorem zetaSuzukiSpectralScrewTraceSummand_functionalPartner
    (t : ℝ) (rho : NontrivialZetaZero) :
    zetaSuzukiSpectralScrewTraceSummand t
        (NontrivialZetaZero.functionalPartner rho) =
      -zetaSuzukiSpectralScrewTraceSummand (-t) rho := by
  unfold zetaSuzukiSpectralScrewTraceSummand
  simp only [analyticZetaZeroMultiplicity_functionalPartner,
    NontrivialZetaZero.spectralCoordinate_functionalPartner]
  rw [suzukiSpectralScrewCoefficient_neg_parameter]
  ring

/-- Functional-equation reflection transports a spectral `P_t` summand at
`-i` to the safe point `i`, with reversed screw time. -/
theorem zetaSuzukiSpectralPSummand_negI_functionalPartner
    (t : ℝ) (rho : NontrivialZetaZero) :
    zetaSuzukiSpectralPSummand t (-Complex.I)
        (NontrivialZetaZero.functionalPartner rho) =
      zetaSuzukiSpectralPSummand (-t) Complex.I rho := by
  unfold zetaSuzukiSpectralPSummand
    suzukiXiUpperEvaluationDenominator
  simp only [analyticZetaZeroMultiplicity_functionalPartner,
    NontrivialZetaZero.spectralCoordinate_functionalPartner]
  rw [suzukiSpectralScrewCoefficient_neg_parameter]
  have hsafe :
      Complex.I - zetaSpectralCoordinate rho.1 ≠ 0 :=
    Complex.normSq_pos.mp
      (normSq_suzukiXiSafeEvaluationDenominator_pos rho)
  have hreflected :
      -Complex.I - -zetaSpectralCoordinate rho.1 ≠ 0 := by
    intro hzero
    apply hsafe
    linear_combination -hzero
  field_simp [hsafe, hreflected]
  ring

/-- Summation over a nonnegative symmetric spectral window is unchanged by
functional-equation reflection. -/
theorem sum_spectralZetaZeroWindow_comp_functionalPartner
    {T : ℝ} (hT : 0 ≤ T) (f : NontrivialZetaZero → ℂ) :
    (∑ rho ∈ spectralZetaZeroWindow T,
        f (NontrivialZetaZero.functionalPartner rho)) =
      ∑ rho ∈ spectralZetaZeroWindow T, f rho := by
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
    simp

/-- The lower unregularized screw trace is the time-reversed upper trace
with one minus sign. -/
theorem suzukiXiLowerScrewTraceWindow_eq_neg_upper
    (t : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    suzukiXiLowerScrewTraceWindow t T =
      -suzukiXiUpperScrewTraceWindow (-t) T := by
  unfold suzukiXiLowerScrewTraceWindow
    suzukiXiUpperScrewTraceWindow
  calc
    (∑ rho ∈ spectralZetaZeroWindow T,
        if (zetaSpectralCoordinate rho.1).im < 0 then
          zetaSuzukiSpectralScrewTraceSummand t rho
        else 0) =
        ∑ rho ∈ spectralZetaZeroWindow T,
          if (zetaSpectralCoordinate
              (NontrivialZetaZero.functionalPartner rho).1).im < 0 then
            zetaSuzukiSpectralScrewTraceSummand t
              (NontrivialZetaZero.functionalPartner rho)
          else 0 := by
      symm
      simpa using
        (sum_spectralZetaZeroWindow_comp_functionalPartner hT
          (fun rho ↦
            if (zetaSpectralCoordinate rho.1).im < 0 then
              zetaSuzukiSpectralScrewTraceSummand t rho
            else 0))
    _ = ∑ rho ∈ spectralZetaZeroWindow T,
          -(if 0 < (zetaSpectralCoordinate rho.1).im then
              zetaSuzukiSpectralScrewTraceSummand (-t) rho
            else 0) := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
      · simp only [NontrivialZetaZero.spectralCoordinate_functionalPartner,
          neg_im, neg_lt_zero, if_pos hupper]
        rw [zetaSuzukiSpectralScrewTraceSummand_functionalPartner]
      · have hnotLower :
            ¬(zetaSpectralCoordinate
                (NontrivialZetaZero.functionalPartner rho).1).im < 0 := by
          simp only [NontrivialZetaZero.spectralCoordinate_functionalPartner,
            neg_im, neg_lt_zero]
          exact hupper
        simp only [if_neg hnotLower, if_neg hupper, neg_zero]
    _ = -(∑ rho ∈ spectralZetaZeroWindow T,
          if 0 < (zetaSpectralCoordinate rho.1).im then
            zetaSuzukiSpectralScrewTraceSummand (-t) rho
          else 0) := by
      rw [Finset.sum_neg_distrib]

/-- The upper restricted `P_t(-i)` window is exactly the reflected lower
restricted window at the safe point `i`. -/
theorem suzukiXiUpperRestrictedSpectralPWindow_negI_eq_lower_atI
    (t : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    suzukiXiUpperRestrictedSpectralPWindow t T (-Complex.I) =
      suzukiXiLowerRestrictedSpectralPWindow (-t) T Complex.I := by
  unfold suzukiXiUpperRestrictedSpectralPWindow
    suzukiXiLowerRestrictedSpectralPWindow
  calc
    (∑ rho ∈ spectralZetaZeroWindow T,
        if 0 < (zetaSpectralCoordinate rho.1).im then
          zetaSuzukiSpectralPSummand t (-Complex.I) rho
        else 0) =
        ∑ rho ∈ spectralZetaZeroWindow T,
          if 0 < (zetaSpectralCoordinate
              (NontrivialZetaZero.functionalPartner rho).1).im then
            zetaSuzukiSpectralPSummand t (-Complex.I)
              (NontrivialZetaZero.functionalPartner rho)
          else 0 := by
      symm
      simpa using
        (sum_spectralZetaZeroWindow_comp_functionalPartner hT
          (fun rho ↦
            if 0 < (zetaSpectralCoordinate rho.1).im then
              zetaSuzukiSpectralPSummand t (-Complex.I) rho
            else 0))
    _ = ∑ rho ∈ spectralZetaZeroWindow T,
          if (zetaSpectralCoordinate rho.1).im < 0 then
            zetaSuzukiSpectralPSummand (-t) Complex.I rho
          else 0 := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      by_cases hlower : (zetaSpectralCoordinate rho.1).im < 0
      · simp only [NontrivialZetaZero.spectralCoordinate_functionalPartner,
          neg_im, neg_pos, if_pos hlower]
        rw [zetaSuzukiSpectralPSummand_negI_functionalPartner]
      · have hnotUpper :
            ¬0 < (zetaSpectralCoordinate
                (NontrivialZetaZero.functionalPartner rho).1).im := by
          simp only [NontrivialZetaZero.spectralCoordinate_functionalPartner,
            neg_im, neg_pos]
          exact hlower
        simp only [if_neg hnotUpper, if_neg hlower]

/-- The lower restricted `P_t(-i)` window is exactly the reflected upper
restricted window at the safe point `i`. -/
theorem suzukiXiLowerRestrictedSpectralPWindow_negI_eq_upper_atI
    (t : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    suzukiXiLowerRestrictedSpectralPWindow t T (-Complex.I) =
      suzukiXiUpperRestrictedSpectralPWindow (-t) T Complex.I := by
  unfold suzukiXiLowerRestrictedSpectralPWindow
    suzukiXiUpperRestrictedSpectralPWindow
  calc
    (∑ rho ∈ spectralZetaZeroWindow T,
        if (zetaSpectralCoordinate rho.1).im < 0 then
          zetaSuzukiSpectralPSummand t (-Complex.I) rho
        else 0) =
        ∑ rho ∈ spectralZetaZeroWindow T,
          if (zetaSpectralCoordinate
              (NontrivialZetaZero.functionalPartner rho).1).im < 0 then
            zetaSuzukiSpectralPSummand t (-Complex.I)
              (NontrivialZetaZero.functionalPartner rho)
          else 0 := by
      symm
      simpa using
        (sum_spectralZetaZeroWindow_comp_functionalPartner hT
          (fun rho ↦
            if (zetaSpectralCoordinate rho.1).im < 0 then
              zetaSuzukiSpectralPSummand t (-Complex.I) rho
            else 0))
    _ = ∑ rho ∈ spectralZetaZeroWindow T,
          if 0 < (zetaSpectralCoordinate rho.1).im then
            zetaSuzukiSpectralPSummand (-t) Complex.I rho
          else 0 := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
      · simp only [NontrivialZetaZero.spectralCoordinate_functionalPartner,
          neg_im, neg_lt_zero, if_pos hupper]
        rw [zetaSuzukiSpectralPSummand_negI_functionalPartner]
      · have hnotLower :
            ¬(zetaSpectralCoordinate
                (NontrivialZetaZero.functionalPartner rho).1).im < 0 := by
          simp only [NontrivialZetaZero.spectralCoordinate_functionalPartner,
            neg_im, neg_lt_zero]
          exact hupper
        simp only [if_neg hnotLower, if_neg hupper]

/-- The upper finite Cayley trace uses only an upper screw trace and a lower
restricted `P` window at the safe point `i`. -/
theorem suzukiXiCarrierCayleyUpperTimeTraceWindow_eq_screwTrace_add_safeP
    (t : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    suzukiXiCarrierCayleyUpperTimeTraceWindow t T =
      suzukiXiCarrierCayleyTimeTraceScale *
        (suzukiXiUpperScrewTraceWindow t T +
          2 * Complex.I *
            suzukiXiLowerRestrictedSpectralPWindow
              (-t) T Complex.I) := by
  rw [suzukiXiCarrierCayleyUpperTimeTraceWindow_eq_screwTrace_add_negI,
    suzukiXiUpperRestrictedSpectralPWindow_negI_eq_lower_atI t hT]

/-- The lower finite Cayley trace is expressed entirely through a
time-reversed upper screw trace and an upper restricted `P` window at the
safe point `i`. -/
theorem suzukiXiCarrierCayleyLowerTimeTraceWindow_eq_upperScrewTrace_add_safeP
    (t : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    suzukiXiCarrierCayleyLowerTimeTraceWindow t T =
      suzukiXiCarrierCayleyTimeTraceScale *
        (-suzukiXiUpperScrewTraceWindow (-t) T +
          2 * Complex.I *
            suzukiXiUpperRestrictedSpectralPWindow
              (-t) T Complex.I) := by
  rw [suzukiXiCarrierCayleyLowerTimeTraceWindow_eq_screwTrace_add_negI,
    suzukiXiLowerScrewTraceWindow_eq_neg_upper t hT,
    suzukiXiLowerRestrictedSpectralPWindow_negI_eq_upper_atI t hT]

/-- The general spectral summand at `i` is definitionally the safe-point
summand constructed from the coefficient Hilbert space. -/
theorem zetaSuzukiSpectralPSummand_at_I
    (t : ℝ) (rho : NontrivialZetaZero) :
    zetaSuzukiSpectralPSummand t Complex.I rho =
      zetaSuzukiSpectralPAtISummand t rho := by
  rfl

/-- The upper restriction of the safe-point spectral series is absolutely
summable. -/
theorem summable_zetaSuzukiUpperRestrictedSpectralPSummand_at_I
    (t : ℝ) :
    Summable (fun rho : NontrivialZetaZero ↦
      if 0 < (zetaSpectralCoordinate rho.1).im then
        zetaSuzukiSpectralPSummand t Complex.I rho
      else 0) := by
  have hsum :=
    (summable_zetaSuzukiSpectralPAtISummand t).indicator
      {rho : NontrivialZetaZero |
        0 < (zetaSpectralCoordinate rho.1).im}
  refine hsum.congr ?_
  intro rho
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [zetaSuzukiSpectralPSummand_at_I]

/-- The lower restriction of the safe-point spectral series is absolutely
summable. -/
theorem summable_zetaSuzukiLowerRestrictedSpectralPSummand_at_I
    (t : ℝ) :
    Summable (fun rho : NontrivialZetaZero ↦
      if (zetaSpectralCoordinate rho.1).im < 0 then
        zetaSuzukiSpectralPSummand t Complex.I rho
      else 0) := by
  have hsum :=
    (summable_zetaSuzukiSpectralPAtISummand t).indicator
      {rho : NontrivialZetaZero |
        (zetaSpectralCoordinate rho.1).im < 0}
  refine hsum.congr ?_
  intro rho
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [zetaSuzukiSpectralPSummand_at_I]

/-- The complete upper-restricted safe-point Suzuki spectral value. -/
def riemannXiSuzukiUpperRestrictedSpectralPAtI (t : ℝ) : ℂ :=
  ∑' rho : NontrivialZetaZero,
    if 0 < (zetaSpectralCoordinate rho.1).im then
      zetaSuzukiSpectralPSummand t Complex.I rho
    else 0

/-- The complete lower-restricted safe-point Suzuki spectral value. -/
def riemannXiSuzukiLowerRestrictedSpectralPAtI (t : ℝ) : ℂ :=
  ∑' rho : NontrivialZetaZero,
    if (zetaSpectralCoordinate rho.1).im < 0 then
      zetaSuzukiSpectralPSummand t Complex.I rho
    else 0

/-- Upper-restricted symmetric zero windows converge unconditionally at the
safe point `i`. -/
theorem tendsto_suzukiXiUpperRestrictedSpectralPWindow_at_I
    (t : ℝ) :
    Tendsto (fun T : ℝ ↦
      suzukiXiUpperRestrictedSpectralPWindow t T Complex.I) atTop
      (nhds (riemannXiSuzukiUpperRestrictedSpectralPAtI t)) := by
  unfold suzukiXiUpperRestrictedSpectralPWindow
    riemannXiSuzukiUpperRestrictedSpectralPAtI
  exact
    (summable_zetaSuzukiUpperRestrictedSpectralPSummand_at_I t).hasSum.comp
      tendsto_spectralZetaZeroWindow_atTop

/-- Lower-restricted symmetric zero windows converge unconditionally at the
safe point `i`. -/
theorem tendsto_suzukiXiLowerRestrictedSpectralPWindow_at_I
    (t : ℝ) :
    Tendsto (fun T : ℝ ↦
      suzukiXiLowerRestrictedSpectralPWindow t T Complex.I) atTop
      (nhds (riemannXiSuzukiLowerRestrictedSpectralPAtI t)) := by
  unfold suzukiXiLowerRestrictedSpectralPWindow
    riemannXiSuzukiLowerRestrictedSpectralPAtI
  exact
    (summable_zetaSuzukiLowerRestrictedSpectralPSummand_at_I t).hasSum.comp
      tendsto_spectralZetaZeroWindow_atTop

/-- The universal Cayley time-trace scale is nonzero. -/
theorem suzukiXiCarrierCayleyTimeTraceScale_ne_zero :
    suzukiXiCarrierCayleyTimeTraceScale ≠ 0 := by
  unfold suzukiXiCarrierCayleyTimeTraceScale
  apply div_ne_zero
  · exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  · exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'

/-- Convergence of the upper unregularized screw trace implies convergence
of the upper Cayley time trace, with the safe correction displayed in the
limit. -/
theorem tendsto_suzukiXiCarrierCayleyUpperTimeTraceWindow_of_screwTrace
    (t : ℝ) {L : ℂ}
    (htrace : Tendsto (suzukiXiUpperScrewTraceWindow t) atTop
      (nhds L)) :
    Tendsto (suzukiXiCarrierCayleyUpperTimeTraceWindow t) atTop
      (nhds (suzukiXiCarrierCayleyTimeTraceScale *
        (L + 2 * Complex.I *
          riemannXiSuzukiLowerRestrictedSpectralPAtI (-t)))) := by
  have hsafe :=
    tendsto_suzukiXiLowerRestrictedSpectralPWindow_at_I (-t)
  refine
    (tendsto_const_nhds.mul
      (htrace.add (tendsto_const_nhds.mul hsafe))).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact
    (suzukiXiCarrierCayleyUpperTimeTraceWindow_eq_screwTrace_add_safeP
      t hT).symm

/-- Convergence of the lower Cayley time trace forces convergence of the
time-reversed upper unregularized screw trace. -/
theorem tendsto_suzukiXiUpperScrewTraceWindow_of_lowerTimeTrace
    (t : ℝ) {L : ℂ}
    (htrace : Tendsto
      (suzukiXiCarrierCayleyLowerTimeTraceWindow t) atTop (nhds L)) :
    Tendsto (suzukiXiUpperScrewTraceWindow (-t)) atTop
      (nhds (-(L / suzukiXiCarrierCayleyTimeTraceScale) +
        2 * Complex.I *
          riemannXiSuzukiUpperRestrictedSpectralPAtI (-t))) := by
  have hsafe :=
    tendsto_suzukiXiUpperRestrictedSpectralPWindow_at_I (-t)
  refine
    ((htrace.div_const suzukiXiCarrierCayleyTimeTraceScale).neg.add
      (tendsto_const_nhds.mul hsafe)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [suzukiXiCarrierCayleyLowerTimeTraceWindow_eq_upperScrewTrace_add_safeP
    t hT]
  field_simp [suzukiXiCarrierCayleyTimeTraceScale_ne_zero]
  ring

/-- Convergence of the lower unregularized screw trace implies convergence
of the lower Cayley time trace, with its safe correction displayed in the
limit. -/
theorem tendsto_suzukiXiCarrierCayleyLowerTimeTraceWindow_of_screwTrace
    (t : ℝ) {L : ℂ}
    (htrace : Tendsto (suzukiXiLowerScrewTraceWindow t) atTop
      (nhds L)) :
    Tendsto (suzukiXiCarrierCayleyLowerTimeTraceWindow t) atTop
      (nhds (suzukiXiCarrierCayleyTimeTraceScale *
        (L + 2 * Complex.I *
          riemannXiSuzukiUpperRestrictedSpectralPAtI (-t)))) := by
  have hsafe :=
    tendsto_suzukiXiUpperRestrictedSpectralPWindow_at_I (-t)
  refine
    (tendsto_const_nhds.mul
      (htrace.add (tendsto_const_nhds.mul hsafe))).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [suzukiXiCarrierCayleyLowerTimeTraceWindow_eq_screwTrace_add_negI,
    suzukiXiLowerRestrictedSpectralPWindow_negI_eq_upper_atI t hT]

/-- Convergence of the upper Cayley time trace forces convergence of the
upper unregularized screw trace. -/
theorem tendsto_suzukiXiUpperScrewTraceWindow_of_upperTimeTrace
    (t : ℝ) {L : ℂ}
    (htrace : Tendsto
      (suzukiXiCarrierCayleyUpperTimeTraceWindow t) atTop (nhds L)) :
    Tendsto (suzukiXiUpperScrewTraceWindow t) atTop
      (nhds (L / suzukiXiCarrierCayleyTimeTraceScale -
        2 * Complex.I *
          riemannXiSuzukiLowerRestrictedSpectralPAtI (-t))) := by
  have hsafe :=
    tendsto_suzukiXiLowerRestrictedSpectralPWindow_at_I (-t)
  refine
    ((htrace.div_const suzukiXiCarrierCayleyTimeTraceScale).sub
      (tendsto_const_nhds.mul hsafe)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [suzukiXiCarrierCayleyUpperTimeTraceWindow_eq_screwTrace_add_safeP
    t hT]
  field_simp [suzukiXiCarrierCayleyTimeTraceScale_ne_zero]
  ring

/-- At every fixed screw time, the upper finite Cayley trace converges if and
only if the upper unregularized half-divisor screw trace converges. -/
theorem exists_tendsto_suzukiXiCarrierCayleyUpperTimeTraceWindow_iff_screwTrace
    (t : ℝ) :
    (∃ L : ℂ, Tendsto
        (suzukiXiCarrierCayleyUpperTimeTraceWindow t) atTop (nhds L)) ↔
      ∃ L : ℂ, Tendsto
        (suzukiXiUpperScrewTraceWindow t) atTop (nhds L) := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨_, tendsto_suzukiXiUpperScrewTraceWindow_of_upperTimeTrace t hL⟩
  · rintro ⟨L, hL⟩
    exact
      ⟨_, tendsto_suzukiXiCarrierCayleyUpperTimeTraceWindow_of_screwTrace
        t hL⟩

/-- At every fixed screw time, the lower finite Cayley trace converges if and
only if the lower unregularized half-divisor screw trace converges. -/
theorem exists_tendsto_suzukiXiCarrierCayleyLowerTimeTraceWindow_iff_screwTrace
    (t : ℝ) :
    (∃ L : ℂ, Tendsto
        (suzukiXiCarrierCayleyLowerTimeTraceWindow t) atTop (nhds L)) ↔
      ∃ L : ℂ, Tendsto
        (suzukiXiLowerScrewTraceWindow t) atTop (nhds L) := by
  constructor
  · rintro ⟨L, hL⟩
    have hUpper :=
      tendsto_suzukiXiUpperScrewTraceWindow_of_lowerTimeTrace t hL
    refine ⟨-(-(L / suzukiXiCarrierCayleyTimeTraceScale) +
      2 * Complex.I *
        riemannXiSuzukiUpperRestrictedSpectralPAtI (-t)), ?_⟩
    refine hUpper.neg.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact (suzukiXiLowerScrewTraceWindow_eq_neg_upper t hT).symm
  · rintro ⟨L, hL⟩
    exact
      ⟨_, tendsto_suzukiXiCarrierCayleyLowerTimeTraceWindow_of_screwTrace
        t hL⟩

end

end RiemannGaussian

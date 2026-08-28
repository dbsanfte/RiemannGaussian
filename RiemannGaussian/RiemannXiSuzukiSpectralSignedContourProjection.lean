import RiemannGaussian.RiemannXiSuzukiSpectralUpperContourProjection

/-!
# Signed upper-minus-lower Suzuki contour projection

The positive bottom height constructed for the upper spectral rectangle also
separates the reflected lower poles: critical-line conjugation sends a lower
pole of height `-h` to an upper pole of height `h` in the same symmetric
window.  This file uses that fact to construct the lower rectangle
`[-T,T] x [-1,-eta]` and proves the exact analogue of the upper contour
formula.

Subtracting the two oriented rectangle integrals produces a function defined
solely from Suzuki's actual transformed spectral-xi logarithmic derivative.
Lean proves that it is exactly `-2*pi` times the established signed off-axis
spectral response.  Its actual derivative at screw time zero is therefore
`-2*pi*(-i)` times the finite Blaschke logarithmic derivative.  Thus the
finite signed RH detector is now an exact contour projection of the full
transformed xi function, not an externally supplied upper/lower divisor
split.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-! ## The same positive height separates the lower poles -/

/-- If `eta` lies below every upper pole in a symmetric window, every lower
pole in that window lies strictly below `-eta`. -/
theorem zetaSpectralCoordinate_im_lt_neg_of_upperContourBottomAdmissible
    {T eta : ℝ} (hT : 0 ≤ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta)
    (rho : NontrivialZetaZero)
    (hrho : rho ∈ spectralZetaZeroWindow T)
    (hlower : (zetaSpectralCoordinate rho.1).im < 0) :
    (zetaSpectralCoordinate rho.1).im < -eta := by
  let sigma := NontrivialZetaZero.conjugatePartner rho
  have hsigmaMem : sigma ∈ spectralZetaZeroWindow T :=
    (conjugatePartner_mem_spectralZetaZeroWindow_iff hT rho).2 hrho
  have hsigmaCoord :
      zetaSpectralCoordinate sigma.1 =
        starRingEnd ℂ (zetaSpectralCoordinate rho.1) := by
    exact NontrivialZetaZero.spectralCoordinate_conjugatePartner rho
  have hsigmaUpper : 0 < (zetaSpectralCoordinate sigma.1).im := by
    rw [hsigmaCoord, Complex.conj_im]
    exact neg_pos.mpr hlower
  have hsep := heta.2.2 sigma hsigmaMem hsigmaUpper
  rw [hsigmaCoord, Complex.conj_im] at hsep
  linarith

/-- The reflected horizontal line `Im w = -eta` does not meet any selected
spectral zero. -/
theorem suzukiXiLowerContourTop_not_mem_spectralXiZeroWindow
    {T eta : ℝ} (hT : 0 ≤ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta)
    (x : ℝ) :
    ((x : ℂ) + ((-eta : ℝ) : ℂ) * Complex.I) ∉
      spectralXiZeroWindow T := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨rho, hrho, heq⟩
  have hlower : (zetaSpectralCoordinate rho.1).im < 0 := by
    rw [heq]
    simp
    exact heta.1
  have hlt :=
    zetaSpectralCoordinate_im_lt_neg_of_upperContourBottomAdmissible
      hT heta rho hrho hlower
  rw [heq] at hlt
  simp at hlt

/-! ## The lower rectangle selects exactly the lower principal parts -/

/-- One selected Suzuki principal part contributes its residue exactly when
its pole lies below the real spectral axis. -/
theorem rectangularBoundaryIntegral_suzukiXiWeilSpectralPrincipalPart_lower
    (t : ℝ) (z : ℂ) {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta)
    (rho : NontrivialZetaZero)
    (hrho : rho ∈ spectralZetaZeroWindow T) :
    rectangularBoundaryIntegral (-T) T (-1) (-eta)
        (suzukiXiWeilSpectralPrincipalPart t z rho) =
      if (zetaSpectralCoordinate rho.1).im < 0 then
        (2 * Real.pi : ℝ) * Complex.I *
          suzukiXiWeilSpectralResidue t z rho
      else 0 := by
  let a : ℂ := zetaSpectralCoordinate rho.1
  have hreLe : |a.re| ≤ T :=
    (mem_spectralZetaZeroWindow hT rho).mp hrho
  have hreLt : |a.re| < T :=
    lt_of_le_of_ne hreLe (hboundary rho)
  have hre : -T < a.re ∧ a.re < T := abs_lt.mp hreLt
  have himHalf : |a.im| < (1 / 2 : ℝ) :=
    NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  change rectangularBoundaryIntegral (-T) T (-1) (-eta)
      (simplePoleKernel (suzukiXiWeilSpectralResidue t z rho) a) = _
  by_cases hlower : a.im < 0
  · rw [if_pos hlower]
    apply rectangularBoundaryIntegral_simplePoleKernel_of_mem
      (suzukiXiWeilSpectralResidue t z rho) a hre.1 hre.2
    · have hnegAbs : -|a.im| ≤ a.im := neg_abs_le _
      linarith
    · exact
        zetaSpectralCoordinate_im_lt_neg_of_upperContourBottomAdmissible
          hT heta rho hrho hlower
  · rw [if_neg hlower]
    apply rectangularBoundaryIntegral_simplePoleKernel_eq_zero_of_below
      (suzukiXiWeilSpectralResidue t z rho) a
    · linarith [heta.2.1]
    · have himNonneg : 0 ≤ a.im := le_of_not_gt hlower
      linarith [heta.1]

/-- A selected lower principal part is integrable on all four sides of the
reflected rectangle. -/
theorem rectangularBoundaryIntegrable_suzukiXiWeilSpectralPrincipalPart_lower
    (t : ℝ) (z : ℂ) {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta)
    (rho : NontrivialZetaZero)
    (hrho : rho ∈ spectralZetaZeroWindow T) :
    rectangularBoundaryIntegrable (-T) T (-1) (-eta)
      (suzukiXiWeilSpectralPrincipalPart t z rho) := by
  have hanalytic {w : ℂ} (hw : w ∉ spectralXiZeroWindow T) :
      AnalyticAt ℂ (suzukiXiWeilSpectralPrincipalPart t z rho) w := by
    apply analyticAt_suzukiXiWeilSpectralPrincipalPart_of_ne
    intro heq
    apply hw
    exact Finset.mem_image.mpr ⟨rho, hrho, heq.symm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralPrincipalPart t z rho)
      (fun x : ℝ ↦
        (x : ℂ) + (((-1 : ℝ) : ℂ)) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro x
    apply hanalytic
    simpa [sub_eq_add_neg] using
      lower_safeLine_not_mem_spectralXiZeroWindow T x
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralPrincipalPart t z rho)
      (fun x : ℝ ↦
        (x : ℂ) + ((-eta : ℝ) : ℂ) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro x
    exact hanalytic
      (suzukiXiLowerContourTop_not_mem_spectralXiZeroWindow hT heta x)
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralPrincipalPart t z rho)
      (fun y : ℝ ↦ (T : ℂ) + (y : ℂ) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro y
    exact hanalytic
      (right_vertical_not_mem_spectralXiZeroWindow hT hboundary y)
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralPrincipalPart t z rho)
      (fun y : ℝ ↦ (((-T : ℝ) : ℂ)) + (y : ℂ) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro y
    apply hanalytic
    simpa using
      (left_vertical_not_mem_spectralXiZeroWindow hT hboundary y)

/-- The complete finite principal sum is integrable on the reflected lower
rectangle. -/
theorem rectangularBoundaryIntegrable_suzukiXiWeilWindowPrincipalSum_lower
    (t : ℝ) (z : ℂ) {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegrable (-T) T (-1) (-eta)
      (suzukiXiWeilWindowPrincipalSum t z T) := by
  unfold suzukiXiWeilWindowPrincipalSum
  apply rectangularBoundaryIntegrable_finsetSum
  intro rho hrho
  exact
    rectangularBoundaryIntegrable_suzukiXiWeilSpectralPrincipalPart_lower
      t z hT hboundary heta rho hrho

/-- The lower rectangle integral of the principal sum is the sum of precisely
the true lower-pole residues. -/
theorem rectangularBoundaryIntegral_suzukiXiWeilWindowPrincipalSum_lower_residues
    (t : ℝ) (z : ℂ) {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegral (-T) T (-1) (-eta)
        (suzukiXiWeilWindowPrincipalSum t z T) =
      ∑ rho ∈ spectralZetaZeroWindow T,
        if (zetaSpectralCoordinate rho.1).im < 0 then
          (2 * Real.pi : ℝ) * Complex.I *
            suzukiXiWeilSpectralResidue t z rho
        else 0 := by
  unfold suzukiXiWeilWindowPrincipalSum
  rw [rectangularBoundaryIntegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro rho hrho
    exact
      rectangularBoundaryIntegral_suzukiXiWeilSpectralPrincipalPart_lower
        t z hT hboundary heta rho hrho
  · intro rho hrho
    exact
      rectangularBoundaryIntegrable_suzukiXiWeilSpectralPrincipalPart_lower
        t z hT hboundary heta rho hrho

/-- The reflected lower rectangle integral is exactly `-2*pi` times the lower
restricted Suzuki window. -/
theorem rectangularBoundaryIntegral_suzukiXiWeilWindowPrincipalSum_lower
    (t : ℝ) (z : ℂ) {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegral (-T) T (-1) (-eta)
        (suzukiXiWeilWindowPrincipalSum t z T) =
      -(((2 * Real.pi : ℝ) : ℂ)) *
        suzukiXiLowerRestrictedSpectralPWindow t T z := by
  rw [
    rectangularBoundaryIntegral_suzukiXiWeilWindowPrincipalSum_lower_residues
      t z hT hboundary heta]
  unfold suzukiXiLowerRestrictedSpectralPWindow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _hrho
  by_cases hlower : (zetaSpectralCoordinate rho.1).im < 0
  · simp only [if_pos hlower]
    rw [two_pi_I_mul_suzukiXiWeilSpectralResidue]
    unfold zetaSuzukiSpectralPSummand
      suzukiXiUpperEvaluationDenominator
    push_cast
    ring
  · simp only [if_neg hlower, mul_zero]

/-! ## The actual transformed logarithmic derivative -/

/-- The actual Suzuki-weighted xi logarithmic derivative is integrable on
the four zero-free sides of the reflected lower rectangle. -/
theorem rectangularBoundaryIntegrable_suzukiXiWeilSpectralIntegrand_lower
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegrable (-T) T (-1) (-eta)
      (suzukiXiWeilSpectralIntegrand t z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralIntegrand t z)
      (fun x : ℝ ↦
        (x : ℂ) + (((-1 : ℝ) : ℂ)) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro x
    apply analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
    · intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith
    · apply riemannXiSpectral_ne_zero_of_half_le_abs_im
      norm_num
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    apply ContinuousAt.continuousWithinAt
    have hanalytic : AnalyticAt ℂ
        (suzukiXiWeilSpectralIntegrand t z)
        ((x : ℂ) + ((-eta : ℝ) : ℂ) * Complex.I) := by
      apply analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
      · intro heq
        have him := congrArg Complex.im heq
        simp at him
        linarith [heta.1]
      · intro hzero
        apply suzukiXiLowerContourTop_not_mem_spectralXiZeroWindow
          hT heta x
        apply (mem_spectralXiZeroWindow_iff hT _).mpr
        refine ⟨hzero, ?_⟩
        have hxabs : |x| ≤ T := (abs_le).2 hx
        simpa using hxabs
    have hpath : ContinuousAt
        (fun u : ℝ ↦
          (u : ℂ) + ((-eta : ℝ) : ℂ) * Complex.I) x := by
      fun_prop
    have hcomp : ContinuousAt
        (suzukiXiWeilSpectralIntegrand t z ∘
          fun u : ℝ ↦
            (u : ℂ) + ((-eta : ℝ) : ℂ) * Complex.I) x :=
      ContinuousAt.comp_of_eq hanalytic.continuousAt hpath rfl
    exact hcomp.congr (Eventually.of_forall fun _ ↦ rfl)
  · apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le (by linarith [heta.2.1])] at hy
    apply ContinuousAt.continuousWithinAt
    have hanalytic : AnalyticAt ℂ
        (suzukiXiWeilSpectralIntegrand t z)
        ((T : ℂ) + (y : ℂ) * Complex.I) := by
      apply analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
      · intro heq
        have him := congrArg Complex.im heq
        simp at him
        linarith [hy.2, heta.1]
      · apply riemannXiSpectral_ne_zero_of_abs_re_ne hboundary
        simp [abs_of_nonneg hT]
    have hpath : ContinuousAt
        (fun u : ℝ ↦ (T : ℂ) + (u : ℂ) * Complex.I) y := by
      fun_prop
    have hcomp : ContinuousAt
        (suzukiXiWeilSpectralIntegrand t z ∘
          fun u : ℝ ↦ (T : ℂ) + (u : ℂ) * Complex.I) y :=
      ContinuousAt.comp_of_eq hanalytic.continuousAt hpath rfl
    exact hcomp.congr (Eventually.of_forall fun _ ↦ rfl)
  · apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le (by linarith [heta.2.1])] at hy
    apply ContinuousAt.continuousWithinAt
    have hanalytic : AnalyticAt ℂ
        (suzukiXiWeilSpectralIntegrand t z)
        (((-T : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
      apply analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
      · intro heq
        have him := congrArg Complex.im heq
        simp at him
        linarith [hy.2, heta.1]
      · apply riemannXiSpectral_ne_zero_of_abs_re_ne hboundary
        simp [abs_of_nonneg hT]
    have hpath : ContinuousAt
        (fun u : ℝ ↦ (((-T : ℝ) : ℂ)) +
          (u : ℂ) * Complex.I) y := by
      fun_prop
    have hcomp : ContinuousAt
        (suzukiXiWeilSpectralIntegrand t z ∘
          fun u : ℝ ↦ (((-T : ℝ) : ℂ)) +
            (u : ℂ) * Complex.I) y :=
      ContinuousAt.comp_of_eq hanalytic.continuousAt hpath rfl
    exact hcomp.congr (Eventually.of_forall fun _ ↦ rfl)

/-- Cauchy's theorem for the same holomorphic finite-window regularization on
the reflected lower subrectangle. -/
theorem suzukiXiWeilWindowRawRemainder_lower_rectangle_identity
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegral (-T) T (-1) (-eta)
      (suzukiXiWeilWindowRawRemainder t z T) = 0 := by
  obtain ⟨F, hFanalytic, hFoff⟩ :=
    exists_suzukiXiWeilWindowRegularization t hz hT
  have hdiff : DifferentiableOn ℂ F
      (Complex.Rectangle
        (((-T : ℝ) : ℂ) + (((-1 : ℝ) : ℂ)) * Complex.I)
        ((T : ℂ) + ((-eta : ℝ) : ℂ) * Complex.I)) := by
    intro w hw
    apply (hFanalytic w ?_).differentiableAt.differentiableWithinAt
    constructor
    · have hre : w.re ∈ uIcc (-T) T := by
        simpa using hw.1
      rw [uIcc_of_le (by linarith)] at hre
      exact (abs_le).2 hre
    · have him : w.im ∈ uIcc (-1) (-eta) := by
        simpa using hw.2
      rw [uIcc_of_le (by linarith [heta.2.1])] at him
      rw [abs_le]
      constructor
      · exact him.1
      · linarith [heta.1, him.2]
  have hrectF :
      rectangularBoundaryIntegral (-T) T (-1) (-eta) F = 0 :=
    rectangularBoundaryIntegral_eq_zero_of_differentiableOn
      (-T) T (-1) (-eta) F hdiff
  have hbottom (x : ℝ) :
      F ((x : ℂ) + (((-1 : ℝ) : ℂ)) * Complex.I) =
        suzukiXiWeilWindowRawRemainder t z T
          ((x : ℂ) + (((-1 : ℝ) : ℂ)) * Complex.I) := by
    apply hFoff
    simpa [sub_eq_add_neg] using
      lower_safeLine_not_mem_spectralXiZeroWindow T x
  have htop (x : ℝ) :
      F ((x : ℂ) + ((-eta : ℝ) : ℂ) * Complex.I) =
        suzukiXiWeilWindowRawRemainder t z T
          ((x : ℂ) + ((-eta : ℝ) : ℂ) * Complex.I) :=
    hFoff _
      (suzukiXiLowerContourTop_not_mem_spectralXiZeroWindow hT heta x)
  have hright (y : ℝ) :
      F ((T : ℂ) + (y : ℂ) * Complex.I) =
        suzukiXiWeilWindowRawRemainder t z T
          ((T : ℂ) + (y : ℂ) * Complex.I) :=
    hFoff _
      (right_vertical_not_mem_spectralXiZeroWindow hT hboundary y)
  have hleft (y : ℝ) :
      F (((-T : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
        suzukiXiWeilWindowRawRemainder t z T
          (((-T : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    apply hFoff
    simpa using
      (left_vertical_not_mem_spectralXiZeroWindow hT hboundary y)
  unfold rectangularBoundaryIntegral at hrectF ⊢
  simp_rw [hbottom, htop, hright, hleft] at hrectF
  exact hrectF

/-- On the reflected lower rectangle, the actual transformed logarithmic
derivative has the same integral as the finite principal sum. -/
theorem suzukiXiWeilSpectralIntegrand_lower_rectangle_eq_windowPrincipalSum
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegral (-T) T (-1) (-eta)
        (suzukiXiWeilSpectralIntegrand t z) =
      rectangularBoundaryIntegral (-T) T (-1) (-eta)
        (suzukiXiWeilWindowPrincipalSum t z T) := by
  have hraw := suzukiXiWeilWindowRawRemainder_lower_rectangle_identity
    t hz hT hboundary heta
  have hintegrand :=
    rectangularBoundaryIntegrable_suzukiXiWeilSpectralIntegrand_lower
      t hz hT hboundary heta
  have hprincipal :=
    rectangularBoundaryIntegrable_suzukiXiWeilWindowPrincipalSum_lower
      t z hT hboundary heta
  have hsub := rectangularBoundaryIntegral_sub (-T) T (-1) (-eta)
    hintegrand hprincipal
  change rectangularBoundaryIntegral (-T) T (-1) (-eta)
      (fun w ↦ suzukiXiWeilSpectralIntegrand t z w -
        suzukiXiWeilWindowPrincipalSum t z T w) = 0 at hraw
  rw [hsub] at hraw
  exact sub_eq_zero.mp hraw

/-- Exact finite lower-contour projection theorem. -/
theorem suzukiXiWeilSpectralIntegrand_lower_rectangle_eq_lowerRestrictedPWindow
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegral (-T) T (-1) (-eta)
        (suzukiXiWeilSpectralIntegrand t z) =
      -(((2 * Real.pi : ℝ) : ℂ)) *
        suzukiXiLowerRestrictedSpectralPWindow t T z := by
  rw [
    suzukiXiWeilSpectralIntegrand_lower_rectangle_eq_windowPrincipalSum
      t hz hT hboundary heta,
    rectangularBoundaryIntegral_suzukiXiWeilWindowPrincipalSum_lower
      t z hT hboundary heta]

/-! ## The signed contour response and its initial velocity -/

/-- The oriented upper-rectangle integral minus the lower-rectangle integral
of the actual transformed spectral-xi logarithmic derivative. -/
def suzukiXiWeilSignedContourResponseWindow
    (t T eta : ℝ) (z : ℂ) : ℂ :=
  rectangularBoundaryIntegral (-T) T eta 1
      (suzukiXiWeilSpectralIntegrand t z) -
    rectangularBoundaryIntegral (-T) T (-1) (-eta)
      (suzukiXiWeilSpectralIntegrand t z)

/-- The signed contour response is exactly `-2*pi` times the established
signed upper-minus-lower spectral response. -/
theorem suzukiXiWeilSignedContourResponseWindow_eq_spectralResponse
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    suzukiXiWeilSignedContourResponseWindow t T eta z =
      -(((2 * Real.pi : ℝ) : ℂ)) *
        suzukiXiOffAxisSignedSpectralPResponseWindow t T z := by
  unfold suzukiXiWeilSignedContourResponseWindow
    suzukiXiOffAxisSignedSpectralPResponseWindow
  rw [
    suzukiXiWeilSpectralIntegrand_upper_rectangle_eq_upperRestrictedPWindow
      t hz hT hboundary heta,
    suzukiXiWeilSpectralIntegrand_lower_rectangle_eq_lowerRestrictedPWindow
      t hz hT hboundary heta]
  ring

/-- The signed contour response has the exact finite spectral time derivative
at every screw time. -/
theorem hasDerivAt_suzukiXiWeilSignedContourResponseWindow_time
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    HasDerivAt
      (fun u : ℝ ↦ suzukiXiWeilSignedContourResponseWindow u T eta z)
      (-(((2 * Real.pi : ℝ) : ℂ)) *
        suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow t T z) t := by
  have heq :
      (fun u : ℝ ↦ suzukiXiWeilSignedContourResponseWindow u T eta z) =
        fun u : ℝ ↦ -(((2 * Real.pi : ℝ) : ℂ)) *
          suzukiXiOffAxisSignedSpectralPResponseWindow u T z := by
    funext u
    exact suzukiXiWeilSignedContourResponseWindow_eq_spectralResponse
      u hz hT hboundary heta
  rw [heq]
  exact
    (hasDerivAt_suzukiXiOffAxisSignedSpectralPResponseWindow_time t T z).const_mul
      (-(((2 * Real.pi : ℝ) : ℂ)))

/-- At screw time zero, the signed contour response differentiates to
`-2*pi*(-i)` times the finite Blaschke logarithmic derivative. -/
theorem hasDerivAt_suzukiXiWeilSignedContourResponseWindow_zero_time
    {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    HasDerivAt
      (fun u : ℝ ↦ suzukiXiWeilSignedContourResponseWindow u T eta z)
      (-(((2 * Real.pi : ℝ) : ℂ)) *
        (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow z T)) 0 := by
  simpa only [
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time hT]
    using
      (hasDerivAt_suzukiXiWeilSignedContourResponseWindow_time
        0 hz hT hboundary heta)

/-- The actual time derivative at zero of the signed contour response. -/
def suzukiXiWeilSignedContourInitialVelocityWindow
    (T eta : ℝ) (z : ℂ) : ℂ :=
  deriv (fun u : ℝ ↦
    suzukiXiWeilSignedContourResponseWindow u T eta z) 0

/-- The actual initial derivative of the signed contour response is the
finite Blaschke logarithmic derivative with the exact contour factor. -/
theorem suzukiXiWeilSignedContourInitialVelocityWindow_eq_blaschke
    {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    suzukiXiWeilSignedContourInitialVelocityWindow T eta z =
      -(((2 * Real.pi : ℝ) : ℂ)) *
        (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow z T) :=
  (hasDerivAt_suzukiXiWeilSignedContourResponseWindow_zero_time
    hz hT hboundary heta).deriv

end

end RiemannGaussian

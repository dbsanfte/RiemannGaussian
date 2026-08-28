import RiemannGaussian.RiemannXiSuzukiSpectralHardyProjection
import RiemannGaussian.RiemannXiSuzukiWeilGlobal

/-!
# Upper-rectangle projection of Suzuki's spectral divisor

This file globalizes the finite local-circle projection.  Given a finite
genuine-zero window, choose a horizontal line of positive height below every
upper pole in that window.  The rectangle with that bottom edge, top edge
`Im w = 1`, and vertical edges `Re w = ±T` then encloses exactly the upper
off-axis poles.

Lean proves that the boundary integral of Suzuki's *actual transformed
spectral-xi logarithmic derivative* over this rectangle is exactly `-2*pi`
times the upper restricted finite `P_t` window.  The top edge lies in the
arithmetic safe half-plane.  This is the first exact contour interface for
recovering the RH-detecting signed response from the full arithmetic Suzuki
function; estimates and limiting deformation of the other three sides remain
open.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-! ## Generic rectangular linearity -/

/-- Interval integrability on all four parametrized sides of an arbitrary
axis-parallel rectangle. -/
def rectangularBoundaryIntegrable
    (l r b u : ℝ) (f : ℂ → ℂ) : Prop :=
  IntervalIntegrable
      (fun x : ℝ ↦ f ((x : ℂ) + (b : ℂ) * Complex.I)) volume l r ∧
    IntervalIntegrable
      (fun x : ℝ ↦ f ((x : ℂ) + (u : ℂ) * Complex.I)) volume l r ∧
    IntervalIntegrable
      (fun y : ℝ ↦ f ((r : ℂ) + (y : ℂ) * Complex.I)) volume b u ∧
    IntervalIntegrable
      (fun y : ℝ ↦ f ((l : ℂ) + (y : ℂ) * Complex.I)) volume b u

/-- Linearity of an arbitrary rectangular boundary integral under
subtraction. -/
theorem rectangularBoundaryIntegral_sub
    (l r b u : ℝ) {f g : ℂ → ℂ}
    (hf : rectangularBoundaryIntegrable l r b u f)
    (hg : rectangularBoundaryIntegrable l r b u g) :
    rectangularBoundaryIntegral l r b u (fun z ↦ f z - g z) =
      rectangularBoundaryIntegral l r b u f -
        rectangularBoundaryIntegral l r b u g := by
  rcases hf with ⟨hfb, hfu, hfr, hfl⟩
  rcases hg with ⟨hgb, hgu, hgr, hgl⟩
  unfold rectangularBoundaryIntegral
  rw [intervalIntegral.integral_sub hfb hgb,
    intervalIntegral.integral_sub hfu hgu,
    intervalIntegral.integral_sub hfr hgr,
    intervalIntegral.integral_sub hfl hgl]
  ring

/-- An arbitrary rectangular boundary integral commutes with a finite sum
when every summand is integrable on all four sides. -/
theorem rectangularBoundaryIntegral_finsetSum
    {alpha : Type*} (l r b u : ℝ) (S : Finset alpha)
    (f : alpha → ℂ → ℂ)
    (hf : ∀ i ∈ S, rectangularBoundaryIntegrable l r b u (f i)) :
    rectangularBoundaryIntegral l r b u
        (fun z ↦ ∑ i ∈ S, f i z) =
      ∑ i ∈ S, rectangularBoundaryIntegral l r b u (f i) := by
  unfold rectangularBoundaryIntegral
  rw [intervalIntegral.integral_finsetSum
      (fun i hi ↦ (hf i hi).1),
    intervalIntegral.integral_finsetSum
      (fun i hi ↦ (hf i hi).2.1),
    intervalIntegral.integral_finsetSum
      (fun i hi ↦ (hf i hi).2.2.1),
    intervalIntegral.integral_finsetSum
      (fun i hi ↦ (hf i hi).2.2.2)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum]

/-- Finite sums preserve integrability on all four sides of an arbitrary
rectangle. -/
theorem rectangularBoundaryIntegrable_finsetSum
    {alpha : Type*} (l r b u : ℝ) (S : Finset alpha)
    (f : alpha → ℂ → ℂ)
    (hf : ∀ i ∈ S, rectangularBoundaryIntegrable l r b u (f i)) :
    rectangularBoundaryIntegrable l r b u
      (fun z ↦ ∑ i ∈ S, f i z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsum := IntervalIntegrable.sum S
        (fun i hi ↦ (hf i hi).1)
    have heq :
        (∑ i ∈ S, fun x : ℝ ↦
          f i ((x : ℂ) + (b : ℂ) * Complex.I)) =
          fun x : ℝ ↦ ∑ i ∈ S,
            f i ((x : ℂ) + (b : ℂ) * Complex.I) := by
      funext x
      simp
    rw [← heq]
    exact hsum
  · have hsum := IntervalIntegrable.sum S
        (fun i hi ↦ (hf i hi).2.1)
    have heq :
        (∑ i ∈ S, fun x : ℝ ↦
          f i ((x : ℂ) + (u : ℂ) * Complex.I)) =
          fun x : ℝ ↦ ∑ i ∈ S,
            f i ((x : ℂ) + (u : ℂ) * Complex.I) := by
      funext x
      simp
    rw [← heq]
    exact hsum
  · have hsum := IntervalIntegrable.sum S
        (fun i hi ↦ (hf i hi).2.2.1)
    have heq :
        (∑ i ∈ S, fun y : ℝ ↦
          f i ((r : ℂ) + (y : ℂ) * Complex.I)) =
          fun y : ℝ ↦ ∑ i ∈ S,
            f i ((r : ℂ) + (y : ℂ) * Complex.I) := by
      funext y
      simp
    rw [← heq]
    exact hsum
  · have hsum := IntervalIntegrable.sum S
        (fun i hi ↦ (hf i hi).2.2.2)
    have heq :
        (∑ i ∈ S, fun y : ℝ ↦
          f i ((l : ℂ) + (y : ℂ) * Complex.I)) =
          fun y : ℝ ↦ ∑ i ∈ S,
            f i ((l : ℂ) + (y : ℂ) * Complex.I) := by
      funext y
      simp
    rw [← heq]
    exact hsum

/-! ## A finite bottom line below every upper pole -/

/-- Admissibility of a positive bottom height for the upper spectral
rectangle. -/
def SuzukiXiUpperContourBottomAdmissible (T eta : ℝ) : Prop :=
  0 < eta ∧ eta < 1 ∧
    ∀ rho ∈ spectralZetaZeroWindow T,
      0 < (zetaSpectralCoordinate rho.1).im →
        eta < (zetaSpectralCoordinate rho.1).im

/-- Every finite genuine-zero window admits a positive bottom line strictly
below all of its upper poles. -/
theorem exists_suzukiXiUpperContourBottomAdmissible (T : ℝ) :
    ∃ eta : ℝ, SuzukiXiUpperContourBottomAdmissible T eta := by
  let upperWindow := (spectralZetaZeroWindow T).filter fun rho ↦
    0 < (zetaSpectralCoordinate rho.1).im
  let heights : Finset ℝ := upperWindow.image fun rho ↦
    (zetaSpectralCoordinate rho.1).im
  by_cases hempty : heights = ∅
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro rho hrho hupper
    have hrhoUpper : rho ∈ upperWindow := by
      simp only [upperWindow, Finset.mem_filter]
      exact ⟨hrho, hupper⟩
    have hheight : (zetaSpectralCoordinate rho.1).im ∈ heights := by
      exact Finset.mem_image.mpr ⟨rho, hrhoUpper, rfl⟩
    rw [hempty] at hheight
    simp at hheight
  · have hnonempty : heights.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    let m : ℝ := heights.min' hnonempty
    have hmMem : m ∈ heights := Finset.min'_mem heights hnonempty
    have hmPos : 0 < m := by
      rcases Finset.mem_image.mp hmMem with ⟨rho, hrho, hrhoHeight⟩
      have hupper := (Finset.mem_filter.mp hrho).2
      rw [← hrhoHeight]
      exact hupper
    refine ⟨m / 2, by linarith, ?_, ?_⟩
    · have hmHalf : m < 1 / 2 := by
        rcases Finset.mem_image.mp hmMem with ⟨rho, _hrho, hrhoHeight⟩
        have him := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
        have hle : (zetaSpectralCoordinate rho.1).im ≤
            |(zetaSpectralCoordinate rho.1).im| := le_abs_self _
        rw [← hrhoHeight]
        linarith
      linarith
    · intro rho hrho hupper
      have hrhoUpper : rho ∈ upperWindow := by
        simp only [upperWindow, Finset.mem_filter]
        exact ⟨hrho, hupper⟩
      have hheight : (zetaSpectralCoordinate rho.1).im ∈ heights :=
        Finset.mem_image.mpr ⟨rho, hrhoUpper, rfl⟩
      have hmLe : m ≤ (zetaSpectralCoordinate rho.1).im :=
        Finset.min'_le heights _ hheight
      linarith

/-- An admissible positive bottom line does not meet any selected spectral
zero, even away from the horizontal span of the rectangle. -/
theorem suzukiXiUpperContourBottom_not_mem_spectralXiZeroWindow
    {T eta : ℝ} (heta : SuzukiXiUpperContourBottomAdmissible T eta)
    (x : ℝ) :
    ((x : ℂ) + (eta : ℂ) * Complex.I) ∉ spectralXiZeroWindow T := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨rho, hrho, heq⟩
  have himEq := congrArg Complex.im heq
  have hupper : 0 < (zetaSpectralCoordinate rho.1).im := by
    rw [heq]
    simpa using heta.1
  have hlt := heta.2.2 rho hrho hupper
  rw [heq] at hlt
  simp at hlt

/-! ## The upper rectangle selects exactly the upper principal parts -/

/-- One selected Suzuki principal part contributes its full residue exactly
when its spectral pole lies in the upper half-plane; all other selected poles
lie strictly below the positive-bottom rectangle. -/
theorem rectangularBoundaryIntegral_suzukiXiWeilSpectralPrincipalPart_upper
    (t : ℝ) (z : ℂ) {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta)
    (rho : NontrivialZetaZero)
    (hrho : rho ∈ spectralZetaZeroWindow T) :
    rectangularBoundaryIntegral (-T) T eta 1
        (suzukiXiWeilSpectralPrincipalPart t z rho) =
      if 0 < (zetaSpectralCoordinate rho.1).im then
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
  change rectangularBoundaryIntegral (-T) T eta 1
      (simplePoleKernel (suzukiXiWeilSpectralResidue t z rho) a) = _
  by_cases hupper : 0 < a.im
  · rw [if_pos hupper]
    apply rectangularBoundaryIntegral_simplePoleKernel_of_mem
      (suzukiXiWeilSpectralResidue t z rho) a
      hre.1 hre.2 (heta.2.2 rho hrho hupper)
    have hle : a.im ≤ |a.im| := le_abs_self _
    linarith
  · rw [if_neg hupper]
    apply rectangularBoundaryIntegral_simplePoleKernel_eq_zero_of_above
      (suzukiXiWeilSpectralResidue t z rho) a heta.2.1.le
    have himNonpos : a.im ≤ 0 := le_of_not_gt hupper
    linarith [heta.1]

/-- A selected principal part is integrable on all four sides of the upper
rectangle. -/
theorem rectangularBoundaryIntegrable_suzukiXiWeilSpectralPrincipalPart_upper
    (t : ℝ) (z : ℂ) {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta)
    (rho : NontrivialZetaZero)
    (hrho : rho ∈ spectralZetaZeroWindow T) :
    rectangularBoundaryIntegrable (-T) T eta 1
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
      (fun x : ℝ ↦ (x : ℂ) + (eta : ℂ) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro x
    exact hanalytic
      (suzukiXiUpperContourBottom_not_mem_spectralXiZeroWindow heta x)
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralPrincipalPart t z rho)
      (fun x : ℝ ↦
        (x : ℂ) + (((1 : ℝ) : ℂ)) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro x
    apply hanalytic
    simpa using upper_safeLine_not_mem_spectralXiZeroWindow T x
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

/-- The complete finite principal sum is integrable on the upper rectangle. -/
theorem rectangularBoundaryIntegrable_suzukiXiWeilWindowPrincipalSum_upper
    (t : ℝ) (z : ℂ) {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegrable (-T) T eta 1
      (suzukiXiWeilWindowPrincipalSum t z T) := by
  unfold suzukiXiWeilWindowPrincipalSum
  apply rectangularBoundaryIntegrable_finsetSum
  intro rho hrho
  exact
    rectangularBoundaryIntegrable_suzukiXiWeilSpectralPrincipalPart_upper
      t z hT hboundary heta rho hrho

/-- The upper rectangle integral of the complete principal sum is the sum of
the true residues of precisely the upper poles. -/
theorem rectangularBoundaryIntegral_suzukiXiWeilWindowPrincipalSum_upper_residues
    (t : ℝ) (z : ℂ) {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegral (-T) T eta 1
        (suzukiXiWeilWindowPrincipalSum t z T) =
      ∑ rho ∈ spectralZetaZeroWindow T,
        if 0 < (zetaSpectralCoordinate rho.1).im then
          (2 * Real.pi : ℝ) * Complex.I *
            suzukiXiWeilSpectralResidue t z rho
        else 0 := by
  unfold suzukiXiWeilWindowPrincipalSum
  rw [rectangularBoundaryIntegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro rho hrho
    exact
      rectangularBoundaryIntegral_suzukiXiWeilSpectralPrincipalPart_upper
        t z hT hboundary heta rho hrho
  · intro rho hrho
    exact
      rectangularBoundaryIntegrable_suzukiXiWeilSpectralPrincipalPart_upper
        t z hT hboundary heta rho hrho

/-- The upper rectangle integral of the finite principal sum is exactly
`-2*pi` times the upper restricted Suzuki window. -/
theorem rectangularBoundaryIntegral_suzukiXiWeilWindowPrincipalSum_upper
    (t : ℝ) (z : ℂ) {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegral (-T) T eta 1
        (suzukiXiWeilWindowPrincipalSum t z T) =
      -(((2 * Real.pi : ℝ) : ℂ)) *
        suzukiXiUpperRestrictedSpectralPWindow t T z := by
  rw [
    rectangularBoundaryIntegral_suzukiXiWeilWindowPrincipalSum_upper_residues
      t z hT hboundary heta]
  unfold suzukiXiUpperRestrictedSpectralPWindow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _hrho
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · simp only [if_pos hupper]
    rw [two_pi_I_mul_suzukiXiWeilSpectralResidue]
    unfold zetaSuzukiSpectralPSummand
      suzukiXiUpperEvaluationDenominator
    push_cast
    ring
  · simp only [if_neg hupper, mul_zero]

/-! ## The actual transformed logarithmic derivative -/

/-- The actual Suzuki-weighted xi logarithmic derivative is integrable on
all four zero-free sides of the upper rectangle. -/
theorem rectangularBoundaryIntegrable_suzukiXiWeilSpectralIntegrand_upper
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegrable (-T) T eta 1
      (suzukiXiWeilSpectralIntegrand t z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    apply ContinuousAt.continuousWithinAt
    have hanalytic : AnalyticAt ℂ
        (suzukiXiWeilSpectralIntegrand t z)
        ((x : ℂ) + (eta : ℂ) * Complex.I) := by
      apply analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
      · intro heq
        have him := congrArg Complex.im heq
        simp at him
        linarith [heta.2.1]
      · intro hzero
        apply suzukiXiUpperContourBottom_not_mem_spectralXiZeroWindow heta x
        apply (mem_spectralXiZeroWindow_iff hT _).mpr
        refine ⟨hzero, ?_⟩
        have hxabs : |x| ≤ T := (abs_le).2 hx
        simpa using hxabs
    have hpath : ContinuousAt
        (fun u : ℝ ↦ (u : ℂ) + (eta : ℂ) * Complex.I) x := by
      fun_prop
    have hcomp : ContinuousAt
        (suzukiXiWeilSpectralIntegrand t z ∘
          fun u : ℝ ↦ (u : ℂ) + (eta : ℂ) * Complex.I) x :=
      ContinuousAt.comp_of_eq hanalytic.continuousAt hpath rfl
    exact hcomp.congr (Eventually.of_forall fun _ ↦ rfl)
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralIntegrand t z)
      (fun x : ℝ ↦
        (x : ℂ) + (((1 : ℝ) : ℂ)) * Complex.I)
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
    intro y hy
    rw [uIcc_of_le heta.2.1.le] at hy
    apply ContinuousAt.continuousWithinAt
    have hanalytic : AnalyticAt ℂ
        (suzukiXiWeilSpectralIntegrand t z)
        ((T : ℂ) + (y : ℂ) * Complex.I) := by
      apply analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
      · intro heq
        have him := congrArg Complex.im heq
        simp at him
        linarith [hy.2]
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
    rw [uIcc_of_le heta.2.1.le] at hy
    apply ContinuousAt.continuousWithinAt
    have hanalytic : AnalyticAt ℂ
        (suzukiXiWeilSpectralIntegrand t z)
        (((-T : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
      apply analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
      · intro heq
        have him := congrArg Complex.im heq
        simp at him
        linarith [hy.2]
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

/-- Cauchy's theorem for the holomorphic finite-window regularization on the
upper subrectangle. -/
theorem suzukiXiWeilWindowRawRemainder_upper_rectangle_identity
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegral (-T) T eta 1
      (suzukiXiWeilWindowRawRemainder t z T) = 0 := by
  obtain ⟨F, hFanalytic, hFoff⟩ :=
    exists_suzukiXiWeilWindowRegularization t hz hT
  have hdiff : DifferentiableOn ℂ F
      (Complex.Rectangle
        (((-T : ℝ) : ℂ) + (eta : ℂ) * Complex.I)
        ((T : ℂ) + (((1 : ℝ) : ℂ)) * Complex.I)) := by
    intro w hw
    apply (hFanalytic w ?_).differentiableAt.differentiableWithinAt
    constructor
    · have hre : w.re ∈ uIcc (-T) T := by
        simpa using hw.1
      rw [uIcc_of_le (by linarith)] at hre
      exact (abs_le).2 hre
    · have him : w.im ∈ uIcc eta 1 := by
        simpa using hw.2
      rw [uIcc_of_le heta.2.1.le] at him
      rw [abs_le]
      constructor
      · linarith [heta.1, him.1]
      · exact him.2
  have hrectF : rectangularBoundaryIntegral (-T) T eta 1 F = 0 :=
    rectangularBoundaryIntegral_eq_zero_of_differentiableOn
      (-T) T eta 1 F hdiff
  have hbottom (x : ℝ) :
      F ((x : ℂ) + (eta : ℂ) * Complex.I) =
        suzukiXiWeilWindowRawRemainder t z T
          ((x : ℂ) + (eta : ℂ) * Complex.I) :=
    hFoff _
      (suzukiXiUpperContourBottom_not_mem_spectralXiZeroWindow heta x)
  have htop (x : ℝ) :
      F ((x : ℂ) + (((1 : ℝ) : ℂ)) * Complex.I) =
        suzukiXiWeilWindowRawRemainder t z T
          ((x : ℂ) + (((1 : ℝ) : ℂ)) * Complex.I) := by
    apply hFoff
    simpa using upper_safeLine_not_mem_spectralXiZeroWindow T x
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

/-- On the upper rectangle, the actual transformed xi logarithmic derivative
has the same boundary integral as the selected finite principal sum. -/
theorem suzukiXiWeilSpectralIntegrand_upper_rectangle_eq_windowPrincipalSum
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegral (-T) T eta 1
        (suzukiXiWeilSpectralIntegrand t z) =
      rectangularBoundaryIntegral (-T) T eta 1
        (suzukiXiWeilWindowPrincipalSum t z T) := by
  have hraw := suzukiXiWeilWindowRawRemainder_upper_rectangle_identity
    t hz hT hboundary heta
  have hintegrand :=
    rectangularBoundaryIntegrable_suzukiXiWeilSpectralIntegrand_upper
      t hz hT hboundary heta
  have hprincipal :=
    rectangularBoundaryIntegrable_suzukiXiWeilWindowPrincipalSum_upper
      t z hT hboundary heta
  have hsub := rectangularBoundaryIntegral_sub (-T) T eta 1
    hintegrand hprincipal
  change rectangularBoundaryIntegral (-T) T eta 1
      (fun w ↦ suzukiXiWeilSpectralIntegrand t z w -
        suzukiXiWeilWindowPrincipalSum t z T w) = 0 at hraw
  rw [hsub] at hraw
  exact sub_eq_zero.mp hraw

/-- Exact finite upper-contour projection theorem.  The boundary integral of
the actual Suzuki-weighted spectral-xi logarithmic derivative, with safe top
edge `Im w = 1`, is `-2*pi` times precisely the upper restricted spectral
window. -/
theorem suzukiXiWeilSpectralIntegrand_upper_rectangle_eq_upperRestrictedPWindow
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    {T eta : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (heta : SuzukiXiUpperContourBottomAdmissible T eta) :
    rectangularBoundaryIntegral (-T) T eta 1
        (suzukiXiWeilSpectralIntegrand t z) =
      -(((2 * Real.pi : ℝ) : ℂ)) *
        suzukiXiUpperRestrictedSpectralPWindow t T z := by
  rw [
    suzukiXiWeilSpectralIntegrand_upper_rectangle_eq_windowPrincipalSum
      t hz hT hboundary heta,
    rectangularBoundaryIntegral_suzukiXiWeilWindowPrincipalSum_upper
      t z hT hboundary heta]

end

end RiemannGaussian

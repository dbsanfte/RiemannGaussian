import RiemannGaussian.PolynomialLogDerivativeCircle
import RiemannGaussian.RiemannXiSuzukiCarrierCayleyTimeResponseLogDefect

/-!
# Finite Hardy projection of Suzuki's spectral function

The arithmetic formula supplies the full Suzuki spectral function, whereas
the RH detector constructed in the preceding files is its upper-minus-lower
spectral part.  Functional-equation symmetry alone cannot recover that
signed part.  This file begins the required analytic separation at the exact
finite level.

For a finite genuine-zero window, pairwise disjoint circles are placed around
its distinct spectral poles.  Lean proves that the normalized circle integral
of the *full* finite `P_t` around one such circle is exactly that pole's
multiplicity-weighted Suzuki coefficient.  Summing those recovered residues
over upper, respectively lower, poles reconstructs the existing restricted
spectral windows.  Their difference therefore has the already-proved initial
velocity and height-integrated Gaussian heat action.

No contour deformation to the arithmetic safe half-plane is asserted here;
that is the next analytic frontier.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-! ## Exact spectral symmetries -/

/-- Functional-equation reflection transports a Suzuki summand at every
spatial point, not only at the previously used points `i` and `-i`. -/
theorem zetaSuzukiSpectralPSummand_functionalPartner
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) :
    zetaSuzukiSpectralPSummand t z
        (NontrivialZetaZero.functionalPartner rho) =
      zetaSuzukiSpectralPSummand (-t) (-z) rho := by
  unfold zetaSuzukiSpectralPSummand
    suzukiXiUpperEvaluationDenominator
  simp only [analyticZetaZeroMultiplicity_functionalPartner,
    NontrivialZetaZero.spectralCoordinate_functionalPartner]
  rw [suzukiSpectralScrewCoefficient_neg_parameter]
  by_cases hdenom : z + zetaSpectralCoordinate rho.1 = 0
  · have hleft : z - -zetaSpectralCoordinate rho.1 = 0 := by
      linear_combination hdenom
    have hright : -z - zetaSpectralCoordinate rho.1 = 0 := by
      linear_combination -hdenom
    rw [hleft, hright]
    simp
  · have hleft : z - -zetaSpectralCoordinate rho.1 ≠ 0 := by
      intro hzero
      apply hdenom
      linear_combination hzero
    have hright : -z - zetaSpectralCoordinate rho.1 ≠ 0 := by
      intro hzero
      apply hdenom
      linear_combination -hzero
    field_simp [hleft, hright]
    ring

/-- A nonnegative symmetric finite window inherits the exact space-time
reflection of every Suzuki summand. -/
theorem suzukiXiSpectralPWindow_functional_reflection
    (t : ℝ) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    suzukiXiSpectralPWindow t T z =
      suzukiXiSpectralPWindow (-t) T (-z) := by
  change
    (∑ rho ∈ spectralZetaZeroWindow T,
        zetaSuzukiSpectralPSummand t z rho) =
      ∑ rho ∈ spectralZetaZeroWindow T,
        zetaSuzukiSpectralPSummand (-t) (-z) rho
  rw [← sum_spectralZetaZeroWindow_comp_functionalPartner hT
    (fun rho ↦ zetaSuzukiSpectralPSummand t z rho)]
  apply Finset.sum_congr rfl
  intro rho _hrho
  exact zetaSuzukiSpectralPSummand_functionalPartner t z rho

/-! ## Isolating circles for a finite genuine divisor -/

/-- A family of positive radii isolates every pole in one finite symmetric
spectral window from every other pole in that window. -/
def SuzukiXiSpectralPWindowIsolatingRadii
    (T : ℝ) (R : ↑(spectralZetaZeroWindow T) → ℝ) : Prop :=
  ∀ rho : ↑(spectralZetaZeroWindow T),
    0 < R rho ∧
      ∀ sigma : ↑(spectralZetaZeroWindow T), sigma ≠ rho →
        zetaSpectralCoordinate sigma.1.1 ∉
          closedBall (zetaSpectralCoordinate rho.1.1) (R rho)

/-- Every finite genuine spectral window admits pairwise isolating positive
circle radii.  Distinctness is supplied by injectivity of the spectral
coordinate, so analytic multiplicity remains in the residue coefficient
rather than being represented by duplicate centers. -/
theorem exists_suzukiXiSpectralPWindowIsolatingRadii (T : ℝ) :
    ∃ R : ↑(spectralZetaZeroWindow T) → ℝ,
      SuzukiXiSpectralPWindowIsolatingRadii T R := by
  let S := spectralZetaZeroWindow T
  let center : ↑S → ℂ :=
    fun rho ↦ zetaSpectralCoordinate rho.1.1
  have hcenterInj : Function.Injective center := by
    intro rho sigma hcenter
    apply Subtype.ext
    apply Subtype.ext
    exact zetaSpectralCoordinate_injective hcenter
  obtain ⟨U, hU, hUdisjoint⟩ :=
    (Set.finite_range center).t2_separation
  have hexBall (rho : ↑S) :
      ∃ d : ℝ, 0 < d ∧ ball (center rho) d ⊆ U (center rho) := by
    exact (Metric.isOpen_iff.mp (hU (center rho)).2)
      (center rho) (hU (center rho)).1
  choose d hd hball using hexBall
  let R : ↑S → ℝ := fun rho ↦ d rho / 2
  refine ⟨R, ?_⟩
  intro rho
  have hRpos : 0 < R rho := by
    dsimp [R]
    linarith [hd rho]
  refine ⟨hRpos, ?_⟩
  intro sigma hne hmem
  have hcenters : center rho ≠ center sigma :=
    hcenterInj.ne hne.symm
  have hdisjoint : Disjoint (U (center rho)) (U (center sigma)) :=
    hUdisjoint (Set.mem_range_self rho) (Set.mem_range_self sigma)
      hcenters
  have hrhoSub :
      closedBall (center rho) (R rho) ⊆ U (center rho) := by
    apply (closedBall_subset_ball ?_).trans (hball rho)
    dsimp [R]
    linarith [hd rho]
  have hsigmaSub :
      closedBall (center sigma) (R sigma) ⊆ U (center sigma) := by
    apply (closedBall_subset_ball ?_).trans (hball sigma)
    dsimp [R]
    linarith [hd sigma]
  have hRposSigma : 0 < R sigma := by
    dsimp [R]
    linarith [hd sigma]
  exact Set.disjoint_left.1 hdisjoint
    (hrhoSub hmem)
    (hsigmaSub (mem_closedBall_self hRposSigma.le))

/-! ## Local residues of the full finite Suzuki function -/

/-- A Suzuki `P_t` summand is circle-integrable whenever its pole misses the
circle. -/
theorem circleIntegrable_zetaSuzukiSpectralPSummand
    (t : ℝ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (rho : NontrivialZetaZero)
    (hboundary : zetaSpectralCoordinate rho.1 ∉ sphere c R) :
    CircleIntegrable
      (fun z ↦ zetaSuzukiSpectralPSummand t z rho) c R := by
  have hkernel : CircleIntegrable
      (fun z : ℂ ↦ (z - zetaSpectralCoordinate rho.1)⁻¹) c R := by
    apply circleIntegrable_sub_inv_iff.mpr
    exact Or.inr (by simpa [abs_of_nonneg hR] using hboundary)
  let a : ℂ :=
    (analyticZetaZeroMultiplicity rho : ℂ) *
      suzukiSpectralScrewCoefficient t
        (zetaSpectralCoordinate rho.1)
  change CircleIntegrable
    (fun z : ℂ ↦ a * (z - zetaSpectralCoordinate rho.1)⁻¹) c R
  have hfun :
      (fun z : ℂ ↦ a * (z - zetaSpectralCoordinate rho.1)⁻¹) =
        (fun _ : ℂ ↦ a) •
          (fun z : ℂ ↦ (z - zetaSpectralCoordinate rho.1)⁻¹) := by
    funext z
    simp
  rw [hfun]
  exact hkernel.continuousOn_smul continuousOn_const

/-- The full finite Suzuki function is circle-integrable when all of its
poles miss the circle. -/
theorem circleIntegrable_suzukiXiSpectralPWindow
    (t T : ℝ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ rho ∈ spectralZetaZeroWindow T,
      zetaSpectralCoordinate rho.1 ∉ sphere c R) :
    CircleIntegrable (suzukiXiSpectralPWindow t T) c R := by
  unfold suzukiXiSpectralPWindow
  have hsum : CircleIntegrable
      (∑ rho ∈ spectralZetaZeroWindow T,
        fun z ↦
          (analyticZetaZeroMultiplicity rho : ℂ) *
            suzukiSpectralScrewCoefficient t
              (zetaSpectralCoordinate rho.1) /
              (z - zetaSpectralCoordinate rho.1)) c R := by
    apply CircleIntegrable.sum
    intro rho hrho
    simpa only [zetaSuzukiSpectralPSummand,
      suzukiXiUpperEvaluationDenominator] using
      (circleIntegrable_zetaSuzukiSpectralPSummand
          t hR rho (hboundary rho hrho))
  have hfun :
      (fun z : ℂ ↦
        ∑ rho ∈ spectralZetaZeroWindow T,
          (analyticZetaZeroMultiplicity rho : ℂ) *
            suzukiSpectralScrewCoefficient t
              (zetaSpectralCoordinate rho.1) /
              (z - zetaSpectralCoordinate rho.1)) =
        ∑ rho ∈ spectralZetaZeroWindow T,
          fun z ↦
            (analyticZetaZeroMultiplicity rho : ℂ) *
              suzukiSpectralScrewCoefficient t
                (zetaSpectralCoordinate rho.1) /
                (z - zetaSpectralCoordinate rho.1) := by
    funext z
    simp
  rw [hfun]
  exact hsum

/-- Integrating the full finite `P_t` around a circle isolating one selected
pole extracts exactly `2πi` times that pole's multiplicity-weighted Suzuki
coefficient. -/
theorem circleIntegral_suzukiXiSpectralPWindow_eq_poleCoefficient
    (t : ℝ) {T R : ℝ} (hR : 0 < R)
    (rho : NontrivialZetaZero)
    (hrho : rho ∈ spectralZetaZeroWindow T)
    (hisolate : ∀ sigma ∈ spectralZetaZeroWindow T, sigma ≠ rho →
      zetaSpectralCoordinate sigma.1 ∉
        closedBall (zetaSpectralCoordinate rho.1) R) :
    (∮ z in C(zetaSpectralCoordinate rho.1, R),
        suzukiXiSpectralPWindow t T z) =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((analyticZetaZeroMultiplicity rho : ℂ) *
          suzukiSpectralScrewCoefficient t
            (zetaSpectralCoordinate rho.1)) := by
  have hboundary : ∀ sigma ∈ spectralZetaZeroWindow T,
      zetaSpectralCoordinate sigma.1 ∉
        sphere (zetaSpectralCoordinate rho.1) R := by
    intro sigma hsigma
    by_cases hsr : sigma = rho
    · subst sigma
      intro hmem
      rw [mem_sphere, dist_self] at hmem
      exact hR.ne' hmem.symm
    · intro hmem
      exact hisolate sigma hsigma hsr (sphere_subset_closedBall hmem)
  change
    (∮ z in C(zetaSpectralCoordinate rho.1, R),
      ∑ sigma ∈ spectralZetaZeroWindow T,
        zetaSuzukiSpectralPSummand t z sigma) = _
  rw [circleIntegral.integral_fun_sum]
  · calc
      (∑ sigma ∈ spectralZetaZeroWindow T,
          ∮ z in C(zetaSpectralCoordinate rho.1, R),
            zetaSuzukiSpectralPSummand t z sigma) =
          ∮ z in C(zetaSpectralCoordinate rho.1, R),
            zetaSuzukiSpectralPSummand t z rho := by
        apply Finset.sum_eq_single rho
        · intro sigma hsigma hne
          have houtside := hisolate sigma hsigma hne
          unfold zetaSuzukiSpectralPSummand
            suzukiXiUpperEvaluationDenominator
          simp only [div_eq_mul_inv]
          rw [circleIntegral.integral_const_mul,
            circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall
              hR.le houtside, mul_zero]
        · intro hnotmem
          exact (hnotmem hrho).elim
      _ = ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          ((analyticZetaZeroMultiplicity rho : ℂ) *
            suzukiSpectralScrewCoefficient t
              (zetaSpectralCoordinate rho.1)) := by
        unfold zetaSuzukiSpectralPSummand
          suzukiXiUpperEvaluationDenominator
        simp only [div_eq_mul_inv]
        rw [circleIntegral.integral_const_mul,
          circleIntegral.integral_sub_inv_of_mem_ball
            (mem_ball_self hR)]
        push_cast
        ring
  · intro sigma hsigma
    exact circleIntegrable_zetaSuzukiSpectralPSummand
      t hR.le sigma (hboundary sigma hsigma)

/-- The normalized local circle residue of the full finite Suzuki function. -/
def suzukiXiSpectralPWindowCircleResidue
    (t T : ℝ) (rho : NontrivialZetaZero) (R : ℝ) : ℂ :=
  ((((2 * Real.pi : ℝ) : ℂ) * Complex.I)⁻¹) *
    (∮ z in C(zetaSpectralCoordinate rho.1, R),
      suzukiXiSpectralPWindow t T z)

/-- On an isolating circle, the normalized residue is exactly the selected
multiplicity-weighted Suzuki coefficient. -/
theorem suzukiXiSpectralPWindowCircleResidue_eq_coefficient
    (t : ℝ) {T : ℝ}
    (R : ↑(spectralZetaZeroWindow T) → ℝ)
    (hR : SuzukiXiSpectralPWindowIsolatingRadii T R)
    (rho : ↑(spectralZetaZeroWindow T)) :
    suzukiXiSpectralPWindowCircleResidue t T rho.1 (R rho) =
      (analyticZetaZeroMultiplicity rho.1 : ℂ) *
        suzukiSpectralScrewCoefficient t
          (zetaSpectralCoordinate rho.1.1) := by
  have hisolate : ∀ sigma ∈ spectralZetaZeroWindow T,
      sigma ≠ rho.1 →
        zetaSpectralCoordinate sigma.1 ∉
          closedBall (zetaSpectralCoordinate rho.1.1) (R rho) := by
    intro sigma hsigma hne
    exact (hR rho).2 ⟨sigma, hsigma⟩ (by
      intro heq
      apply hne
      exact congrArg Subtype.val heq)
  unfold suzukiXiSpectralPWindowCircleResidue
  rw [circleIntegral_suzukiXiSpectralPWindow_eq_poleCoefficient
    t (hR rho).1 rho.1 rho.2 hisolate]
  have htwoPiI :
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (by norm_num [Real.pi_ne_zero]) Complex.I_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ htwoPiI, one_mul]

/-! ## Upper/lower Hardy residue projections -/

/-- Reconstruct the upper-pole part of a finite Suzuki window from normalized
local circle residues of the full finite function. -/
def suzukiXiUpperCircleProjectionWindow
    (t T : ℝ) (z : ℂ)
    (R : ↑(spectralZetaZeroWindow T) → ℝ) : ℂ :=
  ∑ rho : ↑(spectralZetaZeroWindow T),
    if 0 < (zetaSpectralCoordinate rho.1.1).im then
      suzukiXiSpectralPWindowCircleResidue t T rho.1 (R rho) /
        (z - zetaSpectralCoordinate rho.1.1)
    else 0

/-- Reconstruct the lower-pole part of a finite Suzuki window from normalized
local circle residues of the full finite function. -/
def suzukiXiLowerCircleProjectionWindow
    (t T : ℝ) (z : ℂ)
    (R : ↑(spectralZetaZeroWindow T) → ℝ) : ℂ :=
  ∑ rho : ↑(spectralZetaZeroWindow T),
    if (zetaSpectralCoordinate rho.1.1).im < 0 then
      suzukiXiSpectralPWindowCircleResidue t T rho.1 (R rho) /
        (z - zetaSpectralCoordinate rho.1.1)
    else 0

/-- The upper local-circle projection is exactly the pre-existing upper
restricted spectral `P_t` window. -/
theorem suzukiXiUpperCircleProjectionWindow_eq_restricted
    (t T : ℝ) (z : ℂ)
    (R : ↑(spectralZetaZeroWindow T) → ℝ)
    (hR : SuzukiXiSpectralPWindowIsolatingRadii T R) :
    suzukiXiUpperCircleProjectionWindow t T z R =
      suzukiXiUpperRestrictedSpectralPWindow t T z := by
  unfold suzukiXiUpperCircleProjectionWindow
    suzukiXiUpperRestrictedSpectralPWindow
  rw [Finset.univ_eq_attach]
  calc
    (∑ rho ∈ (spectralZetaZeroWindow T).attach,
        if 0 < (zetaSpectralCoordinate rho.1.1).im then
          suzukiXiSpectralPWindowCircleResidue t T rho.1 (R rho) /
            (z - zetaSpectralCoordinate rho.1.1)
        else 0) =
        ∑ rho ∈ (spectralZetaZeroWindow T).attach,
          if 0 < (zetaSpectralCoordinate rho.1.1).im then
            zetaSuzukiSpectralPSummand t z rho.1
          else 0 := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      by_cases hupper : 0 < (zetaSpectralCoordinate rho.1.1).im
      · simp only [if_pos hupper]
        rw [suzukiXiSpectralPWindowCircleResidue_eq_coefficient t R hR rho]
        rfl
      · simp only [if_neg hupper]
    _ = ∑ rho ∈ spectralZetaZeroWindow T,
        if 0 < (zetaSpectralCoordinate rho.1).im then
          zetaSuzukiSpectralPSummand t z rho
        else 0 :=
      Finset.sum_attach (spectralZetaZeroWindow T)
        (fun rho ↦ if 0 < (zetaSpectralCoordinate rho.1).im then
          zetaSuzukiSpectralPSummand t z rho else 0)

/-- The lower local-circle projection is exactly the pre-existing lower
restricted spectral `P_t` window. -/
theorem suzukiXiLowerCircleProjectionWindow_eq_restricted
    (t T : ℝ) (z : ℂ)
    (R : ↑(spectralZetaZeroWindow T) → ℝ)
    (hR : SuzukiXiSpectralPWindowIsolatingRadii T R) :
    suzukiXiLowerCircleProjectionWindow t T z R =
      suzukiXiLowerRestrictedSpectralPWindow t T z := by
  unfold suzukiXiLowerCircleProjectionWindow
    suzukiXiLowerRestrictedSpectralPWindow
  rw [Finset.univ_eq_attach]
  calc
    (∑ rho ∈ (spectralZetaZeroWindow T).attach,
        if (zetaSpectralCoordinate rho.1.1).im < 0 then
          suzukiXiSpectralPWindowCircleResidue t T rho.1 (R rho) /
            (z - zetaSpectralCoordinate rho.1.1)
        else 0) =
        ∑ rho ∈ (spectralZetaZeroWindow T).attach,
          if (zetaSpectralCoordinate rho.1.1).im < 0 then
            zetaSuzukiSpectralPSummand t z rho.1
          else 0 := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      by_cases hlower : (zetaSpectralCoordinate rho.1.1).im < 0
      · simp only [if_pos hlower]
        rw [suzukiXiSpectralPWindowCircleResidue_eq_coefficient t R hR rho]
        rfl
      · simp only [if_neg hlower]
    _ = ∑ rho ∈ spectralZetaZeroWindow T,
        if (zetaSpectralCoordinate rho.1).im < 0 then
          zetaSuzukiSpectralPSummand t z rho
        else 0 :=
      Finset.sum_attach (spectralZetaZeroWindow T)
        (fun rho ↦ if (zetaSpectralCoordinate rho.1).im < 0 then
          zetaSuzukiSpectralPSummand t z rho else 0)

/-- The signed upper-minus-lower residue projection of the full finite
Suzuki function. -/
def suzukiXiOffAxisSignedCircleProjectionWindow
    (t T : ℝ) (z : ℂ)
    (R : ↑(spectralZetaZeroWindow T) → ℝ) : ℂ :=
  suzukiXiUpperCircleProjectionWindow t T z R -
    suzukiXiLowerCircleProjectionWindow t T z R

/-- The signed local-circle projection is exactly the established signed
off-axis Suzuki response. -/
theorem suzukiXiOffAxisSignedCircleProjectionWindow_eq_response
    (t T : ℝ) (z : ℂ)
    (R : ↑(spectralZetaZeroWindow T) → ℝ)
    (hR : SuzukiXiSpectralPWindowIsolatingRadii T R) :
    suzukiXiOffAxisSignedCircleProjectionWindow t T z R =
      suzukiXiOffAxisSignedSpectralPResponseWindow t T z := by
  unfold suzukiXiOffAxisSignedCircleProjectionWindow
    suzukiXiOffAxisSignedSpectralPResponseWindow
  rw [suzukiXiUpperCircleProjectionWindow_eq_restricted t T z R hR,
    suzukiXiLowerCircleProjectionWindow_eq_restricted t T z R hR]

/-- The signed residue projection has the exact established real-time
derivative at every screw time. -/
theorem hasDerivAt_suzukiXiOffAxisSignedCircleProjectionWindow_time
    (t T : ℝ) (z : ℂ)
    (R : ↑(spectralZetaZeroWindow T) → ℝ)
    (hR : SuzukiXiSpectralPWindowIsolatingRadii T R) :
    HasDerivAt
      (fun u : ℝ ↦ suzukiXiOffAxisSignedCircleProjectionWindow u T z R)
      (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow t T z) t := by
  have heq :
      (fun u : ℝ ↦ suzukiXiOffAxisSignedCircleProjectionWindow u T z R) =
        fun u : ℝ ↦ suzukiXiOffAxisSignedSpectralPResponseWindow u T z := by
    funext u
    exact suzukiXiOffAxisSignedCircleProjectionWindow_eq_response
      u T z R hR
  rw [heq]
  exact hasDerivAt_suzukiXiOffAxisSignedSpectralPResponseWindow_time t T z

/-- At time zero, the first variation of the signed residue projection is
exactly `-i` times the finite Blaschke logarithmic derivative. -/
theorem hasDerivAt_suzukiXiOffAxisSignedCircleProjectionWindow_zero_time
    {T : ℝ} (hT : 0 ≤ T) (z : ℂ)
    (R : ↑(spectralZetaZeroWindow T) → ℝ)
    (hR : SuzukiXiSpectralPWindowIsolatingRadii T R) :
    HasDerivAt
      (fun u : ℝ ↦ suzukiXiOffAxisSignedCircleProjectionWindow u T z R)
      (-Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow z T) 0 := by
  simpa only [
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time hT]
    using
      (hasDerivAt_suzukiXiOffAxisSignedCircleProjectionWindow_time
        0 T z R hR)

/-- The actual time derivative at zero of the signed circle-projected full
finite Suzuki function. -/
def suzukiXiOffAxisSignedCircleProjectionInitialVelocityWindow
    (T : ℝ) (z : ℂ)
    (R : ↑(spectralZetaZeroWindow T) → ℝ) : ℂ :=
  deriv
    (fun u : ℝ ↦ suzukiXiOffAxisSignedCircleProjectionWindow u T z R) 0

/-- The actual initial derivative of the circle projection is the finite
signed spectral response derivative. -/
theorem suzukiXiOffAxisSignedCircleProjectionInitialVelocityWindow_eq_response
    (T : ℝ) (z : ℂ)
    (R : ↑(spectralZetaZeroWindow T) → ℝ)
    (hR : SuzukiXiSpectralPWindowIsolatingRadii T R) :
    suzukiXiOffAxisSignedCircleProjectionInitialVelocityWindow T z R =
      suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow 0 T z :=
  (hasDerivAt_suzukiXiOffAxisSignedCircleProjectionWindow_time
    0 T z R hR).deriv

/-- At a nonnegative cutoff, the actual initial derivative extracted by the
circle projection is `-i` times the finite Blaschke logarithmic derivative. -/
theorem suzukiXiOffAxisSignedCircleProjectionInitialVelocityWindow_eq_blaschke
    {T : ℝ} (hT : 0 ≤ T) (z : ℂ)
    (R : ↑(spectralZetaZeroWindow T) → ℝ)
    (hR : SuzukiXiSpectralPWindowIsolatingRadii T R) :
    suzukiXiOffAxisSignedCircleProjectionInitialVelocityWindow T z R =
      -Complex.I * riemannXiUpperBlaschkeLogDerivativeWindow z T := by
  rw [
    suzukiXiOffAxisSignedCircleProjectionInitialVelocityWindow_eq_response
      T z R hR,
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time hT]

/-- Consequently, the height integral of the initial velocity extracted
from the full finite Suzuki function is the finite Gaussian heat action. -/
theorem ofReal_intervalIntegral_two_mul_re_signedCircleProjectionInitialVelocity_eq_heatActionWindow
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    {T : ℝ} (hT : 0 ≤ T)
    (R : ↑(spectralZetaZeroWindow T) → ℝ)
    (hR : SuzukiXiSpectralPWindowIsolatingRadii T R) :
    ENNReal.ofReal
        (∫ u : ℝ in 0..y, 2 *
          (suzukiXiOffAxisSignedCircleProjectionInitialVelocityWindow
            T (upperBoundaryApproachPoint x u) R).re) =
      riemannXiUpperHyperbolicHeatActionWindow
        (upperBoundaryApproachPoint x y) T := by
  simp_rw [
    suzukiXiOffAxisSignedCircleProjectionInitialVelocityWindow_eq_response
      T _ R hR]
  rw [
    ofReal_intervalIntegral_two_mul_re_suzukiInitialResponseWindow_eq_logDefectWindow
      hdelta hgap hy hySmall hT]
  symm
  apply riemannXiUpperHyperbolicHeatActionWindow_eq_logDefectWindow
    (by simpa using hy)
  exact riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
    hdelta hgap hy hySmall

end

end RiemannGaussian

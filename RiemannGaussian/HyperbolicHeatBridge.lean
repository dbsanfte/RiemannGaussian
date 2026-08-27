import RiemannGaussian.FiniteHardyCanonicalConclusion
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Hyperbolic defect as a Gaussian heat integral

This file gives an exact proper-time representation of the logarithmic
pseudo-hyperbolic defect.  For two distinct points of the upper half-plane,
the negative logarithm of their pseudo-hyperbolic distance is the limit of a
positive difference of Gaussian heat kernels.  The result is stated as a
limit of truncated interval integrals, so no convergence of an improper
integral is assumed.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory Polynomial Set Topology intervalIntegral

/-- The heat-kernel difference associated with one upper-half-plane pair in
real coordinates. -/
def pairHyperbolicHeatIntegrand (d v a t : ℝ) : ℝ :=
  t⁻¹ *
    (Real.exp (-(pairHyperbolicUpperSq d v a * t)) -
      Real.exp (-(pairHyperbolicLowerSq d v a * t)))

/-- The heat-kernel difference factors into a common Gaussian and a positive
hyperbolic-sine factor. -/
theorem pairHyperbolicHeatIntegrand_eq_gaussian_sinh
    (d v a t : ℝ) :
    pairHyperbolicHeatIntegrand d v a t =
      2 * t⁻¹ * Real.exp (-(t * (d ^ 2 + v ^ 2 + a ^ 2))) *
        Real.sinh (2 * t * v * a) := by
  have hupper :
      Real.exp (-(pairHyperbolicUpperSq d v a * t)) =
        Real.exp (-(t * (d ^ 2 + v ^ 2 + a ^ 2))) *
          Real.exp (2 * t * v * a) := by
    rw [← Real.exp_add]
    unfold pairHyperbolicUpperSq
    congr 1
    ring
  have hlower :
      Real.exp (-(pairHyperbolicLowerSq d v a * t)) =
        Real.exp (-(t * (d ^ 2 + v ^ 2 + a ^ 2))) *
          Real.exp (-(2 * t * v * a)) := by
    rw [← Real.exp_add]
    unfold pairHyperbolicLowerSq
    congr 1
    ring
  unfold pairHyperbolicHeatIntegrand
  rw [hupper, hlower, Real.sinh_eq]
  ring

/-- At positive proper time, positive heights make the pair heat integrand
strictly positive. -/
theorem pairHyperbolicHeatIntegrand_pos
    {d v a t : ℝ} (hv : 0 < v) (ha : 0 < a) (ht : 0 < t) :
    0 < pairHyperbolicHeatIntegrand d v a t := by
  rw [pairHyperbolicHeatIntegrand_eq_gaussian_sinh]
  have hsinh : 0 < Real.sinh (2 * t * v * a) :=
    Real.sinh_pos_iff.mpr (by positivity)
  positivity

/-- Frullani's formula identifies the truncated proper-time limit with the
logarithm of the squared-distance ratio. -/
theorem tendsto_pairHyperbolicHeatIntegral_log_ratio
    {d v a : ℝ} (hv : 0 < v) (ha : 0 < a)
    (hupper : 0 < pairHyperbolicUpperSq d v a) :
    Tendsto
      (fun p : ℝ × ℝ ↦
        ∫ t in p.1..p.2, pairHyperbolicHeatIntegrand d v a t)
      ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop)
      (nhds (Real.log
        (pairHyperbolicLowerSq d v a /
          pairHyperbolicUpperSq d v a))) := by
  have hf : LocallyIntegrableOn (fun x : ℝ ↦ Real.exp (-x)) (Ioi 0) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn.locallyIntegrableOn
      measurableSet_Ioi
  have hzero :
      Tendsto (fun x : ℝ ↦ Real.exp (-x)) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hcont : Continuous (fun x : ℝ ↦ Real.exp (-x)) :=
      Real.continuous_exp.comp continuous_neg
    have hcw : ContinuousWithinAt (fun x : ℝ ↦ Real.exp (-x)) (Ioi 0) 0 :=
      hcont.continuousAt.continuousWithinAt
    simpa only [ContinuousWithinAt, neg_zero, Real.exp_zero] using hcw
  have hinfinity :
      Tendsto (fun x : ℝ ↦ Real.exp (-x)) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hlower : 0 < pairHyperbolicLowerSq d v a :=
    pairHyperbolicLowerSq_pos ha hv
  simpa only [pairHyperbolicHeatIntegrand, smul_eq_mul, sub_zero, mul_one] using
    (Frullani.tendsto_intervalIntegral
      (f := fun x : ℝ ↦ Real.exp (-x))
      (a := pairHyperbolicUpperSq d v a)
      (b := pairHyperbolicLowerSq d v a)
      (L := (1 : ℝ)) (R := (0 : ℝ))
      hf hupper hlower hzero hinfinity)

/-- The logarithm of the squared-distance ratio is exactly twice the
negative logarithm of the pseudo-hyperbolic radius. -/
theorem pairHyperbolicLogRatio_eq_neg_two_log_radius
    {d v a : ℝ} (hv : 0 < v) (ha : 0 < a)
    (hupper : 0 < pairHyperbolicUpperSq d v a) :
    Real.log
        (pairHyperbolicLowerSq d v a /
          pairHyperbolicUpperSq d v a) =
      -2 * Real.log (pairHyperbolicRadius d v a) := by
  have hlower : 0 < pairHyperbolicLowerSq d v a :=
    pairHyperbolicLowerSq_pos ha hv
  have hratio : 0 ≤
      pairHyperbolicUpperSq d v a /
        pairHyperbolicLowerSq d v a :=
    (div_nonneg hupper.le hlower.le)
  unfold pairHyperbolicRadius
  rw [Real.log_div hlower.ne' hupper.ne', Real.log_sqrt hratio,
    Real.log_div hupper.ne' hlower.ne']
  ring

/-- Exact proper-time representation of the logarithmic
pseudo-hyperbolic defect. -/
theorem tendsto_pairHyperbolicHeatIntegral
    {d v a : ℝ} (hv : 0 < v) (ha : 0 < a)
    (hupper : 0 < pairHyperbolicUpperSq d v a) :
    Tendsto
      (fun p : ℝ × ℝ ↦
        ∫ t in p.1..p.2, pairHyperbolicHeatIntegrand d v a t)
      ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop)
      (nhds (-2 * Real.log (pairHyperbolicRadius d v a))) := by
  rw [← pairHyperbolicLogRatio_eq_neg_two_log_radius hv ha hupper]
  exact tendsto_pairHyperbolicHeatIntegral_log_ratio hv ha hupper

/-- Coordinate-free complex form of the pair heat integrand. -/
def upperHalfPlaneHyperbolicHeatIntegrand (z alpha : ℂ) (t : ℝ) : ℝ :=
  t⁻¹ *
    (Real.exp (-(Complex.normSq (z - alpha) * t)) -
      Real.exp (-(Complex.normSq (z - starRingEnd ℂ alpha) * t)))

/-- The complex heat integrand is the real-coordinate heat integrand. -/
theorem upperHalfPlaneHyperbolicHeatIntegrand_eq_pair
    (z alpha : ℂ) (t : ℝ) :
    upperHalfPlaneHyperbolicHeatIntegrand z alpha t =
      pairHyperbolicHeatIntegrand
        (z.re - alpha.re) z.im alpha.im t := by
  have hupper : Complex.normSq (z - alpha) =
      pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im := by
    unfold pairHyperbolicUpperSq Complex.normSq
    simp
    ring
  have hlower : Complex.normSq (z - starRingEnd ℂ alpha) =
      pairHyperbolicLowerSq (z.re - alpha.re) z.im alpha.im := by
    unfold pairHyperbolicLowerSq Complex.normSq
    simp
    ring
  unfold upperHalfPlaneHyperbolicHeatIntegrand pairHyperbolicHeatIntegrand
  rw [hupper, hlower]

/-- For two distinct upper-half-plane points, the complex heat-kernel
difference integrates in the truncated limit to `-2 log rho`. -/
theorem tendsto_upperHalfPlaneHyperbolicHeatIntegral
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    (hne : z ≠ alpha) :
    Tendsto
      (fun p : ℝ × ℝ ↦
        ∫ t in p.1..p.2,
          upperHalfPlaneHyperbolicHeatIntegrand z alpha t)
      ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop)
      (nhds (-2 * Real.log
        (upperHalfPlanePseudoHyperbolicDistance z alpha))) := by
  have hupper : 0 <
      pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im := by
    rw [show pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im =
        Complex.normSq (z - alpha) by
      unfold pairHyperbolicUpperSq Complex.normSq
      simp
      ring]
    exact Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  have halphaForm :
      (alpha.re : ℂ) + Complex.I * (alpha.im : ℂ) = alpha := by
    rw [mul_comm]
    exact Complex.re_add_im alpha
  have hzForm : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    rw [mul_comm]
    exact Complex.re_add_im z
  have hdistance :
      upperHalfPlanePseudoHyperbolicDistance z alpha =
        pairHyperbolicRadius (z.re - alpha.re) z.im alpha.im := by
    rw [← halphaForm, ← hzForm,
      upperHalfPlanePseudoHyperbolicDistance_eq_pairRadius
        alpha.re alpha.im z.re z.im halpha hz]
    simp
  rw [hdistance]
  simpa only [upperHalfPlaneHyperbolicHeatIntegrand_eq_pair] using
    (tendsto_pairHyperbolicHeatIntegral hz halpha hupper)

/-! ## Multiplicity-counted finite heat actions -/

/-- The truncated heat action of a finite multiset of upper-half-plane
points.  The multiset sum retains algebraic multiplicities. -/
def upperHalfPlaneHyperbolicHeatAction
    (z : ℂ) (upper : Multiset ℂ) (p : ℝ × ℝ) : ℝ :=
  (upper.map fun alpha ↦
    ∫ t in p.1..p.2,
      upperHalfPlaneHyperbolicHeatIntegrand z alpha t).sum

/-- Before combining logarithms, the finite heat action converges to the sum
of the individual logarithmic defects. -/
theorem tendsto_upperHalfPlaneHyperbolicHeatAction_sum
    {z : ℂ} (hz : 0 < z.im) (upper : Multiset ℂ)
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    (hne : ∀ alpha ∈ upper, z ≠ alpha) :
    Tendsto
      (upperHalfPlaneHyperbolicHeatAction z upper)
      ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop)
      (nhds ((upper.map fun alpha ↦
        -2 * Real.log
          (upperHalfPlanePseudoHyperbolicDistance z alpha)).sum)) := by
  induction upper using Multiset.induction_on with
  | empty =>
      change Tendsto (fun _ : ℝ × ℝ ↦ 0)
        ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop) (nhds 0)
      exact tendsto_const_nhds
  | @cons alpha upper ih =>
      have halphaHead : 0 < alpha.im := halpha alpha (by simp)
      have hneHead : z ≠ alpha := hne alpha (by simp)
      have halphaTail : ∀ beta ∈ upper, 0 < beta.im := by
        intro beta hbeta
        exact halpha beta (by simp [hbeta])
      have hneTail : ∀ beta ∈ upper, z ≠ beta := by
        intro beta hbeta
        exact hne beta (by simp [hbeta])
      have haction :
          upperHalfPlaneHyperbolicHeatAction z (alpha ::ₘ upper) =
            fun p : ℝ × ℝ ↦
              (∫ t in p.1..p.2,
                upperHalfPlaneHyperbolicHeatIntegrand z alpha t) +
                upperHalfPlaneHyperbolicHeatAction z upper p := by
        funext p
        simp [upperHalfPlaneHyperbolicHeatAction]
      rw [haction]
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact (tendsto_upperHalfPlaneHyperbolicHeatIntegral
        hz halphaHead hneHead).add (ih halphaTail hneTail)

/-- The complete multiplicity-counted hyperbolic product is exactly the
exponential encoding of the limiting finite heat action. -/
theorem tendsto_upperHalfPlaneHyperbolicHeatAction
    {z : ℂ} (hz : 0 < z.im) (upper : Multiset ℂ)
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    (hne : ∀ alpha ∈ upper, z ≠ alpha) :
    Tendsto
      (upperHalfPlaneHyperbolicHeatAction z upper)
      ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop)
      (nhds (-2 * Real.log
        ((upper.map fun alpha ↦
          upperHalfPlanePseudoHyperbolicDistance z alpha).prod))) := by
  let radii := upper.map fun alpha ↦
    upperHalfPlanePseudoHyperbolicDistance z alpha
  have hradii : ∀ r ∈ radii, r ≠ 0 := by
    intro r hr
    obtain ⟨alpha, halphaMem, rfl⟩ := Multiset.mem_map.mp hr
    exact (upperHalfPlanePseudoHyperbolicDistance_pos_of_ne
      hz (halpha alpha halphaMem) (hne alpha halphaMem)).ne'
  have hsum :
      (upper.map fun alpha ↦
        -2 * Real.log
          (upperHalfPlanePseudoHyperbolicDistance z alpha)).sum =
        -2 * Real.log radii.prod := by
    rw [Real.log_multiset_prod hradii, ← Multiset.sum_map_mul_left,
      Multiset.map_map]
    rfl
  rw [← hsum]
  exact tendsto_upperHalfPlaneHyperbolicHeatAction_sum
    hz upper halpha hne

/-! ## The canonical finite Hardy core -/

/-- The total logarithmic heat mass of the canonical influence core. -/
def canonicalInsideInfluenceDiskHeatMass (A : ℝ[X]) (z : ℂ) : ℝ :=
  -2 * Real.log
    (((canonicalInsideInfluenceDiskRoots A z).map fun alpha ↦
      upperHalfPlanePseudoHyperbolicDistance z alpha).prod)

/-- At every pinned upper root of a positive finite homotopy, the canonical
Hardy influence core has a Gaussian heat action whose limiting mass is
bounded below by the strictly positive one-pair threshold defect. -/
theorem canonicalInsideInfluenceDiskHeatAction_frontier
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta)
    {z : ℂ} (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    Tendsto
        (upperHalfPlaneHyperbolicHeatAction z
          (canonicalInsideInfluenceDiskRoots A z))
        ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop)
        (nhds (canonicalInsideInfluenceDiskHeatMass A z)) ∧
      0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
      -2 * Real.log (pairHyperbolicThreshold eta z.im) ≤
        canonicalInsideInfluenceDiskHeatMass A z := by
  let core := canonicalInsideInfluenceDiskRoots A z
  let radii := core.map fun alpha ↦
    upperHalfPlanePseudoHyperbolicDistance z alpha
  have halpha : ∀ alpha ∈ core, 0 < alpha.im := by
    intro alpha halphaMem
    exact canonicalInsideInfluenceDiskRoots_im_pos alpha halphaMem
  have hne : ∀ alpha ∈ core, z ≠ alpha := by
    intro alpha halphaMem
    exact finiteE_root_ne_upperResidual hA heta hroot
      (realPolynomial_roots_eq_real_add_conjugatePairs A)
      alpha (canonicalInsideInfluenceDiskRoots_mem_upperRoots halphaMem)
  have hradii : ∀ r ∈ radii, 0 < r := by
    intro r hr
    obtain ⟨alpha, halphaMem, rfl⟩ := Multiset.mem_map.mp hr
    exact upperHalfPlanePseudoHyperbolicDistance_pos_of_ne
      hz (halpha alpha halphaMem) (hne alpha halphaMem)
  have hRpos : 0 < radii.prod := Multiset.prod_pos hradii
  have hthresholdPos : 0 < pairHyperbolicThreshold eta z.im :=
    pairHyperbolicThreshold_pos heta hz
  have hthresholdLtOne : pairHyperbolicThreshold eta z.im < 1 :=
    pairHyperbolicThreshold_lt_one heta hz
  have hRle : radii.prod ≤ pairHyperbolicThreshold eta z.im := by
    simpa [core, radii] using
      (canonicalInsideInfluenceDiskRootPseudoHyperbolicProduct_le_threshold_centerHeight
        hA heta hz hroot)
  have hlogLe : Real.log radii.prod ≤
      Real.log (pairHyperbolicThreshold eta z.im) :=
    (Real.log_le_log_iff hRpos hthresholdPos).2 hRle
  have hthresholdLogNeg :
      Real.log (pairHyperbolicThreshold eta z.im) < 0 :=
    Real.log_neg hthresholdPos hthresholdLtOne
  refine ⟨?_, by nlinarith, ?_⟩
  · simpa [canonicalInsideInfluenceDiskHeatMass, core, radii] using
      (tendsto_upperHalfPlaneHyperbolicHeatAction hz core halpha hne)
  · rw [show canonicalInsideInfluenceDiskHeatMass A z =
        -2 * Real.log radii.prod by
      simp [canonicalInsideInfluenceDiskHeatMass, core, radii]]
    nlinarith

end

end RiemannGaussian

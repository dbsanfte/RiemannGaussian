import RiemannGaussian.FiniteToEntireHeatWindowRemainder

/-!
# Quantitative Gaussian bounds for polynomial heat tails

This file supplies the quantitative half of the unused-root tail problem.
At fixed positive proper time, one hyperbolic heat term is bounded by the
ordinary Euclidean Gaussian centered at its root.  Summing with algebraic
multiplicity bounds every radial upper-root tail by the polynomial degree
times that Gaussian.

The exact complement of finitely many divisor clusters inherits the same
bound whenever all of its roots are separated from the observation point.
An asymptotic theorem then reduces vanishing of this remainder to two explicit
obligations: radial escape of every unused root and decay of the resulting
degree-weighted Gaussian envelope.  Neither obligation is inferred from
local uniform convergence; the remaining root-localization problem therefore
stays visible in the theorem hypotheses.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- At positive proper time, the hyperbolic heat difference is bounded by
the ordinary Euclidean Gaussian centered at its upper argument. -/
theorem upperHalfPlaneHyperbolicHeatIntegrand_le_euclideanGaussian
    (z alpha : ℂ) {tau : ℝ} (htau : 0 < tau) :
    upperHalfPlaneHyperbolicHeatIntegrand z alpha tau ≤
      tau⁻¹ * Real.exp (-(Complex.normSq (z - alpha) * tau)) := by
  have hsub :
      Real.exp (-(Complex.normSq (z - alpha) * tau)) -
          Real.exp
            (-(Complex.normSq (z - starRingEnd ℂ alpha) * tau)) ≤
        Real.exp (-(Complex.normSq (z - alpha) * tau)) := by
    nlinarith [Real.exp_pos
      (-(Complex.normSq (z - starRingEnd ℂ alpha) * tau))]
  unfold upperHalfPlaneHyperbolicHeatIntegrand
  exact mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr htau.le)

/-- A point at least `R` from the observation point has the corresponding
uniform Gaussian bound. -/
theorem upperHalfPlaneHyperbolicHeatIntegrand_le_radialGaussian
    (z alpha : ℂ) {tau R : ℝ} (htau : 0 < tau)
    (hR : 0 ≤ R) (hdist : R ≤ dist z alpha) :
    upperHalfPlaneHyperbolicHeatIntegrand z alpha tau ≤
      tau⁻¹ * Real.exp (-(R ^ 2 * tau)) := by
  have hnorm : R ≤ ‖z - alpha‖ := by
    simpa [dist_eq_norm] using hdist
  have hsq : R ^ 2 ≤ Complex.normSq (z - alpha) := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_le_sq₀ hR (norm_nonneg _)).2 hnorm
  have hexp :
      Real.exp (-(Complex.normSq (z - alpha) * tau)) ≤
        Real.exp (-(R ^ 2 * tau)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact
    (upperHalfPlaneHyperbolicHeatIntegrand_le_euclideanGaussian
      z alpha htau).trans
      (mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr htau.le))

/-- A finite collection of points outside one observation ball has heat at
most its cardinality times the common Gaussian envelope. -/
theorem finiteUpperHyperbolicHeatSum_le_card_mul_radialGaussian
    (z : ℂ) (upper : Multiset ℂ) {tau R : ℝ} (htau : 0 < tau)
    (hR : 0 ≤ R)
    (hdist : ∀ alpha ∈ upper, R ≤ dist z alpha) :
    finiteUpperHyperbolicHeatSum z upper tau ≤
      (upper.card : ℝ) *
        (tau⁻¹ * Real.exp (-(R ^ 2 * tau))) := by
  let W := fun alpha : ℂ ↦
    upperHalfPlaneHyperbolicHeatIntegrand z alpha tau
  let C := tau⁻¹ * Real.exp (-(R ^ 2 * tau))
  have hle := (upper.map W).sum_le_card_nsmul C (by
    intro w hw
    obtain ⟨alpha, halpha, rfl⟩ := Multiset.mem_map.mp hw
    exact upperHalfPlaneHyperbolicHeatIntegrand_le_radialGaussian
      z alpha htau hR (hdist alpha halpha))
  simpa [finiteUpperHyperbolicHeatSum, W, C, nsmul_eq_mul] using hle

/-- The multiplicity-counted upper roots never outnumber the degree. -/
theorem realPolynomialUpperRootMultiset_card_le_natDegree (A : ℝ[X]) :
    (realPolynomialUpperRootMultiset A).card ≤ A.natDegree := by
  have hcard :=
    realPolynomial_realRoot_card_add_two_mul_upperRoot_card A
  omega

/-- The upper polynomial root occurrences lying on or outside the closed
observation ball of radius `R`. -/
def realPolynomialUpperRootMultisetOutsideClosedBall
    (A : ℝ[X]) (z : ℂ) (R : ℝ) : Multiset ℂ :=
  (realPolynomialUpperRootMultiset A).filter fun alpha ↦
    R ≤ dist z alpha

/-- The heat carried by the upper polynomial roots on or outside a closed
observation ball. -/
def realPolynomialUpperHeatTailOutsideClosedBall
    (A : ℝ[X]) (z : ℂ) (R tau : ℝ) : ℝ :=
  finiteUpperHyperbolicHeatSum z
    (realPolynomialUpperRootMultisetOutsideClosedBall A z R) tau

/-- The radial upper-root heat tail has an explicit degree-weighted Gaussian
bound. -/
theorem realPolynomialUpperHeatTailOutsideClosedBall_le_degreeGaussian
    (A : ℝ[X]) (z : ℂ) {R tau : ℝ}
    (hR : 0 ≤ R) (htau : 0 < tau) :
    realPolynomialUpperHeatTailOutsideClosedBall A z R tau ≤
      (A.natDegree : ℝ) *
        (tau⁻¹ * Real.exp (-(R ^ 2 * tau))) := by
  let tail := realPolynomialUpperRootMultisetOutsideClosedBall A z R
  let C := tau⁻¹ * Real.exp (-(R ^ 2 * tau))
  have hsum : finiteUpperHyperbolicHeatSum z tail tau ≤
      (tail.card : ℝ) * C := by
    apply finiteUpperHyperbolicHeatSum_le_card_mul_radialGaussian
      z tail htau hR
    intro alpha halpha
    exact (Multiset.mem_filter.mp halpha).2
  have hcard : tail.card ≤ A.natDegree :=
    (Multiset.card_le_card (Multiset.filter_le _ _)).trans
      (realPolynomialUpperRootMultiset_card_le_natDegree A)
  have hC : 0 ≤ C := by
    exact mul_nonneg (inv_nonneg.mpr htau.le) (Real.exp_pos _).le
  calc
    realPolynomialUpperHeatTailOutsideClosedBall A z R tau =
        finiteUpperHyperbolicHeatSum z tail tau := rfl
    _ ≤ (tail.card : ℝ) * C := hsum
    _ ≤ (A.natDegree : ℝ) * C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC

/-- At positive time and an upper observation point, radial upper-root heat
tails are nonnegative. -/
theorem realPolynomialUpperHeatTailOutsideClosedBall_nonneg
    (A : ℝ[X]) {z : ℂ} (hz : 0 < z.im) (R : ℝ)
    {tau : ℝ} (htau : 0 < tau) :
    0 ≤ realPolynomialUpperHeatTailOutsideClosedBall A z R tau := by
  apply finiteUpperHyperbolicHeatSum_nonneg hz
  · intro alpha halpha
    exact realPolynomialUpperRootMultiset_im_pos A alpha
      (Multiset.mem_of_le (Multiset.filter_le _ _) halpha)
  · exact htau

/-- Radial polynomial heat tails tend to zero whenever their explicit
degree-weighted Gaussian envelopes do. -/
theorem tendsto_realPolynomialUpperHeatTailOutsideClosedBall_zero
    {kappa : Type*} {phi : Filter kappa} (A : kappa → ℝ[X])
    {z : ℂ} (hz : 0 < z.im) (R : kappa → ℝ)
    {tau : ℝ} (htau : 0 < tau)
    (hR : ∀ᶠ n in phi, 0 ≤ R n)
    (henvelope : Tendsto
      (fun n ↦ ((A n).natDegree : ℝ) *
        (tau⁻¹ * Real.exp (-((R n) ^ 2 * tau))))
      phi (nhds 0)) :
    Tendsto
      (fun n ↦ realPolynomialUpperHeatTailOutsideClosedBall
        (A n) z (R n) tau)
      phi (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    exact realPolynomialUpperHeatTailOutsideClosedBall_nonneg
      (A n) hz (R n) htau
  · filter_upwards [hR] with n hRn
    exact realPolynomialUpperHeatTailOutsideClosedBall_le_degreeGaussian
      (A n) z hRn htau
  · exact henvelope

/-- If every unused upper-root occurrence is radially separated from the
observation point, the exact cluster complement is a submultiset of the
radial tail. -/
theorem realPolynomialUpperRootRemainderOutsideBalls_le_outsideClosedBall
    {iota : Type*} [Fintype iota] (A : ℝ[X])
    (a : iota → ℂ) (r : iota → ℝ) (z : ℂ) (R : ℝ)
    (hdist : ∀ alpha ∈
      realPolynomialUpperRootMultiset A -
        ∑ i : iota, realPolynomialRootMultisetInBall A (a i) (r i),
      R ≤ dist z alpha) :
    realPolynomialUpperRootMultiset A -
        ∑ i : iota, realPolynomialRootMultisetInBall A (a i) (r i) ≤
      realPolynomialUpperRootMultisetOutsideClosedBall A z R := by
  unfold realPolynomialUpperRootMultisetOutsideClosedBall
  rw [Multiset.le_filter]
  exact ⟨Multiset.sub_le_self _ _, hdist⟩

/-- Under the same radial separation, the exact cluster-complement heat is
dominated by the radial heat tail. -/
theorem realPolynomialUpperHeatRemainderOutsideBalls_le_tail
    {iota : Type*} [Fintype iota] (A : ℝ[X])
    (a : iota → ℂ) (r : iota → ℝ) {z : ℂ} (hz : 0 < z.im)
    (R : ℝ) {tau : ℝ} (htau : 0 < tau)
    (hdist : ∀ alpha ∈
      realPolynomialUpperRootMultiset A -
        ∑ i : iota, realPolynomialRootMultisetInBall A (a i) (r i),
      R ≤ dist z alpha) :
    realPolynomialUpperHeatRemainderOutsideBalls A a r z tau ≤
      realPolynomialUpperHeatTailOutsideClosedBall A z R tau := by
  apply finiteUpperHyperbolicHeatSum_mono hz
  · exact
      realPolynomialUpperRootRemainderOutsideBalls_le_outsideClosedBall
        A a r z R hdist
  · intro alpha halpha
    exact realPolynomialUpperRootMultiset_im_pos A alpha
      (Multiset.mem_of_le (Multiset.filter_le _ _) halpha)
  · exact htau

/-- The unused upper roots outside selected clusters obey a degree-weighted
Gaussian estimate whenever they are all at least `R` from the observation
point. -/
theorem realPolynomialUpperHeatRemainderOutsideBalls_le_degreeGaussian
    {iota : Type*} [Fintype iota] (A : ℝ[X])
    (a : iota → ℂ) (r : iota → ℝ) (z : ℂ)
    {tau R : ℝ} (htau : 0 < tau) (hR : 0 ≤ R)
    (hdist : ∀ alpha ∈
      realPolynomialUpperRootMultiset A -
        ∑ i : iota, realPolynomialRootMultisetInBall A (a i) (r i),
      R ≤ dist z alpha) :
    realPolynomialUpperHeatRemainderOutsideBalls A a r z tau ≤
      (A.natDegree : ℝ) *
        (tau⁻¹ * Real.exp (-(R ^ 2 * tau))) := by
  let unused := realPolynomialUpperRootMultiset A -
    ∑ i : iota, realPolynomialRootMultisetInBall A (a i) (r i)
  let C := tau⁻¹ * Real.exp (-(R ^ 2 * tau))
  have hsum : finiteUpperHyperbolicHeatSum z unused tau ≤
      (unused.card : ℝ) * C :=
    finiteUpperHyperbolicHeatSum_le_card_mul_radialGaussian
      z unused htau hR hdist
  have hcard : unused.card ≤ A.natDegree :=
    (Multiset.card_le_card (Multiset.sub_le_self _ _)).trans
      (realPolynomialUpperRootMultiset_card_le_natDegree A)
  have hC : 0 ≤ C := by
    exact mul_nonneg (inv_nonneg.mpr htau.le) (Real.exp_pos _).le
  calc
    realPolynomialUpperHeatRemainderOutsideBalls A a r z tau =
        finiteUpperHyperbolicHeatSum z unused tau := rfl
    _ ≤ (unused.card : ℝ) * C := hsum
    _ ≤ (A.natDegree : ℝ) * C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC

/-- The exact unused-root heat remainder vanishes if a separating radius
makes its degree-weighted Gaussian envelope vanish. -/
theorem tendsto_realPolynomialUpperHeatRemainderOutsideBalls_zero_of_degreeGaussian
    {kappa iota : Type*} {phi : Filter kappa} [Fintype iota]
    (A : kappa → ℝ[X]) (a : kappa → iota → ℂ)
    (r : kappa → iota → ℝ) {z : ℂ} (hz : 0 < z.im)
    {tau : ℝ} (htau : 0 < tau) (R : kappa → ℝ)
    (hR : ∀ᶠ n in phi, 0 ≤ R n)
    (hdist : ∀ᶠ n in phi, ∀ alpha ∈
      realPolynomialUpperRootMultiset (A n) -
        ∑ i : iota,
          realPolynomialRootMultisetInBall (A n) (a n i) (r n i),
      R n ≤ dist z alpha)
    (henvelope : Tendsto
      (fun n ↦ ((A n).natDegree : ℝ) *
        (tau⁻¹ * Real.exp (-((R n) ^ 2 * tau))))
      phi (nhds 0)) :
    Tendsto
      (fun n ↦ realPolynomialUpperHeatRemainderOutsideBalls
        (A n) (a n) (r n) z tau)
      phi (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    exact realPolynomialUpperHeatRemainderOutsideBalls_nonneg
      (A n) (a n) (r n) hz htau
  · filter_upwards [hR, hdist] with n hRn hdistn
    exact realPolynomialUpperHeatRemainderOutsideBalls_le_degreeGaussian
      (A n) (a n) (r n) z htau hRn hdistn
  · exact henvelope

end

end RiemannGaussian

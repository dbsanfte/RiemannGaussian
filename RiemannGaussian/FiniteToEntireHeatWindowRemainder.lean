import RiemannGaussian.FiniteToEntireBoundedHeat
import RiemannGaussian.FiniteToEntireFullDivisorHeat

/-!
# Bounded xi heat windows inside full polynomial heat divisors

This file makes the remaining finite-to-entire tail problem exact.  Isolating
balls around upper spectral-xi zeros are chosen wholly inside the upper half
plane.  Their polynomial root clusters are therefore genuine submultisets of
the complete upper polynomial divisor, with every algebraic multiplicity
retained.

At fixed positive proper time, the full polynomial heat sum splits exactly
into the cluster sum converging to the chosen xi window and a nonnegative
remainder over all unused upper roots.  Consequently convergence of the full
polynomial heat sums to any candidate limit `L` is equivalent to convergence
of this remainder to `L` minus the xi window.  For the complete xi heat sum,
this is precisely the spectral tail outside the chosen window.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- Pairwise disjoint filters of one multiset add to a submultiset of the
original, including multiplicities. -/
theorem finset_sum_filter_le_of_pairwiseDisjoint
    {alpha iota : Type*} [DecidableEq alpha]
    (s : Multiset alpha) (S : Finset iota) (U : iota → Set alpha)
    (hdisjoint : (S : Set iota).PairwiseDisjoint U) :
    (∑ i ∈ S, s.filter fun x ↦ x ∈ U i) ≤ s := by
  rw [Multiset.le_iff_count]
  intro x
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Multiset.count_add]
      have htail : (S : Set iota).PairwiseDisjoint U := by
        intro j hj k hk hjk
        exact hdisjoint (by simp [hj]) (by simp [hk]) hjk
      by_cases hxi : x ∈ U i
      · have hother : ∀ j ∈ S, x ∉ U j := by
          intro j hj hxj
          have hij : i ≠ j := by
            intro hij
            subst j
            exact hi hj
          have hsets : Disjoint (U i) (U j) :=
            hdisjoint (by simp) (by simp [hj]) hij
          exact Set.disjoint_left.mp hsets hxi hxj
        have htailzero :
            Multiset.count x
              (∑ j ∈ S, s.filter fun y ↦ y ∈ U j) = 0 := by
          rw [Multiset.count_eq_zero]
          rw [Multiset.mem_sum]
          rintro ⟨j, hj, hxfilter⟩
          exact hother j hj (Multiset.mem_filter.mp hxfilter).2
        rw [htailzero]
        simp [hxi]
      · rw [Multiset.count_filter, if_neg hxi, zero_add]
        exact ih htail

/-- The multiplicity-counted complex roots of a real polynomial in an open
ball. -/
def realPolynomialRootMultisetInBall
    (A : ℝ[X]) (a : ℂ) (R : ℝ) : Multiset ℂ :=
  (A.map Complex.ofRealHom).roots.filter fun w ↦ w ∈ ball a R

/-- An open ball whose radius does not exceed its center's height lies in the
open upper half-plane. -/
theorem im_pos_of_mem_ball_of_radius_le_im
    {a w : ℂ} {R : ℝ} (hR : R ≤ a.im) (hw : w ∈ ball a R) :
    0 < w.im := by
  have hdist : dist w a < R := mem_ball.mp hw
  have habs : |(w - a).im| ≤ ‖w - a‖ := Complex.abs_im_le_norm _
  have hnorm : ‖w - a‖ = dist w a := by
    rw [dist_eq_norm]
  have hdiff : a.im - w.im ≤ dist w a := by
    rw [← hnorm]
    rw [Complex.sub_im, abs_sub_comm] at habs
    exact (le_abs_self (a.im - w.im)).trans habs
  linarith

/-- Every polynomial root in such an upper ball is an occurrence in the
canonical upper root multiset. -/
theorem realPolynomialRootMultisetInBall_le_upper
    (A : ℝ[X]) {a : ℂ} {R : ℝ} (hR : R ≤ a.im) :
    realPolynomialRootMultisetInBall A a R ≤
      realPolynomialUpperRootMultiset A := by
  exact Multiset.monotone_filter_right _ fun w hw ↦
    im_pos_of_mem_ball_of_radius_le_im hR hw

/-- Root clusters cut out by pairwise disjoint upper balls form a submultiset
of the complete upper polynomial divisor. -/
theorem sum_realPolynomialRootMultisetInBalls_le_upper
    {iota : Type*} [Fintype iota] (A : ℝ[X])
    (a : iota → ℂ) (R : iota → ℝ)
    (hR : ∀ i, R i ≤ (a i).im)
    (hdisjoint : (Set.univ : Set iota).PairwiseDisjoint
      fun i ↦ ball (a i) (R i)) :
    (∑ i : iota, realPolynomialRootMultisetInBall A (a i) (R i)) ≤
      realPolynomialUpperRootMultiset A := by
  let roots := (A.map Complex.ofRealHom).roots
  have hleRoots :
      (∑ i : iota, roots.filter fun w ↦ w ∈ ball (a i) (R i)) ≤ roots := by
    apply finset_sum_filter_le_of_pairwiseDisjoint
      roots Finset.univ (fun i ↦ ball (a i) (R i))
    simpa using hdisjoint
  unfold realPolynomialUpperRootMultiset
  rw [Multiset.le_filter]
  refine ⟨?_, ?_⟩
  · simpa [realPolynomialRootMultisetInBall, roots,
      realPolynomialUpperRootMultiset] using hleRoots
  · intro w hw
    rw [Multiset.mem_sum] at hw
    obtain ⟨i, _, hwi⟩ := hw
    exact im_pos_of_mem_ball_of_radius_le_im (hR i)
      (Multiset.of_mem_filter hwi)

/-- The sum of the cluster heat weights is the finite heat sum over the
combined multiplicity-counted cluster multiset. -/
theorem sum_realPolynomialRootWeightedSumInBall_eq_heatSum
    {iota : Type*} [Fintype iota] (A : ℝ[X])
    (a : iota → ℂ) (R : iota → ℝ) (z : ℂ) (tau : ℝ) :
    (∑ i : iota,
      realPolynomialRootWeightedSumInBall A (a i) (R i)
        (fun alpha ↦ upperHalfPlaneHyperbolicHeatIntegrand z alpha tau)) =
      finiteUpperHyperbolicHeatSum z
        (∑ i : iota,
          realPolynomialRootMultisetInBall A (a i) (R i)) tau := by
  change
    (∑ i : iota,
      ((realPolynomialRootMultisetInBall A (a i) (R i)).map
        (fun alpha ↦ upperHalfPlaneHyperbolicHeatIntegrand z alpha tau)).sum) =
      (((∑ i : iota,
        realPolynomialRootMultisetInBall A (a i) (R i)).map
        (fun alpha ↦ upperHalfPlaneHyperbolicHeatIntegrand z alpha tau)).sum)
  let W := fun alpha ↦ upperHalfPlaneHyperbolicHeatIntegrand z alpha tau
  let roots := fun i ↦ realPolynomialRootMultisetInBall A (a i) (R i)
  calc
    (∑ i : iota, ((roots i).map W).sum) =
        (∑ i : iota, (roots i).map W).sum :=
      (map_sum Multiset.sumAddMonoidHom
        (fun i ↦ (roots i).map W) Finset.univ).symm
    _ = ((∑ i : iota, roots i).map W).sum := by
      congr 1
      exact (map_sum (Multiset.mapAddMonoidHom W)
        roots Finset.univ).symm

/-- At positive proper time, disjoint upper cluster heat is dominated by the
complete polynomial upper-divisor heat sum. -/
theorem sum_realPolynomialRootWeightedSumInBall_le_upperHeatSum
    {iota : Type*} [Fintype iota] (A : ℝ[X])
    (a : iota → ℂ) (R : iota → ℝ)
    (hR : ∀ i, R i ≤ (a i).im)
    (hdisjoint : (Set.univ : Set iota).PairwiseDisjoint
      fun i ↦ ball (a i) (R i))
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    (∑ i : iota,
      realPolynomialRootWeightedSumInBall A (a i) (R i)
        (fun alpha ↦ upperHalfPlaneHyperbolicHeatIntegrand z alpha tau)) ≤
      realPolynomialUpperHyperbolicHeatSum A z tau := by
  rw [sum_realPolynomialRootWeightedSumInBall_eq_heatSum]
  exact finiteUpperHyperbolicHeatSum_mono hz
    (sum_realPolynomialRootMultisetInBalls_le_upper A a R hR hdisjoint)
    (realPolynomialUpperRootMultiset_im_pos A) htau

/-- The fixed-time heat carried by upper polynomial root occurrences outside
a prescribed finite family of disjoint root clusters. -/
def realPolynomialUpperHeatRemainderOutsideBalls
    {iota : Type*} [Fintype iota] (A : ℝ[X])
    (a : iota → ℂ) (R : iota → ℝ) (z : ℂ) (tau : ℝ) : ℝ :=
  finiteUpperHyperbolicHeatSum z
    (realPolynomialUpperRootMultiset A -
      ∑ i : iota, realPolynomialRootMultisetInBall A (a i) (R i)) tau

/-- The complete polynomial heat sum splits exactly into selected cluster
heat and the unused-upper-root remainder. -/
theorem realPolynomialUpperHeatSum_eq_clusters_add_remainder
    {iota : Type*} [Fintype iota] (A : ℝ[X])
    (a : iota → ℂ) (R : iota → ℝ)
    (hR : ∀ i, R i ≤ (a i).im)
    (hdisjoint : (Set.univ : Set iota).PairwiseDisjoint
      fun i ↦ ball (a i) (R i))
    (z : ℂ) (tau : ℝ) :
    realPolynomialUpperHyperbolicHeatSum A z tau =
      (∑ i : iota,
        realPolynomialRootWeightedSumInBall A (a i) (R i)
          (fun alpha ↦
            upperHalfPlaneHyperbolicHeatIntegrand z alpha tau)) +
        realPolynomialUpperHeatRemainderOutsideBalls
          A a R z tau := by
  let clusters := ∑ i : iota,
    realPolynomialRootMultisetInBall A (a i) (R i)
  have hle : clusters ≤ realPolynomialUpperRootMultiset A :=
    sum_realPolynomialRootMultisetInBalls_le_upper A a R hR hdisjoint
  have hdecomp :
      realPolynomialUpperRootMultiset A =
        (realPolynomialUpperRootMultiset A - clusters) + clusters :=
    (Multiset.sub_add_cancel hle).symm
  rw [sum_realPolynomialRootWeightedSumInBall_eq_heatSum]
  change finiteUpperHyperbolicHeatSum z
      (realPolynomialUpperRootMultiset A) tau =
    finiteUpperHyperbolicHeatSum z clusters tau +
      finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultiset A - clusters) tau
  rw [hdecomp]
  simp [finiteUpperHyperbolicHeatSum, add_comm]

/-- Every positive-time unused-upper-root heat remainder is nonnegative. -/
theorem realPolynomialUpperHeatRemainderOutsideBalls_nonneg
    {iota : Type*} [Fintype iota] (A : ℝ[X])
    (a : iota → ℂ) (R : iota → ℝ)
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    0 ≤ realPolynomialUpperHeatRemainderOutsideBalls
      A a R z tau := by
  apply finiteUpperHyperbolicHeatSum_nonneg hz
  intro alpha halpha
  exact realPolynomialUpperRootMultiset_im_pos A alpha
    (Multiset.mem_of_le (Multiset.sub_le_self _ _) halpha)
  exact htau

/-- A finite xi divisor admits pairwise disjoint heat-transport balls below
any prescribed family of positive radius bounds. -/
theorem exists_pairwiseDisjoint_finite_riemannXiSpectral_polynomialHeat_tendsto_lt
    {iota : Type*} {phi : Filter iota} [phi.NeBot]
    [phi.IsCountablyGenerated]
    (A : iota → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    (z : ℂ) (tau : ℝ) (S : Finset NontrivialZetaZero)
    (rBound : S → ℝ) (hrBound : ∀ rho : S, 0 < rBound rho) :
    ∃ R : S → ℝ,
      (∀ rho : S, 0 < R rho ∧ R rho < rBound rho ∧
        ∀ w ∈ closedBall (zetaSpectralCoordinate rho.1.1) (R rho),
          w ≠ zetaSpectralCoordinate rho.1.1 →
            riemannXiSpectral w ≠ 0) ∧
      (Set.univ : Set S).PairwiseDisjoint (fun rho : S ↦
        closedBall (zetaSpectralCoordinate rho.1.1) (R rho)) ∧
      Tendsto
        (fun n ↦ ∑ rho : S,
          realPolynomialRootWeightedSumInBall (A n)
            (zetaSpectralCoordinate rho.1.1) (R rho)
            (fun alpha ↦
              upperHalfPlaneHyperbolicHeatIntegrand z alpha tau))
        phi
        (nhds (∑ rho : S,
          (analyticZetaZeroMultiplicity rho.1 : ℝ) *
            upperHalfPlaneHyperbolicHeatIntegrand z
              (zetaSpectralCoordinate rho.1.1) tau)) := by
  let center : S → ℂ := fun rho ↦ zetaSpectralCoordinate rho.1.1
  have hcenterInj : Function.Injective center := by
    intro rho sigma hcenter
    apply Subtype.ext
    apply Subtype.ext
    exact zetaSpectralCoordinate_injective hcenter
  obtain ⟨U, hU, hUdisjoint⟩ :=
    (Set.finite_range center).t2_separation
  have hexBall (rho : S) :
      ∃ r : ℝ, 0 < r ∧ ball (center rho) r ⊆ U (center rho) := by
    exact (Metric.isOpen_iff.mp (hU (center rho)).2)
      (center rho) (hU (center rho)).1
  choose r hr hball using hexBall
  have hbound (rho : S) : 0 < min (r rho) (rBound rho) :=
    lt_min (hr rho) (hrBound rho)
  have hex (rho : S) :
      ∃ R : ℝ, 0 < R ∧ R < min (r rho) (rBound rho) ∧
        (∀ w ∈ closedBall (center rho) R, w ≠ center rho →
          riemannXiSpectral w ≠ 0) ∧
        Tendsto
          (fun n ↦ realPolynomialRootWeightedSumInBall (A n)
            (center rho) R
            (fun alpha ↦
              upperHalfPlaneHyperbolicHeatIntegrand z alpha tau))
          phi
          (nhds ((analyticZetaZeroMultiplicity rho.1 : ℝ) *
            upperHalfPlaneHyperbolicHeatIntegrand z (center rho) tau)) :=
    exists_lt_riemannXiSpectral_localPolynomialHeat_tendsto
      A hA z tau rho.1 (hbound rho)
  choose R hR hRlt hzero hLimit using hex
  refine ⟨R, ?_, ?_, ?_⟩
  · intro rho
    exact ⟨hR rho, (hRlt rho).trans_le (min_le_right _ _), hzero rho⟩
  · intro rho _ sigma _ hrs
    have hcenters : center rho ≠ center sigma := hcenterInj.ne hrs
    have hdisjoint : Disjoint (U (center rho)) (U (center sigma)) :=
      hUdisjoint (Set.mem_range_self rho) (Set.mem_range_self sigma)
        hcenters
    apply hdisjoint.mono
    · exact (closedBall_subset_ball
        ((hRlt rho).trans_le (min_le_left _ _))).trans (hball rho)
    · exact (closedBall_subset_ball
        ((hRlt sigma).trans_le (min_le_left _ _))).trans (hball sigma)
  · simpa [center] using
      tendsto_finsetSum Finset.univ (fun rho _ ↦ hLimit rho)

/-- The exact fixed-window transport package: upper isolating balls, literal
cluster convergence, full-divisor decomposition with nonnegative remainder,
and equivalence between every candidate full limit and its forced remainder
limit. -/
def RiemannXiUpperHeatWindowPolynomialRemainderTransport
    {iota : Type*} (phi : Filter iota) (A : iota → ℝ[X])
    (z : ℂ) (tau T : ℝ) : Prop :=
  ∃ R : upperSpectralZetaZeroWindow T → ℝ,
    (∀ rho : upperSpectralZetaZeroWindow T, 0 < R rho ∧
      R rho < (zetaSpectralCoordinate rho.1.1).im ∧
      ∀ w ∈ closedBall
          (zetaSpectralCoordinate rho.1.1) (R rho),
        w ≠ zetaSpectralCoordinate rho.1.1 →
          riemannXiSpectral w ≠ 0) ∧
    (Set.univ : Set (upperSpectralZetaZeroWindow T)).PairwiseDisjoint
      (fun rho ↦ closedBall
        (zetaSpectralCoordinate rho.1.1) (R rho)) ∧
    Tendsto
      (fun n ↦ ∑ rho : upperSpectralZetaZeroWindow T,
        realPolynomialRootWeightedSumInBall (A n)
          (zetaSpectralCoordinate rho.1.1) (R rho)
          (fun alpha ↦
            upperHalfPlaneHyperbolicHeatIntegrand z alpha tau))
      phi (nhds (riemannXiUpperHyperbolicHeatWindow z tau T)) ∧
    (∀ n,
        realPolynomialUpperHyperbolicHeatSum (A n) z tau =
            (∑ rho : upperSpectralZetaZeroWindow T,
              realPolynomialRootWeightedSumInBall (A n)
                (zetaSpectralCoordinate rho.1.1) (R rho)
                (fun alpha ↦
                  upperHalfPlaneHyperbolicHeatIntegrand z alpha tau)) +
              realPolynomialUpperHeatRemainderOutsideBalls (A n)
                (fun rho ↦ zetaSpectralCoordinate rho.1.1) R z tau ∧
          0 ≤ realPolynomialUpperHeatRemainderOutsideBalls (A n)
            (fun rho ↦ zetaSpectralCoordinate rho.1.1) R z tau) ∧
    ∀ L : ℝ,
      Tendsto
          (fun n ↦ realPolynomialUpperHyperbolicHeatSum (A n) z tau)
          phi (nhds L) ↔
        Tendsto
          (fun n ↦ realPolynomialUpperHeatRemainderOutsideBalls (A n)
            (fun rho ↦ zetaSpectralCoordinate rho.1.1) R z tau)
          phi (nhds (L - riemannXiUpperHyperbolicHeatWindow z tau T))

/-- Every fixed upper spectral-xi window is transported by literal upper
polynomial root clusters.  The complete polynomial heat sum is exactly the
convergent cluster part plus a nonnegative unused-root remainder, and full-sum
convergence to any candidate is equivalent to the corresponding forced
remainder limit. -/
theorem exists_riemannXiUpperHeatWindow_polynomial_tendsto_with_remainder
    {iota : Type*} {phi : Filter iota} [phi.NeBot]
    [phi.IsCountablyGenerated]
    (A : iota → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) (T : ℝ) :
    RiemannXiUpperHeatWindowPolynomialRemainderTransport
      phi A z tau T := by
  unfold RiemannXiUpperHeatWindowPolynomialRemainderTransport
  let S := upperSpectralZetaZeroWindow T
  have hupper (rho : S) :
      0 < (zetaSpectralCoordinate rho.1.1).im := by
    exact (Finset.mem_filter.mp rho.2).2
  obtain ⟨R, hR, hdisjoint, hLimit⟩ :=
    exists_pairwiseDisjoint_finite_riemannXiSpectral_polynomialHeat_tendsto_lt
      A hA z tau S (fun rho ↦
        (zetaSpectralCoordinate rho.1.1).im) hupper
  refine ⟨R, hR, hdisjoint, ?_, ?_, ?_⟩
  · rw [← sum_upperSpectralZetaZeroWindow_heat_eq]
    exact hLimit
  · intro n
    have hballDisjoint : (Set.univ : Set S).PairwiseDisjoint
        (fun rho ↦ ball (zetaSpectralCoordinate rho.1.1) (R rho)) :=
      hdisjoint.mono fun rho ↦ ball_subset_closedBall
    exact ⟨realPolynomialUpperHeatSum_eq_clusters_add_remainder (A n)
        (fun rho : S ↦ zetaSpectralCoordinate rho.1.1) R
        (fun rho ↦ (hR rho).2.1.le) hballDisjoint z tau,
      realPolynomialUpperHeatRemainderOutsideBalls_nonneg (A n)
        (fun rho : S ↦ zetaSpectralCoordinate rho.1.1) R hz htau⟩
  · let C : iota → ℝ := fun n ↦
      ∑ rho : S,
        realPolynomialRootWeightedSumInBall (A n)
          (zetaSpectralCoordinate rho.1.1) (R rho)
          (fun alpha ↦
            upperHalfPlaneHyperbolicHeatIntegrand z alpha tau)
    let D : iota → ℝ := fun n ↦
      realPolynomialUpperHeatRemainderOutsideBalls (A n)
        (fun rho : S ↦ zetaSpectralCoordinate rho.1.1) R z tau
    have hC : Tendsto C phi
        (nhds (riemannXiUpperHyperbolicHeatWindow z tau T)) := by
      rw [← sum_upperSpectralZetaZeroWindow_heat_eq]
      simpa [C, S] using hLimit
    have hsum (n : iota) :
        realPolynomialUpperHyperbolicHeatSum (A n) z tau = C n + D n :=
      realPolynomialUpperHeatSum_eq_clusters_add_remainder (A n)
        (fun rho : S ↦ zetaSpectralCoordinate rho.1.1) R
        (fun rho ↦ (hR rho).2.1.le)
        (hdisjoint.mono fun rho ↦ ball_subset_closedBall) z tau
    intro L
    constructor
    · intro hfull
      have hdiff := hfull.sub hC
      have hfun :
          (fun n ↦ realPolynomialUpperHyperbolicHeatSum (A n) z tau -
            C n) = D := by
        funext n
        rw [hsum n]
        ring
      simpa only [hfun] using hdiff
    · intro hD
      have hD' : Tendsto D phi
          (nhds (L - riemannXiUpperHyperbolicHeatWindow z tau T)) := by
        simpa [D, S] using hD
      have hadd := hC.add hD'
      have hfun :
          (fun n ↦ C n + D n) =
            (fun n ↦ realPolynomialUpperHyperbolicHeatSum (A n) z tau) := by
        funext n
        exact (hsum n).symm
      have htarget :
          riemannXiUpperHyperbolicHeatWindow z tau T +
              (L - riemannXiUpperHyperbolicHeatWindow z tau T) = L := by
        ring
      simpa only [hfun, htarget] using hadd

/-- Under failure of RH, the same root-pinned canonical Hardy sequence has
the exact nonnegative-remainder transport package for every upper observation
point, positive proper time, and finite spectral window. -/
theorem exists_canonicalFiniteHardyFrontier_upperHeatWindowRemainders_of_not_rh
    (hRH : ¬RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z0 : ℂ, 0 < z0.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z0) ∧
        ∀ (z : ℂ), 0 < z.im → ∀ (tau : ℝ), 0 < tau → ∀ T : ℝ,
          RiemannXiUpperHeatWindowPolynomialRemainderTransport
            atTop B z tau T := by
  obtain ⟨eta, heta, z0, hz0, B, hB, hfrontier⟩ :=
    exists_canonicalFiniteHardyFrontier_sequence_of_not_rh hRH
  refine ⟨eta, heta, z0, hz0, B, hB, hfrontier, ?_⟩
  intro z hz tau htau T
  exact exists_riemannXiUpperHeatWindow_polynomial_tendsto_with_remainder
    B hB hz htau T

end

end RiemannGaussian

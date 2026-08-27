import RiemannGaussian.FiniteToEntireRadialAnnulus

/-!
# Fixed radial-shell heat transport

This file transports every fixed radial shell of a locally uniformly
convergent real-polynomial sequence to the matching spectral-xi shell.  The
upper-half-plane cutoff is handled without assuming roots stay away from the
real axis: the positive part of the hyperbolic heat integrand is continuous,
equals the integrand on upper roots, and vanishes on real and lower roots.

Consequently continuous weighted-divisor convergence can be applied to the
complete polynomial root multiset.  Exact radial root counts then exclude
every spurious root in a fixed zero-free disk, with algebraic multiplicity,
and subtraction of nested disks gives the annular limit.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The continuous positive part of the hyperbolic heat integrand. -/
def upperHalfPlanePositivePartHeatIntegrand
    (z alpha : ℂ) (tau : ℝ) : ℝ :=
  max (upperHalfPlaneHyperbolicHeatIntegrand z alpha tau) 0

/-- The positive-part heat weight is continuous in the divisor point,
including across the real axis. -/
theorem continuous_upperHalfPlanePositivePartHeatIntegrand
    (z : ℂ) (tau : ℝ) :
    Continuous fun alpha : ℂ ↦
      upperHalfPlanePositivePartHeatIntegrand z alpha tau := by
  unfold upperHalfPlanePositivePartHeatIntegrand
    upperHalfPlaneHyperbolicHeatIntegrand
  simp only [Complex.normSq_apply]
  fun_prop

/-- At positive proper time and positive observation height, the heat
integrand is nonpositive at every real or lower-half-plane divisor point. -/
theorem upperHalfPlaneHyperbolicHeatIntegrand_nonpos_of_im_nonpos
    {z alpha : ℂ} {tau : ℝ} (hz : 0 < z.im)
    (halpha : alpha.im ≤ 0) (htau : 0 < tau) :
    upperHalfPlaneHyperbolicHeatIntegrand z alpha tau ≤ 0 := by
  rw [upperHalfPlaneHyperbolicHeatIntegrand_eq_pair,
    pairHyperbolicHeatIntegrand_eq_gaussian_sinh]
  have hcoefficient : 0 ≤ 2 * tau * z.im := by positivity
  have hsinh : Real.sinh (2 * tau * z.im * alpha.im) ≤ 0 :=
    Real.sinh_nonpos_iff.mpr
      (mul_nonpos_of_nonneg_of_nonpos hcoefficient halpha)
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hsinh

/-- The positive-part weight is the original heat weight at an upper point. -/
theorem upperHalfPlanePositivePartHeatIntegrand_eq_of_im_pos
    {z alpha : ℂ} {tau : ℝ} (hz : 0 < z.im)
    (halpha : 0 < alpha.im) (htau : 0 < tau) :
    upperHalfPlanePositivePartHeatIntegrand z alpha tau =
      upperHalfPlaneHyperbolicHeatIntegrand z alpha tau := by
  rw [upperHalfPlanePositivePartHeatIntegrand, max_eq_left]
  exact (upperHalfPlaneHyperbolicHeatIntegrand_pos hz halpha htau).le

/-- The positive-part weight vanishes at every real or lower point. -/
theorem upperHalfPlanePositivePartHeatIntegrand_eq_zero_of_im_nonpos
    {z alpha : ℂ} {tau : ℝ} (hz : 0 < z.im)
    (halpha : alpha.im ≤ 0) (htau : 0 < tau) :
    upperHalfPlanePositivePartHeatIntegrand z alpha tau = 0 := by
  rw [upperHalfPlanePositivePartHeatIntegrand, max_eq_right]
  exact upperHalfPlaneHyperbolicHeatIntegrand_nonpos_of_im_nonpos
    hz halpha htau

/-- Summing the continuous positive-part weight over any complex multiset is
exactly the original heat sum over its upper-half-plane submultiset. -/
theorem multiset_sum_map_positivePartHeat_eq_filter_im_pos
    (s : Multiset ℂ) {z : ℂ} (hz : 0 < z.im)
    {tau : ℝ} (htau : 0 < tau) :
    (s.map fun alpha ↦
        upperHalfPlanePositivePartHeatIntegrand z alpha tau).sum =
      ((s.filter fun alpha ↦ 0 < alpha.im).map fun alpha ↦
        upperHalfPlaneHyperbolicHeatIntegrand z alpha tau).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons alpha s ih =>
      by_cases halpha : 0 < alpha.im
      · simp [halpha, ih,
          upperHalfPlanePositivePartHeatIntegrand_eq_of_im_pos
            hz halpha htau]
      · have halphaNonpos : alpha.im ≤ 0 := le_of_not_gt halpha
        simp [halpha, ih,
          upperHalfPlanePositivePartHeatIntegrand_eq_zero_of_im_nonpos
            hz halphaNonpos htau]

/-- In a radial disk, the complete root multiset carrying the continuous
positive-part weight is exactly the upper-root heat sum. -/
theorem realPolynomialRootPositivePartHeatSumInBall_eq_upperHeat
    (A : ℝ[X]) (R : ℝ) {z : ℂ} (hz : 0 < z.im)
    {tau : ℝ} (htau : 0 < tau) :
    realPolynomialRootWeightedSumInBall A 0 R
        (fun alpha ↦ upperHalfPlanePositivePartHeatIntegrand z alpha tau) =
      finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInsideBall A R) tau := by
  unfold realPolynomialRootWeightedSumInBall
    realPolynomialUpperRootMultisetInsideBall
    realPolynomialUpperRootMultiset finiteUpperHyperbolicHeatSum
  rw [multiset_sum_map_positivePartHeat_eq_filter_im_pos _ hz htau]
  rw [Multiset.filter_comm]

/-- In a radial annulus, the complete root multiset carrying the continuous
positive-part weight is exactly the upper-root heat sum. -/
theorem realPolynomialRootPositivePartHeatSumInRadialAnnulus_eq_upperHeat
    (A : ℝ[X]) (r R : ℝ) {z : ℂ} (hz : 0 < z.im)
    {tau : ℝ} (htau : 0 < tau) :
    ((realPolynomialRootMultisetInRadialAnnulus A r R).map fun alpha ↦
        upperHalfPlanePositivePartHeatIntegrand z alpha tau).sum =
      finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInRadialAnnulus A r R) tau := by
  unfold realPolynomialRootMultisetInRadialAnnulus
    realPolynomialUpperRootMultisetInRadialAnnulus
    realPolynomialUpperRootMultiset finiteUpperHyperbolicHeatSum
  rw [multiset_sum_map_positivePartHeat_eq_filter_im_pos _ hz htau]
  rw [Multiset.filter_comm]

/-- Upper roots in nested radial disks split exactly into the inner disk and
the intervening annulus, retaining every occurrence. -/
theorem upperRootMultisetInsideBall_add_upperRootMultisetInRadialAnnulus
    (A : ℝ[X]) {r R : ℝ} (hrR : r ≤ R) :
    realPolynomialUpperRootMultisetInsideBall A r +
        realPolynomialUpperRootMultisetInRadialAnnulus A r R =
      realPolynomialUpperRootMultisetInsideBall A R := by
  have h := congrArg (Multiset.filter fun w : ℂ ↦ 0 < w.im)
    (rootMultisetInBall_add_rootMultisetInRadialAnnulus A hrR)
  simpa [realPolynomialRootMultisetInBall,
    realPolynomialRootMultisetInRadialAnnulus,
    realPolynomialUpperRootMultisetInsideBall,
    realPolynomialUpperRootMultisetInRadialAnnulus,
    realPolynomialUpperRootMultiset, Multiset.filter_comm,
    and_comm, and_left_comm, and_assoc] using h

/-- Fixed-time upper heat is additive across nested radial disks. -/
theorem finiteUpperHeatInsideBall_add_annulus
    (A : ℝ[X]) {r R : ℝ} (hrR : r ≤ R)
    (z : ℂ) (tau : ℝ) :
    finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInsideBall A r) tau +
      finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInRadialAnnulus A r R) tau =
      finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInsideBall A R) tau := by
  have h := congrArg
    (fun s : Multiset ℂ ↦ finiteUpperHyperbolicHeatSum z s tau)
    (upperRootMultisetInsideBall_add_upperRootMultisetInRadialAnnulus A hrR)
  simpa [finiteUpperHyperbolicHeatSum] using h

/-- If one fixed outer ball already has the correct analytic multiplicity,
then every continuous root weight on that ball converges to the multiplicity
times its value at the limiting zero. -/
theorem AnalyticAt.realPolynomialRootWeightedSumInBall_tendsto_of_eventuallyEq_order
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X]) {f : ℂ → ℂ} {a : ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      f phi Set.univ)
    (hf : AnalyticAt ℂ f a) (hfinite : analyticOrderAt f a ≠ ⊤)
    {W : ℂ → ℝ} (hW : ContinuousAt W a)
    {R : ℝ} (hR : 0 < R)
    (hOuterCount : ∀ᶠ n in phi,
      realPolynomialRootCountInBall (A n) a R =
        analyticOrderNatAt f a) :
    Tendsto
      (fun n ↦ realPolynomialRootWeightedSumInBall (A n) a R W)
      phi (nhds ((analyticOrderNatAt f a : ℝ) * W a)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let m : ℕ := analyticOrderNatAt f a
  change ∀ᶠ n in phi,
    dist (realPolynomialRootWeightedSumInBall (A n) a R W)
      ((m : ℝ) * W a) < epsilon
  by_cases hm : m = 0
  · have htarget : (m : ℝ) * W a = 0 := by simp [hm]
    rw [htarget]
    filter_upwards [hOuterCount] with n hn
    have hcard :
        (((A n).map Complex.ofRealHom).roots.filter
          (fun w ↦ w ∈ ball a R)).card = 0 := by
      simpa [realPolynomialRootCountInBall, m] using hn.trans hm
    have hnil :
        ((A n).map Complex.ofRealHom).roots.filter
          (fun w ↦ w ∈ ball a R) = 0 :=
      Multiset.card_eq_zero.mp hcard
    change dist
      (((((A n).map Complex.ofRealHom).roots.filter
        fun w ↦ w ∈ ball a R).map W).sum) 0 < epsilon
    rw [hnil]
    simpa using hepsilon
  · have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hm)
    let tolerance : ℝ := epsilon / (2 * m)
    have htolerance : 0 < tolerance := by
      dsimp [tolerance]
      positivity
    have hWclose : ∀ᶠ w in nhds a,
        dist (W w) (W a) < tolerance :=
      (Metric.tendsto_nhds.mp hW.tendsto) tolerance htolerance
    obtain ⟨delta, hdelta, hdeltaSub⟩ :=
      Metric.mem_nhds_iff.mp hWclose
    have hbound : 0 < min R delta := lt_min hR hdelta
    obtain ⟨r, hr, hrBound, _, hInnerCount⟩ :=
      AnalyticAt.exists_lt_eventuallyEq_realPolynomialRootCountInBall_order
        A hA hf hfinite hbound
    have hrR : r ≤ R :=
      (le_of_lt hrBound).trans (min_le_left R delta)
    have hrDelta : r ≤ delta :=
      (le_of_lt hrBound).trans (min_le_right R delta)
    filter_upwards [hOuterCount, hInnerCount] with n hnOuter hnInner
    let roots := ((A n).map Complex.ofRealHom).roots
    let outer := roots.filter fun w ↦ w ∈ ball a R
    let inner := roots.filter fun w ↦ w ∈ ball a r
    have hcardOuter : outer.card = m := by
      simpa [outer, roots, realPolynomialRootCountInBall, m] using hnOuter
    have hcardInner : inner.card = m := by
      simpa [inner, roots, realPolynomialRootCountInBall, m] using hnInner
    have hinnerLe : inner ≤ outer := by
      exact Multiset.monotone_filter_right roots fun w hw ↦
        ball_subset_ball hrR hw
    have hinnerOuter : inner = outer :=
      Multiset.eq_of_le_of_card_le hinnerLe (by
        rw [hcardInner, hcardOuter])
    have hweightClose : ∀ w ∈ inner,
        |W w - W a| < tolerance := by
      intro w hw
      have hwBall : w ∈ ball a delta :=
        ball_subset_ball hrDelta (Multiset.of_mem_filter hw)
      simpa [Real.dist_eq] using hdeltaSub hwBall
    have hsumBound :
        (inner.map fun w ↦ |W w - W a|).sum ≤
          (inner.card : ℝ) * tolerance := by
      have hle := (inner.map fun w ↦ |W w - W a|).sum_le_card_nsmul
        tolerance (fun x hx ↦ by
          obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
          exact (hweightClose w hw).le)
      simpa [nsmul_eq_mul] using hle
    have hdiff :
        (inner.map W).sum - (m : ℝ) * W a =
          (inner.map fun w ↦ W w - W a).sum := by
      rw [multiset_sum_map_sub_const, hcardInner]
    rw [realPolynomialRootWeightedSumInBall]
    change dist (outer.map W).sum ((m : ℝ) * W a) < epsilon
    rw [← hinnerOuter, Real.dist_eq, hdiff]
    calc
      |(inner.map fun w ↦ W w - W a).sum| ≤
          (inner.map fun w ↦ |W w - W a|).sum := by
        simpa only [Multiset.map_map, Function.comp_apply] using
          (inner.map fun w ↦ W w - W a).abs_sum_le_sum_abs
      _ ≤ (inner.card : ℝ) * tolerance := hsumBound
      _ = (m : ℝ) * tolerance := by rw [hcardInner]
      _ = epsilon / 2 := by
        dsimp [tolerance]
        field_simp
      _ < epsilon := by linarith

/-- Pairwise-disjoint local root multisets fill an outer polynomial-root
multiset exactly as soon as their multiplicity counts add to the outer count. -/
theorem realPolynomialRootMultisetInBall_eq_sum_of_rootCounts
    {kappa : Type*} [Fintype kappa]
    (A : ℝ[X]) (c : ℂ) (R : ℝ) (center : kappa → ℂ) (r : kappa → ℝ)
    (hinside : ∀ i, closedBall (center i) (r i) ⊆ ball c R)
    (hdisjoint : (Set.univ : Set kappa).PairwiseDisjoint
      (fun i ↦ closedBall (center i) (r i)))
    (hcount : realPolynomialRootCountInBall A c R =
      ∑ i : kappa,
        realPolynomialRootCountInBall A (center i) (r i)) :
    realPolynomialRootMultisetInBall A c R =
      ∑ i : kappa,
        realPolynomialRootMultisetInBall A (center i) (r i) := by
  let roots := (A.map Complex.ofRealHom).roots
  have hdisjointOpen :
      (Set.univ : Set kappa).PairwiseDisjoint
        (fun i ↦ ball (center i) (r i)) :=
    hdisjoint.mono fun _ ↦ ball_subset_closedBall
  have hsumLeRoots :
      (∑ i : kappa, roots.filter fun w ↦ w ∈ ball (center i) (r i)) ≤
        roots := by
    simpa using finset_sum_filter_le_of_pairwiseDisjoint
      roots Finset.univ (fun i ↦ ball (center i) (r i))
        (by simpa using hdisjointOpen)
  have hsumLeOuter :
      (∑ i : kappa,
          realPolynomialRootMultisetInBall A (center i) (r i)) ≤
        realPolynomialRootMultisetInBall A c R := by
    unfold realPolynomialRootMultisetInBall
    rw [Multiset.le_filter]
    refine ⟨by simpa [roots] using hsumLeRoots, ?_⟩
    intro w hw
    rw [Multiset.mem_sum] at hw
    obtain ⟨i, _, hwi⟩ := hw
    exact hinside i (ball_subset_closedBall (Multiset.of_mem_filter hwi))
  symm
  apply Multiset.eq_of_le_of_card_le hsumLeOuter
  have hcard :
      (realPolynomialRootMultisetInBall A c R).card =
        (∑ i : kappa,
          realPolynomialRootMultisetInBall A (center i) (r i)).card := by
    simpa [realPolynomialRootCountInBall,
      realPolynomialRootMultisetInBall] using hcount
  exact hcard.le

/-- Across a positive zero-free radial circle, every continuous weighted sum
over the complete enclosed polynomial divisor converges to the genuine finite
spectral-xi divisor with analytic multiplicities. -/
theorem tendsto_realPolynomialRootWeightedSumInRadialBall
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    {R : ℝ} (hR : 0 < R)
    (hboundary : ∀ w ∈ sphere 0 R, riemannXiSpectral w ≠ 0)
    {W : ℂ → ℝ} (hW : Continuous W) :
    Tendsto
      (fun n ↦ realPolynomialRootWeightedSumInBall (A n) 0 R W)
      phi
      (nhds (∑ rho : spectralZetaZeroRadialWindow R,
        (analyticZetaZeroMultiplicity rho.1 : ℝ) *
          W (zetaSpectralCoordinate rho.1.1))) := by
  let S := spectralZetaZeroRadialWindow R
  obtain ⟨r, hr, hdisjoint, hcounts⟩ :=
    exists_pairwiseDisjoint_insideBall_simultaneous_radialRootCounts
      A hA hR
  have hOuterCount : ∀ᶠ n in phi,
      realPolynomialRootCountInBall (A n) 0 R =
        riemannXiSpectralRadialDivisorCount R :=
    eventuallyEq_realPolynomialRootCountInBall_radialDivisor
      A hA hR hboundary
  have hlocal (rho : S) :
      Tendsto
        (fun n ↦ realPolynomialRootWeightedSumInBall (A n)
          (zetaSpectralCoordinate rho.1.1) (r rho) W)
        phi
        (nhds ((analyticZetaZeroMultiplicity rho.1 : ℝ) *
          W (zetaSpectralCoordinate rho.1.1))) := by
    have hfinite : analyticOrderAt riemannXiSpectral
        (zetaSpectralCoordinate rho.1.1) ≠ ⊤ := by
      rw [analyticOrderAt_riemannXiSpectral_zetaSpectralCoordinate,
        analyticOrderAt_riemannXi_eq_riemannZeta]
      exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho.1
    have hcountOrder : ∀ᶠ n in phi,
        realPolynomialRootCountInBall (A n)
            (zetaSpectralCoordinate rho.1.1) (r rho) =
          analyticOrderNatAt riemannXiSpectral
            (zetaSpectralCoordinate rho.1.1) := by
      filter_upwards [hcounts] with n hn
      simpa only
        [analyticOrderNatAt_riemannXiSpectral_zetaSpectralCoordinate] using
          hn rho
    have hlimit :=
      AnalyticAt.realPolynomialRootWeightedSumInBall_tendsto_of_eventuallyEq_order
        A hA
        (analyticAt_riemannXiSpectral (zetaSpectralCoordinate rho.1.1))
        hfinite hW.continuousAt (hr rho).1 hcountOrder
    simpa only
      [analyticOrderNatAt_riemannXiSpectral_zetaSpectralCoordinate] using
        hlimit
  have hclusterLimit :
      Tendsto
        (fun n ↦ ∑ rho : S,
          realPolynomialRootWeightedSumInBall (A n)
            (zetaSpectralCoordinate rho.1.1) (r rho) W)
        phi
        (nhds (∑ rho : S,
          (analyticZetaZeroMultiplicity rho.1 : ℝ) *
            W (zetaSpectralCoordinate rho.1.1))) := by
    exact tendsto_finsetSum Finset.univ fun rho _ ↦ hlocal rho
  have hMultiplicitySum :
      (∑ rho : S, analyticZetaZeroMultiplicity rho.1) =
        riemannXiSpectralRadialDivisorCount R := by
    rw [riemannXiSpectralRadialDivisorCount]
    exact (Finset.sum_subtype
      (spectralZetaZeroRadialWindow R) (fun _ ↦ Iff.rfl)
      analyticZetaZeroMultiplicity).symm
  have hpartition : ∀ᶠ n in phi,
      realPolynomialRootMultisetInBall (A n) 0 R =
        ∑ rho : S, realPolynomialRootMultisetInBall (A n)
          (zetaSpectralCoordinate rho.1.1) (r rho) := by
    filter_upwards [hcounts, hOuterCount] with n hnCounts hnOuter
    apply realPolynomialRootMultisetInBall_eq_sum_of_rootCounts
      (A n) 0 R (fun rho : S ↦ zetaSpectralCoordinate rho.1.1) r
      (fun rho ↦ (hr rho).2.2) hdisjoint
    calc
      realPolynomialRootCountInBall (A n) 0 R =
          riemannXiSpectralRadialDivisorCount R := hnOuter
      _ = ∑ rho : S, analyticZetaZeroMultiplicity rho.1 :=
        hMultiplicitySum.symm
      _ = ∑ rho : S,
          realPolynomialRootCountInBall (A n)
            (zetaSpectralCoordinate rho.1.1) (r rho) := by
        apply Finset.sum_congr rfl
        intro rho _
        exact (hnCounts rho).symm
  apply hclusterLimit.congr'
  filter_upwards [hpartition] with n hn
  change
    (∑ rho : S,
      ((realPolynomialRootMultisetInBall (A n)
        (zetaSpectralCoordinate rho.1.1) (r rho)).map W).sum) =
      ((realPolynomialRootMultisetInBall (A n) 0 R).map W).sum
  rw [hn]
  change
    (∑ rho : S, Multiset.sumAddMonoidHom
      ((Multiset.mapAddMonoidHom W)
        (realPolynomialRootMultisetInBall (A n)
          (zetaSpectralCoordinate rho.1.1) (r rho)))) =
      Multiset.sumAddMonoidHom
        ((Multiset.mapAddMonoidHom W)
          (∑ rho : S, realPolynomialRootMultisetInBall (A n)
            (zetaSpectralCoordinate rho.1.1) (r rho)))
  rw [map_sum (Multiset.mapAddMonoidHom W)]
  rw [map_sum Multiset.sumAddMonoidHom]

/-- The genuine multiplicity-counted upper spectral-xi heat inside one open
radial disk.  Critical-line and lower spectral zeros contribute zero through
`zetaUpperHyperbolicHeatSummand`. -/
def riemannXiUpperHyperbolicHeatRadialWindow
    (z : ℂ) (tau R : ℝ) : ℝ :=
  ∑ rho : spectralZetaZeroRadialWindow R,
    zetaUpperHyperbolicHeatSummand z tau rho.1

/-- At a genuine spectral zero, multiplicity times the continuous
positive-part weight is exactly the existing upper spectral heat summand. -/
theorem analyticMultiplicity_mul_positivePartHeat_eq_zetaUpperSummand
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau)
    (rho : NontrivialZetaZero) :
    (analyticZetaZeroMultiplicity rho : ℝ) *
        upperHalfPlanePositivePartHeatIntegrand z
          (zetaSpectralCoordinate rho.1) tau =
      zetaUpperHyperbolicHeatSummand z tau rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [upperHalfPlanePositivePartHeatIntegrand_eq_of_im_pos
      hz hupper htau, zetaUpperHyperbolicHeatSummand, if_pos hupper]
  · rw [upperHalfPlanePositivePartHeatIntegrand_eq_zero_of_im_nonpos
      hz (le_of_not_gt hupper) htau,
      zetaUpperHyperbolicHeatSummand, if_neg hupper]
    simp

/-- The radial sum of multiplicity-weighted positive-part heat terms is the
upper spectral radial heat window. -/
theorem sum_positivePartHeat_radialWindow_eq
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) (R : ℝ) :
    (∑ rho : spectralZetaZeroRadialWindow R,
      (analyticZetaZeroMultiplicity rho.1 : ℝ) *
        upperHalfPlanePositivePartHeatIntegrand z
          (zetaSpectralCoordinate rho.1.1) tau) =
      riemannXiUpperHyperbolicHeatRadialWindow z tau R := by
  unfold riemannXiUpperHyperbolicHeatRadialWindow
  apply Finset.sum_congr rfl
  intro rho _
  exact analyticMultiplicity_mul_positivePartHeat_eq_zetaUpperSummand
    hz htau rho.1

/-- For every positive zero-free radial circle, the literal heat of the
upper polynomial roots inside the disk converges to the genuine upper
spectral-xi radial heat window.  Roots tending to the real axis are handled
by the continuous positive-part weight and contribute zero in the limit. -/
theorem tendsto_finiteUpperHeatInsideRadialBall
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    {R : ℝ} (hR : 0 < R)
    (hboundary : ∀ w ∈ sphere 0 R, riemannXiSpectral w ≠ 0)
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n ↦ finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInsideBall (A n) R) tau)
      phi (nhds (riemannXiUpperHyperbolicHeatRadialWindow z tau R)) := by
  have hWeighted := tendsto_realPolynomialRootWeightedSumInRadialBall
    A hA hR hboundary
      (continuous_upperHalfPlanePositivePartHeatIntegrand z tau)
  rw [← sum_positivePartHeat_radialWindow_eq hz htau R]
  apply hWeighted.congr'
  exact Eventually.of_forall fun n ↦
    realPolynomialRootPositivePartHeatSumInBall_eq_upperHeat
      (A n) R hz htau

/-- The genuine upper spectral heat in the radial annulus between two nested
disks, defined by exact subtraction of the cumulative radial windows. -/
def riemannXiUpperHyperbolicHeatRadialAnnulus
    (z : ℂ) (tau r R : ℝ) : ℝ :=
  riemannXiUpperHyperbolicHeatRadialWindow z tau R -
    riemannXiUpperHyperbolicHeatRadialWindow z tau r

/-- Between two positive nested zero-free circles, the literal upper-root
heat in the polynomial annulus converges to the genuine spectral-xi annular
heat with every analytic multiplicity retained. -/
theorem tendsto_finiteUpperHeatInRadialAnnulus
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (hboundaryInner : ∀ w ∈ sphere 0 r, riemannXiSpectral w ≠ 0)
    (hboundaryOuter : ∀ w ∈ sphere 0 R, riemannXiSpectral w ≠ 0)
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n ↦ finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInRadialAnnulus (A n) r R) tau)
      phi
      (nhds (riemannXiUpperHyperbolicHeatRadialAnnulus z tau r R)) := by
  have hOuter := tendsto_finiteUpperHeatInsideRadialBall
    A hA hR hboundaryOuter hz htau
  have hInner := tendsto_finiteUpperHeatInsideRadialBall
    A hA hr hboundaryInner hz htau
  unfold riemannXiUpperHyperbolicHeatRadialAnnulus
  apply (hOuter.sub hInner).congr'
  exact Eventually.of_forall fun n ↦ by
    have hsplit := finiteUpperHeatInsideBall_add_annulus
      (A n) hrR z tau
    linarith

/-- Every fixed consecutive pair of the selected zero-free radial circles
has exact polynomial-to-spectral upper heat transport. -/
theorem tendsto_finiteUpperHeatInSelectedRadialAnnulus
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    (m : ℕ) {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n ↦ finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInRadialAnnulus (A n)
          (quantitativeSpectralRadialBoundary m)
          (quantitativeSpectralRadialBoundary (m + 1))) tau)
      phi
      (nhds (riemannXiUpperHyperbolicHeatRadialAnnulus z tau
        (quantitativeSpectralRadialBoundary m)
        (quantitativeSpectralRadialBoundary (m + 1)))) := by
  apply tendsto_finiteUpperHeatInRadialAnnulus A hA
    (quantitativeSpectralRadialBoundary_pos m)
    (quantitativeSpectralRadialBoundary_pos (m + 1))
    (quantitativeSpectralRadialBoundary_lt_of_succ_le
      (m := m) (n := m + 1) (by omega)).le
  · intro w hw
    apply riemannXiSpectral_ne_zero_on_quantitativeRadialBoundary m
    simpa [mem_sphere, dist_zero_right] using hw
  · intro w hw
    apply riemannXiSpectral_ne_zero_on_quantitativeRadialBoundary (m + 1)
    simpa [mem_sphere, dist_zero_right] using hw
  · exact hz
  · exact htau

/-- Under failure of RH, one and the same canonical finite Hardy sequence
simultaneously has cross-stage genuine divisor counts, vanishing outer heat,
fixed-shell convergence to spectral xi, and one quadratic-Gaussian majorant
for every sufficiently early shell.  This is the complete checked input for
the subsequent triangular-array dominated-convergence step. -/
theorem exists_radialRouche_fixedShellHeatTransport_sequence_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ K : ℝ, 1 ≤ K ∧ ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        (∀ (n m : ℕ), m + 1 ≤ n →
          realPolynomialRootCountInBall (B n) 0
              (quantitativeSpectralRadialBoundary m) =
            riemannXiSpectralRadialDivisorCount
              (quantitativeSpectralRadialBoundary m)) ∧
        (∀ (u : ℂ) (tau : ℝ), 0 < u.im → 0 < tau →
          Tendsto
            (fun n ↦ realPolynomialUpperHeatRemainderOutsideRootMultiset
              (B n) (realPolynomialUpperRootMultisetInsideBall (B n)
                (quantitativeSpectralRadialBoundary n)) u tau)
            atTop (nhds 0)) ∧
        (∀ (m : ℕ) (u : ℂ) (tau : ℝ), 0 < u.im → 0 < tau →
          Tendsto
            (fun n ↦ finiteUpperHyperbolicHeatSum u
              (realPolynomialUpperRootMultisetInRadialAnnulus (B n)
                (quantitativeSpectralRadialBoundary m)
                (quantitativeSpectralRadialBoundary (m + 1))) tau)
            atTop
            (nhds (riemannXiUpperHyperbolicHeatRadialAnnulus u tau
              (quantitativeSpectralRadialBoundary m)
              (quantitativeSpectralRadialBoundary (m + 1))))) ∧
        ∀ (n m : ℕ) (u : ℂ) (tau : ℝ), m + 2 ≤ n → 0 < tau →
          ‖u‖ ≤ quantitativeSpectralRadialBoundary m →
          finiteUpperHyperbolicHeatSum u
              (realPolynomialUpperRootMultisetInRadialAnnulus (B n)
                (quantitativeSpectralRadialBoundary m)
                (quantitativeSpectralRadialBoundary (m + 1))) tau ≤
            (K *
                (2 *
                    (quantitativeSpectralRadialBoundary (m + 1) + 1) + 1) ^ 2 /
                  Real.log 2) *
              (tau⁻¹ * Real.exp
                (-((quantitativeSpectralRadialBoundary m - ‖u‖) ^ 2 *
                  tau))) := by
  obtain ⟨eta, heta, z, hz, _hxi, A, _, C, _, B, hdata⟩ :=
    exists_radialRouche_crossStageDivisor_vanishingHeatTail_sequence_of_not_rh
      hRH
  dsimp only at hdata
  rcases hdata with
    ⟨_, hlimit, hfrontier, _, _, _, _, hcounts, htail⟩
  obtain ⟨K, hK, hKbound⟩ := riemannXi_quadraticGrowth
  refine ⟨eta, heta, z, hz, K, hK, B, hlimit, ?_, hcounts, htail, ?_, ?_⟩
  · intro n
    exact (hfrontier n).1
  · intro m u tau hu htau
    exact tendsto_finiteUpperHeatInSelectedRadialAnnulus
      B hlimit m hu htau
  · intro n m u tau hmn htau hru
    apply finiteUpperHeatInEarlierScheduledRadialAnnulus_le_quadraticGaussian
      (B n) hK hKbound hmn
    · intro k hkn
      exact hcounts n k hkn
    · exact htau
    · exact hru

end

end RiemannGaussian

import RiemannGaussian.FiniteToEntireLocalDivisor

/-!
# Bounded divisor and fixed-time heat transport

This file assembles the pointwise local-divisor theorem over arbitrary finite
families of spectral-xi zeros.  Pairwise disjoint isolating balls synchronize
the exact polynomial multiplicity counts.  More strongly, every continuous
weight summed over the full polynomial root multiset in one such ball
converges to analytic multiplicity times the weight at the limiting zero.

Specializing the weight to the upper-half-plane heat kernel proves that every
finite spectral-xi heat window is a limit of literal fixed-time heat sums over
pairwise disjoint clusters of polynomial roots.  Under failure of RH this
holds along the same exact root-pinned canonical Hardy sequence used by the
finite defect frontier.  No claim about roots outside the selected bounded
clusters, or about uniform tails as the window expands, is made here.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- A finite family of spectral xi zeros can be assigned arbitrarily small
isolating radii whose exact polynomial multiplicity counts hold
simultaneously. -/
theorem exists_simultaneous_riemannXiSpectral_localRootCounts
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    (S : Finset NontrivialZetaZero)
    (r : S → ℝ)
    (hr : ∀ rho : S, 0 < r rho) :
    ∃ R : S → ℝ,
      (∀ rho : S, 0 < R rho ∧ R rho < r rho ∧
        ∀ z ∈ closedBall (zetaSpectralCoordinate rho.1.1) (R rho),
          z ≠ zetaSpectralCoordinate rho.1.1 →
            riemannXiSpectral z ≠ 0) ∧
      ∀ᶠ n in phi, ∀ rho : S,
        realPolynomialRootCountInBall (A n)
          (zetaSpectralCoordinate rho.1.1) (R rho) =
            analyticZetaZeroMultiplicity rho.1 := by
  have hex (rho : S) :
      ∃ R : ℝ, 0 < R ∧ R < r rho ∧
        (∀ z ∈ closedBall (zetaSpectralCoordinate rho.1.1) R,
          z ≠ zetaSpectralCoordinate rho.1.1 →
            riemannXiSpectral z ≠ 0) ∧
        ∀ᶠ n in phi,
          realPolynomialRootCountInBall (A n)
            (zetaSpectralCoordinate rho.1.1) R =
              analyticZetaZeroMultiplicity rho.1 :=
    exists_lt_eventuallyEq_riemannXiSpectral_localRootCount
      A hA rho.1 (hr rho)
  choose R hR hRlt hzero hcount using hex
  refine ⟨R, ?_, Filter.eventually_all.mpr hcount⟩
  intro rho
  exact ⟨hR rho, hRlt rho, hzero rho⟩

/-- A finite spectral-xi divisor admits pairwise disjoint isolating balls in
which all exact polynomial multiplicity counts hold simultaneously. -/
theorem exists_pairwiseDisjoint_simultaneous_riemannXiSpectral_localRootCounts
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    (S : Finset NontrivialZetaZero) :
    ∃ R : S → ℝ,
      (∀ rho : S, 0 < R rho ∧
        ∀ z ∈ closedBall (zetaSpectralCoordinate rho.1.1) (R rho),
          z ≠ zetaSpectralCoordinate rho.1.1 →
            riemannXiSpectral z ≠ 0) ∧
      (Set.univ : Set S).PairwiseDisjoint (fun rho : S ↦
        closedBall (zetaSpectralCoordinate rho.1.1) (R rho)) ∧
      ∀ᶠ n in phi, ∀ rho : S,
        realPolynomialRootCountInBall (A n)
          (zetaSpectralCoordinate rho.1.1) (R rho) =
            analyticZetaZeroMultiplicity rho.1 := by
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
  obtain ⟨R, hR, hcount⟩ :=
    exists_simultaneous_riemannXiSpectral_localRootCounts
      A hA S r hr
  refine ⟨R, ?_, ?_, hcount⟩
  · intro rho
    exact ⟨(hR rho).1, (hR rho).2.2⟩
  · intro rho _ sigma _ hrs
    have hcenters : center rho ≠ center sigma :=
      hcenterInj.ne hrs
    have hdisjoint : Disjoint (U (center rho)) (U (center sigma)) :=
      hUdisjoint (Set.mem_range_self rho) (Set.mem_range_self sigma)
        hcenters
    apply hdisjoint.mono
    · exact (closedBall_subset_ball (hR rho).2.1).trans (hball rho)
    · exact (closedBall_subset_ball (hR sigma).2.1).trans (hball sigma)

/-- A continuous real weight summed over the roots of a real polynomial in
a complex ball, with every root occurrence retained. -/
def realPolynomialRootWeightedSumInBall
    (A : ℝ[X]) (a : ℂ) (R : ℝ) (W : ℂ → ℝ) : ℝ :=
  ((((A.map Complex.ofRealHom).roots.filter fun w ↦ w ∈ ball a R).map W).sum)

/-- Subtracting a constant from every multiset summand subtracts the
cardinality multiple of that constant from the total sum. -/
theorem multiset_sum_map_sub_const
    {alpha : Type*} (s : Multiset alpha) (W : alpha → ℝ) (c : ℝ) :
    (s.map fun x ↦ W x - c).sum =
      (s.map W).sum - (s.card : ℝ) * c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
        Nat.cast_add, Nat.cast_one, ih]
      ring

/-- Below any prescribed positive radius, continuous weighted sums over the
polynomial root multiset in one isolating ball converge to analytic
multiplicity times the weight at the limiting zero. -/
theorem AnalyticAt.exists_lt_realPolynomialRootWeightedSumInBall_tendsto
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X]) {f : ℂ → ℂ} {a : ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      f phi Set.univ)
    (hf : AnalyticAt ℂ f a) (hfinite : analyticOrderAt f a ≠ ⊤)
    {W : ℂ → ℝ} (hW : ContinuousAt W a)
    {rBound : ℝ} (hrBound : 0 < rBound) :
    ∃ R : ℝ, 0 < R ∧ R < rBound ∧
      (∀ z ∈ closedBall a R, z ≠ a → f z ≠ 0) ∧
      Tendsto
        (fun n ↦ realPolynomialRootWeightedSumInBall (A n) a R W)
        phi (nhds ((analyticOrderNatAt f a : ℝ) * W a)) := by
  obtain ⟨R, hR, hRBound, hzero, hOuterCount⟩ :=
    AnalyticAt.exists_lt_eventuallyEq_realPolynomialRootCountInBall_order
      A hA hf hfinite hrBound
  refine ⟨R, hR, hRBound, hzero, ?_⟩
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
    have hWclose : ∀ᶠ w in 𝓝 a,
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
      Multiset.eq_of_le_of_card_le hinnerLe (by rw [hcardInner, hcardOuter])
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

/-- On one fixed isolating ball, continuous weighted sums over the polynomial
root multiset converge to analytic multiplicity times the weight at the
limiting zero. -/
theorem AnalyticAt.exists_realPolynomialRootWeightedSumInBall_tendsto
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X]) {f : ℂ → ℂ} {a : ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      f phi Set.univ)
    (hf : AnalyticAt ℂ f a) (hfinite : analyticOrderAt f a ≠ ⊤)
    {W : ℂ → ℝ} (hW : ContinuousAt W a) :
    ∃ R : ℝ, 0 < R ∧
      (∀ z ∈ closedBall a R, z ≠ a → f z ≠ 0) ∧
      Tendsto
        (fun n ↦ realPolynomialRootWeightedSumInBall (A n) a R W)
        phi (nhds ((analyticOrderNatAt f a : ℝ) * W a)) := by
  obtain ⟨R, hR, _, hzero, hLimit⟩ :=
    AnalyticAt.exists_lt_realPolynomialRootWeightedSumInBall_tendsto
      A hA hf hfinite hW zero_lt_one
  exact ⟨R, hR, hzero, hLimit⟩

/-- Below any prescribed radius, the fixed-time heat weight summed over
polynomial roots near one spectral xi zero converges to that zero's genuine
multiplicity-weighted heat contribution. -/
theorem exists_lt_riemannXiSpectral_localPolynomialHeat_tendsto
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    (z : ℂ) (tau : ℝ) (rho : NontrivialZetaZero)
    {rBound : ℝ} (hrBound : 0 < rBound) :
    ∃ R : ℝ, 0 < R ∧ R < rBound ∧
      (∀ w ∈ closedBall (zetaSpectralCoordinate rho.1) R,
        w ≠ zetaSpectralCoordinate rho.1 →
          riemannXiSpectral w ≠ 0) ∧
      Tendsto
        (fun n ↦ realPolynomialRootWeightedSumInBall (A n)
          (zetaSpectralCoordinate rho.1) R
          (fun alpha ↦ upperHalfPlaneHyperbolicHeatIntegrand z alpha tau))
        phi
        (nhds ((analyticZetaZeroMultiplicity rho : ℝ) *
          upperHalfPlaneHyperbolicHeatIntegrand z
            (zetaSpectralCoordinate rho.1) tau)) := by
  have hfinite : analyticOrderAt riemannXiSpectral
      (zetaSpectralCoordinate rho.1) ≠ ⊤ := by
    rw [analyticOrderAt_riemannXiSpectral_zetaSpectralCoordinate,
      analyticOrderAt_riemannXi_eq_riemannZeta]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  have hweight : ContinuousAt
      (fun alpha ↦ upperHalfPlaneHyperbolicHeatIntegrand z alpha tau)
      (zetaSpectralCoordinate rho.1) := by
    unfold upperHalfPlaneHyperbolicHeatIntegrand
    simp only [Complex.normSq_apply]
    fun_prop
  obtain ⟨R, hR, hRlt, hzero, hLimit⟩ :=
    AnalyticAt.exists_lt_realPolynomialRootWeightedSumInBall_tendsto
      A hA (analyticAt_riemannXiSpectral
        (zetaSpectralCoordinate rho.1)) hfinite hweight hrBound
  refine ⟨R, hR, hRlt, hzero, ?_⟩
  simpa only
    [analyticOrderNatAt_riemannXiSpectral_zetaSpectralCoordinate] using
      hLimit

/-- For any finite spectral-xi divisor, one can choose pairwise disjoint
isolating balls so that the summed fixed-time polynomial heat weights converge
to the exact multiplicity-weighted spectral heat sum over that divisor. -/
theorem exists_pairwiseDisjoint_finite_riemannXiSpectral_polynomialHeat_tendsto
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    (z : ℂ) (tau : ℝ) (S : Finset NontrivialZetaZero) :
    ∃ R : S → ℝ,
      (∀ rho : S, 0 < R rho ∧
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
  have hex (rho : S) :
      ∃ R : ℝ, 0 < R ∧ R < r rho ∧
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
      A hA z tau rho.1 (hr rho)
  choose R hR hRlt hzero hLimit using hex
  refine ⟨R, ?_, ?_, ?_⟩
  · intro rho
    exact ⟨hR rho, hzero rho⟩
  · intro rho _ sigma _ hrs
    have hcenters : center rho ≠ center sigma :=
      hcenterInj.ne hrs
    have hdisjoint : Disjoint (U (center rho)) (U (center sigma)) :=
      hUdisjoint (Set.mem_range_self rho) (Set.mem_range_self sigma)
        hcenters
    apply hdisjoint.mono
    · exact (closedBall_subset_ball (hRlt rho)).trans (hball rho)
    · exact (closedBall_subset_ball (hRlt sigma)).trans (hball sigma)
  · simpa [center] using
      tendsto_finsetSum Finset.univ (fun rho _ ↦ hLimit rho)

/-- The finite canonical spectral window restricted to upper-half-plane
zeros. -/
noncomputable def upperSpectralZetaZeroWindow
    (T : ℝ) : Finset NontrivialZetaZero :=
  (spectralZetaZeroWindow T).filter fun rho ↦
    0 < (zetaSpectralCoordinate rho.1).im

/-- Summing genuine multiplicity-weighted heat terms over the upper subtype
of a canonical window gives the existing upper spectral heat window. -/
theorem sum_upperSpectralZetaZeroWindow_heat_eq
    (z : ℂ) (tau T : ℝ) :
    (∑ rho : upperSpectralZetaZeroWindow T,
      (analyticZetaZeroMultiplicity rho.1 : ℝ) *
        upperHalfPlaneHyperbolicHeatIntegrand z
          (zetaSpectralCoordinate rho.1.1) tau) =
      riemannXiUpperHyperbolicHeatWindow z tau T := by
  classical
  have hsub :
      (∑ rho ∈ upperSpectralZetaZeroWindow T,
        (analyticZetaZeroMultiplicity rho : ℝ) *
          upperHalfPlaneHyperbolicHeatIntegrand z
            (zetaSpectralCoordinate rho.1) tau) =
      (∑ rho : upperSpectralZetaZeroWindow T,
        (analyticZetaZeroMultiplicity rho.1 : ℝ) *
          upperHalfPlaneHyperbolicHeatIntegrand z
            (zetaSpectralCoordinate rho.1.1) tau) :=
    Finset.sum_subtype (upperSpectralZetaZeroWindow T)
      (fun _ ↦ Iff.rfl) _
  rw [← hsub]
  unfold upperSpectralZetaZeroWindow
  rw [Finset.sum_filter]
  simp [riemannXiUpperHyperbolicHeatWindow,
    zetaUpperHyperbolicHeatSummand]

/-- Every fixed finite upper spectral heat window is the limit of literal
heat weights summed over pairwise disjoint clusters of roots of the
polynomial approximants. -/
theorem exists_pairwiseDisjoint_riemannXiUpperHeatWindow_polynomial_tendsto
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    (z : ℂ) (tau T : ℝ) :
    ∃ R : upperSpectralZetaZeroWindow T → ℝ,
      (∀ rho : upperSpectralZetaZeroWindow T, 0 < R rho ∧
        ∀ w ∈ closedBall (zetaSpectralCoordinate rho.1.1) (R rho),
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
        phi (nhds (riemannXiUpperHyperbolicHeatWindow z tau T)) := by
  obtain ⟨R, hR, hdisjoint, hLimit⟩ :=
    exists_pairwiseDisjoint_finite_riemannXiSpectral_polynomialHeat_tendsto
      A hA z tau (upperSpectralZetaZeroWindow T)
  refine ⟨R, hR, hdisjoint, ?_⟩
  rw [← sum_upperSpectralZetaZeroWindow_heat_eq]
  exact hLimit

/-- Under failure of RH, the same root-pinned canonical Hardy sequence
recovers every finite upper spectral-xi heat window as a limit of literal
polynomial-root heat clusters. -/
theorem exists_canonicalFiniteHardyFrontier_upperHeatWindows_of_not_rh
    (hRH : ¬RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z0 : ℂ, 0 < z0.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z0) ∧
        ∀ (z : ℂ) (tau T : ℝ),
          ∃ R : upperSpectralZetaZeroWindow T → ℝ,
            (∀ rho : upperSpectralZetaZeroWindow T, 0 < R rho ∧
              ∀ w ∈ closedBall
                  (zetaSpectralCoordinate rho.1.1) (R rho),
                w ≠ zetaSpectralCoordinate rho.1.1 →
                  riemannXiSpectral w ≠ 0) ∧
            (Set.univ : Set (upperSpectralZetaZeroWindow T)).PairwiseDisjoint
              (fun rho ↦ closedBall
                (zetaSpectralCoordinate rho.1.1) (R rho)) ∧
            Tendsto
              (fun n ↦ ∑ rho : upperSpectralZetaZeroWindow T,
                realPolynomialRootWeightedSumInBall (B n)
                  (zetaSpectralCoordinate rho.1.1) (R rho)
                  (fun alpha ↦
                    upperHalfPlaneHyperbolicHeatIntegrand z alpha tau))
              atTop
              (nhds (riemannXiUpperHyperbolicHeatWindow z tau T)) := by
  obtain ⟨eta, heta, z0, hz0, B, hB, hfrontier⟩ :=
    exists_canonicalFiniteHardyFrontier_sequence_of_not_rh hRH
  refine ⟨eta, heta, z0, hz0, B, hB, hfrontier, ?_⟩
  intro z tau T
  exact exists_pairwiseDisjoint_riemannXiUpperHeatWindow_polynomial_tendsto
    B hB z tau T

end

end RiemannGaussian

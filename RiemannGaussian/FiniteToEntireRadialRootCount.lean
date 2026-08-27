import RiemannGaussian.FiniteToEntireRadialDivisor

/-!
# Exact radial divisor counts for polynomial approximants

This file closes the finite-divisor identification inside an arbitrary
zero-free radial circle.  The complement of finitely many isolating balls is
compact and contains no spectral-xi zero, so locally uniform convergence
eventually excludes all polynomial roots there.  An explicit multiset
partition then proves that the complete enclosed polynomial root count is the
sum of the genuine analytic xi multiplicities.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- A finite family of pairwise-exclusive predicates partitions the filtered
cardinality of a multiset, retaining every repeated occurrence. -/
theorem multiset_card_filter_eq_sum_card_filter_of_partition
    {alpha ι : Type*} [Fintype ι]
    (s : Multiset alpha) (p : alpha → Prop) (q : ι → alpha → Prop)
    [DecidablePred p] [∀ i, DecidablePred (q i)]
    (hcover : ∀ x ∈ s, p x ↔ ∃ i, q i x)
    (hdisjoint : ∀ x ∈ s, ∀ i j, q i x → q j x → i = j) :
    (s.filter p).card = ∑ i, (s.filter (q i)).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : a ∈ a ::ₘ s := by simp
      have hcoverTail : ∀ x ∈ s, p x ↔ ∃ i, q i x := by
        intro x hx
        exact hcover x (by simp [hx])
      have hdisjointTail :
          ∀ x ∈ s, ∀ i j, q i x → q j x → i = j := by
        intro x hx
        exact hdisjoint x (by simp [hx])
      have hhead :
          (if p a then 1 else 0) = ∑ i, if q i a then 1 else 0 := by
        by_cases hpa : p a
        · rw [if_pos hpa]
          obtain ⟨i, hi⟩ := (hcover a ha).mp hpa
          have hfilter :
              Finset.univ.filter (fun j ↦ q j a) = {i} := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_singleton]
            constructor
            · intro hj
              exact hdisjoint a ha j i hj hi
            · rintro rfl
              exact hi
          have hsum := Finset.sum_boole (R := ℕ)
            (fun j : ι ↦ q j a) Finset.univ
          rw [hfilter] at hsum
          change (∑ j : ι, if q j a then 1 else 0) = 1 at hsum
          exact hsum.symm
        · rw [if_neg hpa]
          have hnone : ∀ i, ¬q i a := by
            intro i hi
            exact hpa ((hcover a ha).mpr ⟨i, hi⟩)
          simp [hnone]
      simp only [Multiset.filter_cons, Multiset.card_add, apply_ite,
        Multiset.card_singleton, Multiset.card_zero]
      rw [ih hcoverTail hdisjointTail, Finset.sum_add_distrib, hhead]

/-- The part of a closed radial disk outside all prescribed open divisor
balls. -/
def radialDivisorComplement
    (R : ℝ) (r : spectralZetaZeroRadialWindow R → ℝ) : Set ℂ :=
  closedBall 0 R \ ⋃ rho : spectralZetaZeroRadialWindow R,
    ball (zetaSpectralCoordinate rho.1.1) (r rho)

/-- The closed radial disk outside finitely many open divisor balls is
compact. -/
theorem isCompact_radialDivisorComplement
    (R : ℝ) (r : spectralZetaZeroRadialWindow R → ℝ) :
    IsCompact (radialDivisorComplement R r) := by
  exact (isCompact_closedBall 0 R).diff
    (isOpen_iUnion fun _ : spectralZetaZeroRadialWindow R ↦ isOpen_ball)

/-- If the outer circle is xi-zero-free and all cluster radii are positive,
the radial divisor complement contains no spectral-xi zero. -/
theorem radialDivisorComplement_subset_zeroFree
    {R : ℝ} (hR : 0 < R)
    (hboundary : ∀ w ∈ sphere 0 R, riemannXiSpectral w ≠ 0)
    {r : spectralZetaZeroRadialWindow R → ℝ}
    (hr : ∀ rho, 0 < r rho) :
    radialDivisorComplement R r ⊆
      {w | riemannXiSpectral w ≠ 0} := by
  intro w hw
  change w ∈ closedBall 0 R \ ⋃ rho : spectralZetaZeroRadialWindow R,
    ball (zetaSpectralCoordinate rho.1.1) (r rho) at hw
  change riemannXiSpectral w ≠ 0
  intro hwzero
  have hnormLe : ‖w‖ ≤ R := by
    simpa [mem_closedBall, dist_zero_right] using hw.1
  have hnormNe : ‖w‖ ≠ R := by
    intro hnorm
    exact hboundary w (by
      simpa [mem_sphere, dist_zero_right] using hnorm) hwzero
  have hnormLt : ‖w‖ < R := lt_of_le_of_ne hnormLe hnormNe
  obtain ⟨rho, hwrho⟩ :=
    (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
  have hrho : rho ∈ spectralZetaZeroRadialWindow R :=
    (mem_spectralZetaZeroRadialWindow hR.le rho).mpr (by
      simpa [hwrho] using hnormLt)
  let rhoS : spectralZetaZeroRadialWindow R := ⟨rho, hrho⟩
  apply hw.2
  apply Set.mem_iUnion.mpr
  refine ⟨rhoS, ?_⟩
  rw [hwrho]
  exact mem_ball_self (hr rhoS)

/-- If a polynomial is zero-free outside a pairwise-disjoint finite family of
balls inside an outer ball, its complete outer root count is the sum of the
local counts, with algebraic multiplicity. -/
theorem realPolynomialRootCountInBall_eq_sum_of_zeroFree_complement
    {kappa : Type*} [Fintype kappa]
    (A : ℝ[X]) (c : ℂ) (R : ℝ) (center : kappa → ℂ) (r : kappa → ℝ)
    (hinside : ∀ i, closedBall (center i) (r i) ⊆ ball c R)
    (hdisjoint : (Set.univ : Set kappa).PairwiseDisjoint
      (fun i ↦ closedBall (center i) (r i)))
    (hzero : ∀ w ∈ closedBall c R \ ⋃ i : kappa, ball (center i) (r i),
      (A.map Complex.ofRealHom).eval w ≠ 0) :
    realPolynomialRootCountInBall A c R =
      ∑ i : kappa,
        realPolynomialRootCountInBall A (center i) (r i) := by
  let roots := (A.map Complex.ofRealHom).roots
  have hdisjointOpen :
      (Set.univ : Set kappa).PairwiseDisjoint
        (fun i ↦ ball (center i) (r i)) :=
    hdisjoint.mono fun _ ↦ ball_subset_closedBall
  have hcover (w : ℂ) (hwroot : w ∈ roots) :
      w ∈ ball c R ↔ ∃ i : kappa, w ∈ ball (center i) (r i) := by
    constructor
    · intro hwOuter
      by_contra hnone
      have hwK : w ∈ closedBall c R \ ⋃ i : kappa,
          ball (center i) (r i) := by
        refine ⟨ball_subset_closedBall hwOuter, ?_⟩
        intro hwUnion
        rcases Set.mem_iUnion.mp hwUnion with ⟨i, hwi⟩
        exact hnone ⟨i, hwi⟩
      have hwEval : (A.map Complex.ofRealHom).eval w = 0 := by
        simpa [roots, Polynomial.IsRoot] using
          (Polynomial.mem_roots'.mp hwroot).2
      exact (hzero w hwK) hwEval
    · rintro ⟨i, hwi⟩
      exact hinside i (ball_subset_closedBall hwi)
  have hunique (w : ℂ) (hwroot : w ∈ roots)
      (i j : kappa) (hwi : w ∈ ball (center i) (r i))
      (hwj : w ∈ ball (center j) (r j)) : i = j := by
    by_contra hij
    exact Set.disjoint_left.mp
      (hdisjointOpen (Set.mem_univ i) (Set.mem_univ j) hij) hwi hwj
  have hpartition :=
    multiset_card_filter_eq_sum_card_filter_of_partition
      roots (fun w ↦ w ∈ ball c R)
      (fun i w ↦ w ∈ ball (center i) (r i))
      hcover hunique
  simpa [realPolynomialRootCountInBall, roots] using hpartition

/-- Across a spectral-xi-zero-free radial circle, every globally locally
uniform real-polynomial approximation eventually has complete enclosed root
count equal to the genuine finite spectral-xi divisor count. -/
theorem eventuallyEq_realPolynomialRootCountInBall_radialDivisor
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    {R : ℝ} (hR : 0 < R)
    (hboundary : ∀ w ∈ sphere 0 R, riemannXiSpectral w ≠ 0) :
    ∀ᶠ n in phi,
      realPolynomialRootCountInBall (A n) 0 R =
        riemannXiSpectralRadialDivisorCount R := by
  obtain ⟨r, hr, hdisjoint, hcounts⟩ :=
    exists_pairwiseDisjoint_insideBall_simultaneous_radialRootCounts
      A hA hR
  let U : Set ℂ := {w | riemannXiSpectral w ≠ 0}
  have hUopen : IsOpen U :=
    isOpen_ne.preimage differentiable_riemannXiSpectral.continuous
  have hpolyZeroFree :
      ∀ᶠ n in phi,
        ∀ w ∈ radialDivisorComplement R r,
          ((A n).map Complex.ofRealHom).eval w ≠ 0 :=
    eventually_forall_ne_zero_on_compact_of_tendstoLocallyUniformlyOn
      (hA.mono (subset_univ U)) hUopen
      (isCompact_radialDivisorComplement R r)
      (radialDivisorComplement_subset_zeroFree hR hboundary
        (fun rho ↦ (hr rho).1))
      differentiable_riemannXiSpectral.continuous.continuousOn
      (fun _ hw ↦ hw)
  have hMultiplicitySum :
      (∑ rho : spectralZetaZeroRadialWindow R,
        analyticZetaZeroMultiplicity rho.1) =
        riemannXiSpectralRadialDivisorCount R := by
    rw [riemannXiSpectralRadialDivisorCount]
    exact (Finset.sum_subtype
      (spectralZetaZeroRadialWindow R) (fun _ ↦ Iff.rfl)
      analyticZetaZeroMultiplicity).symm
  filter_upwards [hcounts, hpolyZeroFree] with n hnCounts hnZero
  calc
    realPolynomialRootCountInBall (A n) 0 R =
        ∑ rho : spectralZetaZeroRadialWindow R,
          realPolynomialRootCountInBall (A n)
            (zetaSpectralCoordinate rho.1.1) (r rho) := by
      apply realPolynomialRootCountInBall_eq_sum_of_zeroFree_complement
      · exact fun rho ↦ (hr rho).2.2
      · exact hdisjoint
      · simpa [radialDivisorComplement] using hnZero
    _ = ∑ rho : spectralZetaZeroRadialWindow R,
        analyticZetaZeroMultiplicity rho.1 := by
      exact Finset.sum_congr rfl fun rho _ ↦ hnCounts rho
    _ = riemannXiSpectralRadialDivisorCount R := hMultiplicitySum

/-- The spectral-xi logarithmic-derivative integral around any positive
zero-free radial circle is exactly `2 * pi * I` times the genuine analytic
divisor multiplicity inside the circle. -/
theorem circleIntegral_logDeriv_riemannXiSpectral_eq_radialDivisorCount
    {R : ℝ} (hR : 0 < R)
    (hboundary : ∀ w ∈ sphere 0 R, riemannXiSpectral w ≠ 0) :
    (∮ w in C(0, R), logDeriv riemannXiSpectral w) =
      (riemannXiSpectralRadialDivisorCount R : ℂ) *
        (2 * Real.pi : ℝ) * Complex.I := by
  let A : ℕ → ℝ[X] := riemannXiSpectralRealTaylorPolynomial
  have hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral atTop Set.univ := by
    simpa [A] using
      riemannXiSpectralRealTaylorPolynomial_tendstoLocallyUniformlyOn
  obtain ⟨m, hm, hIntegral⟩ :=
    exists_eventuallyEq_riemannXiSpectral_polynomialRootCountInBall
      A hA 0 hR.le hboundary
  have hDivisor :=
    eventuallyEq_realPolynomialRootCountInBall_radialDivisor
      A hA hR hboundary
  obtain ⟨n, hnM, hnDivisor⟩ := (hm.and hDivisor).exists
  have hmDivisor : m = riemannXiSpectralRadialDivisorCount R :=
    hnM.symm.trans hnDivisor
  simpa [hmDivisor] using hIntegral

/-- On every selected expanding spectral circle, the xi argument-principle
integral is the exact finite genuine divisor multiplicity. -/
theorem circleIntegral_logDeriv_riemannXiSpectral_eq_selectedRadialDivisorCount
    (n : ℕ) :
    (∮ w in C(0, quantitativeSpectralRadialBoundary n),
      logDeriv riemannXiSpectral w) =
      (riemannXiSpectralRadialDivisorCount
        (quantitativeSpectralRadialBoundary n) : ℂ) *
        (2 * Real.pi : ℝ) * Complex.I := by
  apply circleIntegral_logDeriv_riemannXiSpectral_eq_radialDivisorCount
    (quantitativeSpectralRadialBoundary_pos n)
  intro w hw
  apply riemannXiSpectral_ne_zero_on_quantitativeRadialBoundary n
  simpa [mem_sphere, dist_zero_right] using hw

/-- A polynomial whose selected-circle argument-principle count equals the
spectral-xi integral has exactly the genuine xi divisor multiplicity inside
that circle. -/
theorem realPolynomialRootCountInBall_eq_selectedRadialDivisorCount
    (A : ℝ[X]) (n : ℕ)
    (hIntegral :
      (realPolynomialRootCountInBall A 0
          (quantitativeSpectralRadialBoundary n) : ℂ) *
          (2 * Real.pi : ℝ) * Complex.I =
        ∮ w in C(0, quantitativeSpectralRadialBoundary n),
          logDeriv riemannXiSpectral w) :
    realPolynomialRootCountInBall A 0
        (quantitativeSpectralRadialBoundary n) =
      riemannXiSpectralRadialDivisorCount
        (quantitativeSpectralRadialBoundary n) := by
  have hDivisorIntegral :=
    circleIntegral_logDeriv_riemannXiSpectral_eq_selectedRadialDivisorCount n
  have hscale : ((2 * Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 := by
    have htwoPi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
    exact mul_ne_zero htwoPi Complex.I_ne_zero
  have hcast :
      (realPolynomialRootCountInBall A 0
          (quantitativeSpectralRadialBoundary n) : ℂ) =
        (riemannXiSpectralRadialDivisorCount
          (quantitativeSpectralRadialBoundary n) : ℂ) := by
    apply mul_right_cancel₀ hscale
    calc
      (realPolynomialRootCountInBall A 0
          (quantitativeSpectralRadialBoundary n) : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I) =
        (realPolynomialRootCountInBall A 0
          (quantitativeSpectralRadialBoundary n) : ℂ) *
          (2 * Real.pi : ℝ) * Complex.I := by ring
      _ = ∮ w in C(0, quantitativeSpectralRadialBoundary n),
          logDeriv riemannXiSpectral w := hIntegral
      _ = (riemannXiSpectralRadialDivisorCount
          (quantitativeSpectralRadialBoundary n) : ℂ) *
          (2 * Real.pi : ℝ) * Complex.I := hDivisorIntegral
      _ = (riemannXiSpectralRadialDivisorCount
          (quantitativeSpectralRadialBoundary n) : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I) := by ring
  exact_mod_cast hcast

/-- Under failure of RH, every scheduled canonical finite Hardy polynomial
has exactly the genuine finite spectral-xi divisor inside its selected
expanding circle; no additional polynomial root remains enclosed. -/
theorem exists_radialRouche_exactDivisor_sequence_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ A : ℝ, 1 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
        ∃ B : ℕ → ℝ[X],
          let L := finiteERootPinnedRadialConstant A eta z
          Tendsto (radialRoucheIndex A L C) atTop atTop ∧
          TendstoLocallyUniformlyOn
            (fun n w => ((B n).map Complex.ofRealHom).eval w)
            riemannXiSpectral atTop Set.univ ∧
          (∀ n, CanonicalFiniteHardyFrontier (B n) eta z ∧
            (B n).natDegree ≤ max (radialRoucheIndex A L C n) 3) ∧
          (∀ n, (radialRoucheIndex A L C n : ℝ) <
            radialRoucheIndexGrowthConstant A L C *
              Real.exp (5 * quantitativeSpectralRadialBoundary n)) ∧
          ∀ n : ℕ,
            realPolynomialRootCountInBall (B n) 0
                (quantitativeSpectralRadialBoundary n) =
              riemannXiSpectralRadialDivisorCount
                (quantitativeSpectralRadialBoundary n) := by
  obtain ⟨eta, heta, z, hz, A, hA, C, hC, B,
      hindex, hlimit, hfrontier, hgrowth, hIntegral⟩ :=
    exists_radialRouche_rootCount_integral_sequence_of_not_rh hRH
  let L : ℝ := finiteERootPinnedRadialConstant A eta z
  refine ⟨eta, heta, z, hz, A, hA, C, hC, B, ?_⟩
  dsimp only
  refine ⟨by simpa [L] using hindex, hlimit, ?_, ?_, ?_⟩
  · intro n
    simpa [L] using hfrontier n
  · intro n
    simpa [L] using hgrowth n
  · intro n
    apply realPolynomialRootCountInBall_eq_selectedRadialDivisorCount
    simpa [L] using hIntegral n

end

end RiemannGaussian

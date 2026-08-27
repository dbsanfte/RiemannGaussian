import RiemannGaussian.PolynomialLogDerivativeCircle

/-!
# Stable root counts across zero-free circles

This file turns convergence of logarithmic-derivative circle integrals into
eventual equality of polynomial root counts.  The discrete step is proved
explicitly: a convergent net of positive real multiples of natural numbers
is eventually constant.  Combining that fact with the exact polynomial
argument principle gives local multiplicity stability for arbitrary locally
uniform real-polynomial approximants and for the root-pinned canonical Hardy
sequence forced by failure of RH.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- A convergent net of fixed positive multiples of natural numbers is
eventually constant. -/
theorem eventuallyEq_nat_of_tendsto_natCast_mul
    {ι : Type*} {phi : Filter ι} [phi.NeBot]
    (k : ι → ℕ) {a L : ℝ} (ha : 0 < a)
    (h : Tendsto (fun i ↦ (k i : ℝ) * a) phi (nhds L)) :
    ∃ m : ℕ, ∀ᶠ i in phi, k i = m := by
  have hclose : ∀ᶠ i in phi, dist ((k i : ℝ) * a) L < a / 3 :=
    (Metric.tendsto_nhds.mp h) (a / 3) (by positivity)
  obtain ⟨i0, hi0⟩ := hclose.exists
  refine ⟨k i0, ?_⟩
  filter_upwards [hclose] with i hi
  have hdist : dist ((k i : ℝ) * a) ((k i0 : ℝ) * a) < a := by
    calc
      dist ((k i : ℝ) * a) ((k i0 : ℝ) * a) ≤
          dist ((k i : ℝ) * a) L + dist L ((k i0 : ℝ) * a) :=
        dist_triangle _ _ _
      _ < a / 3 + a / 3 := add_lt_add hi (by simpa [dist_comm] using hi0)
      _ < a := by linarith
  have hdistCast : dist (k i : ℝ) (k i0 : ℝ) < 1 := by
    rw [Real.dist_eq, ← sub_mul, abs_mul, abs_of_pos ha] at hdist
    have hmul : |(k i : ℝ) - (k i0 : ℝ)| * a < 1 * a := by
      simpa using hdist
    simpa [Real.dist_eq] using lt_of_mul_lt_mul_right hmul ha.le
  have habs : |(k i : ℝ) - (k i0 : ℝ)| < 1 := by
    simpa [Real.dist_eq] using hdistCast
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcast : (k i : ℝ) + 1 ≤ (k i0 : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hlt)
    linarith [abs_lt.mp habs]
  · have hcast : (k i0 : ℝ) + 1 ≤ (k i : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hgt)
    linarith [abs_lt.mp habs]

/-- The number of roots of a real polynomial in a complex open ball,
counted with algebraic multiplicity. -/
def realPolynomialRootCountInBall (A : ℝ[X]) (c : ℂ) (R : ℝ) : ℕ :=
  ((A.map Complex.ofRealHom).roots.filter fun w ↦ w ∈ ball c R).card

/-- Across a zero-free circle, locally uniform convergence of real
polynomials forces their root counts inside the circle to stabilize.  The
limiting logarithmic-derivative integral is the same integer multiple of
`2 * pi * I`. -/
theorem exists_eventuallyEq_realPolynomialRootCountInBall_of_tendstoLocallyUniformlyOn
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X]) {f : ℂ → ℂ} {U : Set ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w) f phi U)
    (hU : IsOpen U) (hzero : ∀ w ∈ U, f w ≠ 0)
    (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (hsphere : sphere c R ⊆ U) :
    ∃ m : ℕ,
      (∀ᶠ n in phi, realPolynomialRootCountInBall (A n) c R = m) ∧
      (∮ w in C(c, R), logDeriv f w) =
        (m : ℂ) * (2 * Real.pi : ℝ) * Complex.I := by
  let F : ι → ℂ → ℂ :=
    fun n w ↦ ((A n).map Complex.ofRealHom).eval w
  let L : ℂ := ∮ w in C(c, R), logDeriv f w
  have hhol : ∀ᶠ n in phi, DifferentiableOn ℂ (F n) U :=
    Eventually.of_forall fun n ↦
      ((A n).map Complex.ofRealHom).differentiableOn
  have hfdiff : DifferentiableOn ℂ f U :=
    hA.differentiableOn hhol hU
  have hboundary : ∀ᶠ n in phi, ∀ w ∈ sphere c R, F n w ≠ 0 :=
    eventually_forall_ne_zero_on_compact_of_tendstoLocallyUniformlyOn
      hA hU (isCompact_sphere c R) hsphere hfdiff.continuousOn hzero
  have hpolyNe : ∀ᶠ n in phi, A n ≠ 0 := by
    obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (E := ℂ)).mpr hR
    filter_upwards [hboundary] with n hn
    intro hAn
    exact hn w hw (by simp [F, hAn])
  have hIntegral : Tendsto
      (fun n ↦ ∮ w in C(c, R), logDeriv (F n) w) phi (nhds L) := by
    simpa [F, L] using realPolynomial_circleIntegral_logDeriv_tendsto
      A hA hU hzero c hR hsphere
  have hExact : ∀ᶠ n in phi,
      (∮ w in C(c, R), logDeriv (F n) w) =
        (realPolynomialRootCountInBall (A n) c R : ℂ) *
          (2 * Real.pi : ℝ) * Complex.I := by
    filter_upwards [hboundary, hpolyNe] with n hnBoundary hnNe
    simpa [F, realPolynomialRootCountInBall] using
      circleIntegral_logDeriv_realPolynomial_eq_rootCount
        hnNe hR hnBoundary
  have hScaled : Tendsto
      (fun n ↦ (realPolynomialRootCountInBall (A n) c R : ℂ) *
        (2 * Real.pi : ℝ) * Complex.I) phi (nhds L) :=
    hIntegral.congr' hExact
  have hScaledReal : Tendsto
      (fun n ↦ (realPolynomialRootCountInBall (A n) c R : ℝ) *
        (2 * Real.pi)) phi (nhds L.im) := by
    have him := (Complex.continuous_im.tendsto L).comp hScaled
    refine him.congr' (Eventually.of_forall fun n ↦ ?_)
    simp
  obtain ⟨m, hm⟩ := eventuallyEq_nat_of_tendsto_natCast_mul
    (fun n ↦ realPolynomialRootCountInBall (A n) c R)
    (show 0 < 2 * Real.pi by positivity) hScaledReal
  refine ⟨m, hm, ?_⟩
  have hScaledM : Tendsto
      (fun n ↦ (realPolynomialRootCountInBall (A n) c R : ℂ) *
        (2 * Real.pi : ℝ) * Complex.I) phi
      (nhds ((m : ℂ) * (2 * Real.pi : ℝ) * Complex.I)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hm] with n hn
    simp [hn]
  exact tendsto_nhds_unique hScaled hScaledM

/-- Spectral-xi specialization: a globally convergent real-polynomial
sequence has eventually constant root count inside every circle on which
spectral xi has no zero. -/
theorem exists_eventuallyEq_riemannXiSpectral_polynomialRootCountInBall
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ w ∈ sphere c R, riemannXiSpectral w ≠ 0) :
    ∃ m : ℕ,
      (∀ᶠ n in phi, realPolynomialRootCountInBall (A n) c R = m) ∧
      (∮ w in C(c, R), logDeriv riemannXiSpectral w) =
        (m : ℂ) * (2 * Real.pi : ℝ) * Complex.I := by
  let U : Set ℂ := {w | riemannXiSpectral w ≠ 0}
  have hU : IsOpen U :=
    isOpen_ne.preimage differentiable_riemannXiSpectral.continuous
  have hzero : ∀ w ∈ U, riemannXiSpectral w ≠ 0 := fun _ hw ↦ hw
  have hsphere : sphere c R ⊆ U := fun w hw ↦ hboundary w hw
  exact
    exists_eventuallyEq_realPolynomialRootCountInBall_of_tendstoLocallyUniformlyOn
      A (hA.mono (subset_univ U)) hU hzero c hR hsphere

/-- If RH fails, the exact root-pinned canonical Hardy sequence already
constructed in the finite-to-entire reduction has stable multiplicity counts
inside every circle avoiding the spectral-xi divisor.  Its stabilized count
is certified by the spectral-xi logarithmic-derivative integral. -/
theorem exists_canonicalFiniteHardyFrontier_rootCount_stability_of_not_rh
    (hRH : ¬RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        ∀ (c : ℂ) (R : ℝ), 0 ≤ R →
          (∀ w ∈ sphere c R, riemannXiSpectral w ≠ 0) →
          ∃ m : ℕ,
            (∀ᶠ n in atTop,
              realPolynomialRootCountInBall (B n) c R = m) ∧
            (∮ w in C(c, R), logDeriv riemannXiSpectral w) =
              (m : ℂ) * (2 * Real.pi : ℝ) * Complex.I := by
  obtain ⟨eta, heta, z, hz, B, hB, hfrontier⟩ :=
    exists_canonicalFiniteHardyFrontier_sequence_of_not_rh hRH
  refine ⟨eta, heta, z, hz, B, hB, hfrontier, ?_⟩
  intro c R hR hboundary
  exact exists_eventuallyEq_riemannXiSpectral_polynomialRootCountInBall
    B hB c hR hboundary

end

end RiemannGaussian

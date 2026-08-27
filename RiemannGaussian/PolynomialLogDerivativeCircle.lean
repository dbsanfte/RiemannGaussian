import RiemannGaussian.FiniteToEntireLogDerivative

/-!
# Polynomial logarithmic derivatives and circle root counts

This file proves the finite argument-principle identity needed by the local
divisor passage.  For a nonzero complex polynomial with no zero on a circle,
the circle integral of its logarithmic derivative is exactly `2 * pi * I`
times the number of roots in the open ball, counted with the multiplicities
stored in the polynomial root multiset.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- A Cauchy kernel whose pole lies outside the closed disk has zero circle
integral. -/
theorem circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall
    {c w : ℂ} {R : ℝ} (hR : 0 ≤ R) (hw : w ∉ closedBall c R) :
    (∮ z in C(c, R), (z - w)⁻¹) = 0 := by
  apply circleIntegral_eq_zero_of_differentiable_on_off_countable
    hR countable_empty
  · apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz
    show z - w ≠ 0
    exact sub_ne_zero.mpr fun hzw ↦ hw (hzw ▸ hz)
  · intro z hz
    have hzclosed : z ∈ closedBall c R :=
      ball_subset_closedBall hz.1
    exact (differentiableAt_id.sub_const w).inv
      (sub_ne_zero.mpr fun hzw ↦ hw (hzw ▸ hzclosed))

/-- The sum of simple Cauchy kernels attached to a finite root multiset. -/
def multisetCauchySum (roots : Multiset ℂ) (z : ℂ) : ℂ :=
  (roots.map fun w ↦ (z - w)⁻¹).sum

/-- A finite Cauchy sum is circle integrable when none of its poles lies on
the circle. -/
theorem circleIntegrable_multisetCauchySum
    (roots : Multiset ℂ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ w ∈ roots, w ∉ sphere c R) :
    CircleIntegrable (multisetCauchySum roots) c R := by
  induction roots using Multiset.induction_on with
  | empty =>
      change CircleIntegrable (fun _ ↦ (0 : ℂ)) c R
      exact circleIntegrable_const 0 c R
  | @cons w roots ih =>
      have hw : w ∉ sphere c R := hboundary w (by simp)
      have hroots : ∀ u ∈ roots, u ∉ sphere c R := by
        intro u hu
        exact hboundary u (by simp [hu])
      have hhead : CircleIntegrable (fun z : ℂ ↦ (z - w)⁻¹) c R := by
        apply circleIntegrable_sub_inv_iff.mpr
        exact Or.inr (by simpa [abs_of_nonneg hR] using hw)
      have htail := ih hroots
      unfold multisetCauchySum
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact hhead.add htail

/-- The circle integral of a finite Cauchy sum counts exactly the poles in
the open disk, retaining every multiset occurrence. -/
theorem circleIntegral_multisetCauchySum_eq_card
    (roots : Multiset ℂ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ w ∈ roots, w ∉ sphere c R) :
    (∮ z in C(c, R), multisetCauchySum roots z) =
      ((roots.filter fun w ↦ w ∈ ball c R).card : ℂ) *
        (2 * Real.pi : ℝ) * Complex.I := by
  induction roots using Multiset.induction_on with
  | empty => simp [multisetCauchySum, circleIntegral]
  | @cons w roots ih =>
      have hwBoundary : w ∉ sphere c R := hboundary w (by simp)
      have hrootsBoundary : ∀ u ∈ roots, u ∉ sphere c R := by
        intro u hu
        exact hboundary u (by simp [hu])
      have hhead : CircleIntegrable (fun z : ℂ ↦ (z - w)⁻¹) c R := by
        apply circleIntegrable_sub_inv_iff.mpr
        exact Or.inr (by simpa [abs_of_nonneg hR] using hwBoundary)
      have htail : CircleIntegrable (multisetCauchySum roots) c R :=
        circleIntegrable_multisetCauchySum roots hR hrootsBoundary
      have hintegralAdd :
          (∮ z in C(c, R), multisetCauchySum (w ::ₘ roots) z) =
            (∮ z in C(c, R), (z - w)⁻¹) +
              ∮ z in C(c, R), multisetCauchySum roots z := by
        simpa [multisetCauchySum] using
          circleIntegral.integral_add hhead htail
      rw [hintegralAdd, ih hrootsBoundary]
      by_cases hwBall : w ∈ ball c R
      · rw [circleIntegral.integral_sub_inv_of_mem_ball hwBall,
          Multiset.filter_cons_of_pos _ hwBall, Multiset.card_cons]
        push_cast
        ring
      · have hwClosed : w ∉ closedBall c R := by
          intro hwClosed
          have hge : R ≤ dist w c := by
            rw [mem_ball] at hwBall
            exact le_of_not_gt hwBall
          have hne : dist w c ≠ R := by
            intro heq
            apply hwBoundary
            rw [mem_sphere, heq]
          have hgt : R < dist w c := lt_of_le_of_ne hge hne.symm
          have hle : dist w c ≤ R := by
            simpa [mem_closedBall] using hwClosed
          exact (not_le_of_gt hgt) hle
        rw [circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall hR hwClosed,
          Multiset.filter_cons_of_neg _ hwBall, zero_add]

/-- Polynomial argument principle on a circle, with algebraic multiplicity
coming directly from the polynomial root multiset. -/
theorem circleIntegral_logDeriv_polynomial_eq_rootCount
    {p : ℂ[X]} (hp : p ≠ 0) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R, p.eval z ≠ 0) :
    (∮ z in C(c, R), logDeriv (fun w ↦ p.eval w) z) =
      (((p.roots.filter fun w ↦ w ∈ ball c R).card : ℕ) : ℂ) *
        (2 * Real.pi : ℝ) * Complex.I := by
  have hrootBoundary : ∀ w ∈ p.roots, w ∉ sphere c R := by
    intro w hw hwsphere
    exact hboundary w hwsphere ((mem_roots hp).mp hw)
  rw [circleIntegral.integral_congr hR fun z hz ↦ ?_]
  · exact circleIntegral_multisetCauchySum_eq_card
      p.roots hR hrootBoundary
  · rw [logDeriv_apply, Polynomial.deriv]
    simpa [multisetCauchySum] using
      (IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero
        (hboundary z hz)

/-- Real-polynomial specialization of the exact circle root-count formula. -/
theorem circleIntegral_logDeriv_realPolynomial_eq_rootCount
    {A : ℝ[X]} (hA : A ≠ 0) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R,
      (A.map Complex.ofRealHom).eval z ≠ 0) :
    (∮ z in C(c, R),
        logDeriv (fun w ↦ (A.map Complex.ofRealHom).eval w) z) =
      (((A.map Complex.ofRealHom).roots.filter fun w ↦
        w ∈ ball c R).card : ℂ) * (2 * Real.pi : ℝ) * Complex.I := by
  exact circleIntegral_logDeriv_polynomial_eq_rootCount
    ((Polynomial.map_ne_zero_iff (p := A)
      Complex.ofRealHom.injective).mpr hA)
    hR hboundary

end

end RiemannGaussian

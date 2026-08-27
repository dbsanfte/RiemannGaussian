import RiemannGaussian.FiniteToEntireRadialHeatTail

/-!
# Cross-stage radial Rouché control

The scheduled polynomial error on one selected outer circle controls the
whole enclosed disk by the maximum-modulus principle.  Because the explicit
outer error floor is strictly smaller than every earlier selected xi floor,
the stage-`n` polynomial has the genuine xi divisor count inside every
selected circle at least one index earlier.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- A norm bound for the difference between a polynomial and spectral xi on
a positive circle propagates throughout the enclosed closed disk. -/
theorem norm_realPolynomial_sub_riemannXiSpectral_le_of_sphere_bound
    (A : ℝ[X]) {R E : ℝ} (hR : 0 < R)
    (hbound : ∀ w : ℂ, ‖w‖ = R →
      ‖(A.map Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤ E)
    {w : ℂ} (hw : ‖w‖ ≤ R) :
    ‖(A.map Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤ E := by
  let f : ℂ → ℂ := fun u ↦
    (A.map Complex.ofRealHom).eval u - riemannXiSpectral u
  have hdiff : DiffContOnCl ℂ f (ball 0 R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hR.ne']
    exact ((A.map Complex.ofRealHom).differentiable.sub
      differentiable_riemannXiSpectral).differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    isBounded_ball hdiff (z := w)
  · intro u hu
    rw [frontier_ball 0 hR.ne'] at hu
    apply hbound
    simpa [mem_sphere, dist_zero_right] using hu
  · rw [closure_ball 0 hR.ne']
    simpa [mem_closedBall, dist_zero_right] using hw

/-- A selected radius is strictly smaller than any selected radius whose
index is at least one larger. -/
theorem quantitativeSpectralRadialBoundary_lt_of_succ_le
    {m n : ℕ} (hmn : m + 1 ≤ n) :
    quantitativeSpectralRadialBoundary m <
      quantitativeSpectralRadialBoundary n := by
  have hcast : (m : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hmn
  have hm := (quantitativeSpectralRadialBoundary_spec m).2.1
  have hn := (quantitativeSpectralRadialBoundary_spec n).1
  linarith

/-- For a positive lower-bound constant, the double-exponential floor at a
later selected radius is strictly smaller than the floor at an earlier one. -/
theorem quantitativeRadialFloor_lt_of_succ_le
    {C : ℝ} (hC : 0 < C) {m n : ℕ} (hmn : m + 1 ≤ n) :
    Real.exp
        (-C * Real.exp (5 * quantitativeSpectralRadialBoundary n)) <
      Real.exp
        (-C * Real.exp (5 * quantitativeSpectralRadialBoundary m)) := by
  apply Real.exp_lt_exp.mpr
  have hr := quantitativeSpectralRadialBoundary_lt_of_succ_le hmn
  have hexp :
      Real.exp (5 * quantitativeSpectralRadialBoundary m) <
        Real.exp (5 * quantitativeSpectralRadialBoundary n) :=
    Real.exp_lt_exp.mpr (by linarith)
  nlinarith

/-- If a polynomial beats the scheduled error floor on the `n`th selected
circle, then on every selected circle at least one index earlier its complete
root count is the genuine spectral-xi divisor count. -/
theorem realPolynomialRootCountInBall_eq_earlierRadialDivisorCount
    (A : ℝ[X]) {C : ℝ} (hC : 0 < C)
    (hfloor : ∀ (k : ℕ) {w : ℂ},
      ‖w‖ = quantitativeSpectralRadialBoundary k →
        Real.exp
            (-C * Real.exp
              (5 * quantitativeSpectralRadialBoundary k)) ≤
          ‖riemannXiSpectral w‖)
    {m n : ℕ} (hmn : m + 1 ≤ n)
    (herror : ∀ w : ℂ,
      ‖w‖ = quantitativeSpectralRadialBoundary n →
        ‖(A.map Complex.ofRealHom).eval w - riemannXiSpectral w‖ <
          Real.exp
            (-C * Real.exp
              (5 * quantitativeSpectralRadialBoundary n))) :
    realPolynomialRootCountInBall A 0
        (quantitativeSpectralRadialBoundary m) =
      riemannXiSpectralRadialDivisorCount
        (quantitativeSpectralRadialBoundary m) := by
  have hinnerOuter := quantitativeSpectralRadialBoundary_lt_of_succ_le hmn
  have houterBound {w : ℂ}
      (hw : ‖w‖ ≤ quantitativeSpectralRadialBoundary n) :
      ‖(A.map Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤
        Real.exp
          (-C * Real.exp
            (5 * quantitativeSpectralRadialBoundary n)) := by
    apply norm_realPolynomial_sub_riemannXiSpectral_le_of_sphere_bound
      A (quantitativeSpectralRadialBoundary_pos n)
    · intro u hu
      exact (herror u hu).le
    · exact hw
  apply realPolynomialRootCountInBall_eq_selectedRadialDivisorCount A m
  apply realPolynomialRootCountInBall_mul_eq_circleIntegral_of_norm_sub_lt
    differentiable_riemannXiSpectral
    (quantitativeSpectralRadialBoundary_pos m).le
  intro w hw
  have hwnorm : ‖w‖ = quantitativeSpectralRadialBoundary m := by
    simpa [mem_sphere, dist_zero_right] using hw
  have hwouter : ‖w‖ ≤ quantitativeSpectralRadialBoundary n := by
    rw [hwnorm]
    exact hinnerOuter.le
  calc
    ‖(A.map Complex.ofRealHom).eval w - riemannXiSpectral w‖ ≤
        Real.exp
          (-C * Real.exp
            (5 * quantitativeSpectralRadialBoundary n)) :=
      houterBound hwouter
    _ < Real.exp
          (-C * Real.exp
            (5 * quantitativeSpectralRadialBoundary m)) :=
      quantitativeRadialFloor_lt_of_succ_le hC hmn
    _ ≤ ‖riemannXiSpectral w‖ := hfloor m hwnorm

/-- Under failure of RH, one scheduled canonical Hardy sequence has the
genuine divisor count not only on its own stage circle but simultaneously on
every selected circle at least one index earlier.  Its outside-circle heat
still vanishes at every fixed positive proper time. -/
theorem exists_radialRouche_crossStageDivisor_vanishingHeatTail_sequence_of_not_rh
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
          (∀ (n : ℕ) {w : ℂ},
            ‖w‖ = quantitativeSpectralRadialBoundary n →
              Real.exp
                  (-C * Real.exp
                    (5 * quantitativeSpectralRadialBoundary n)) ≤
                ‖riemannXiSpectral w‖) ∧
          (∀ (n : ℕ) {w : ℂ},
            ‖w‖ = quantitativeSpectralRadialBoundary n →
              ‖((B n).map Complex.ofRealHom).eval w -
                  riemannXiSpectral w‖ <
                Real.exp
                  (-C * Real.exp
                    (5 * quantitativeSpectralRadialBoundary n)) ∧
              ‖((B n).map Complex.ofRealHom).eval w -
                  riemannXiSpectral w‖ < ‖riemannXiSpectral w‖) ∧
          (∀ n : ℕ,
            realPolynomialRootCountInBall (B n) 0
                (quantitativeSpectralRadialBoundary n) =
              riemannXiSpectralRadialDivisorCount
                (quantitativeSpectralRadialBoundary n)) ∧
          (∀ (n m : ℕ), m + 1 ≤ n →
            realPolynomialRootCountInBall (B n) 0
                (quantitativeSpectralRadialBoundary m) =
              riemannXiSpectralRadialDivisorCount
                (quantitativeSpectralRadialBoundary m)) ∧
          ∀ (u : ℂ) (tau : ℝ), 0 < u.im → 0 < tau →
            Tendsto
              (fun n ↦ realPolynomialUpperHeatRemainderOutsideRootMultiset
                (B n) (realPolynomialUpperRootMultisetInsideBall (B n)
                  (quantitativeSpectralRadialBoundary n)) u tau)
              atTop (nhds 0) := by
  obtain ⟨eta, heta, z, hz, A, hA, C, hC, B,
      hindex, hlimit, hfrontier, hgrowth, hfloor, herror⟩ :=
    exists_radialRouche_canonicalFiniteHardyFrontier_sequence_of_not_rh hRH
  let L : ℝ := finiteERootPinnedRadialConstant A eta z
  have hL : 0 < L := by
    simpa [L] using
      (finiteERootPinnedRadialConstant_pos (A := A) (eta := eta) (z := z))
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  refine ⟨eta, heta, z, hz, A, hA, C, hC, B, ?_⟩
  dsimp only
  refine ⟨by simpa [L] using hindex, hlimit, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simpa [L] using hfrontier n
  · intro n
    simpa [L] using hgrowth n
  · intro n w hw
    exact hfloor n hw
  · intro n w hw
    exact herror n hw
  · intro n
    apply realPolynomialRootCountInBall_eq_selectedRadialDivisorCount
    apply realPolynomialRootCountInBall_mul_eq_circleIntegral_of_norm_sub_lt
      differentiable_riemannXiSpectral
      (quantitativeSpectralRadialBoundary_pos n).le
    intro w hw
    exact (herror n (by
      simpa [mem_sphere, dist_zero_right] using hw)).2
  · intro n m hmn
    apply realPolynomialRootCountInBall_eq_earlierRadialDivisorCount
      (B n) hC hfloor hmn
    intro w hw
    exact (herror n hw).1
  · intro u tau hu htau
    apply tendsto_radialRouche_upperHeatRemainderOutsideInsideBall_zero
      hA0 hL.le hC.le B
    · intro n
      simpa [L] using (hfrontier n).2
    · intro n
      simpa [L] using hgrowth n
    · exact hu
    · exact htau

end

end RiemannGaussian

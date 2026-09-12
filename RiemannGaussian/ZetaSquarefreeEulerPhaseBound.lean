/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeEulerPhase
import RiemannGaussian.ZetaSquarefreeEulerFermiRadius

/-!
# Actual squarefree responses with the prime phases retained

The exact Euler decomposition is transported back to the convergent
marked arithmetic series. On a proved analytic disc, its Cauchy estimate
retains the signed first and doubled prime phases in an explicit compact
maximum. All higher harmonics and all squarefree marks have one common
constant, independent of the finite excluded prime set and moment order.

The compact phase maximum is finite for each finite set; no uniform bound
for growing sets is assumed. The original absolute Euler budget remains
available in its own theorem chain.
-/

namespace RiemannGaussian.SquarefreeEulerPhase
noncomputable section
open Complex Filter Topology
open scoped Classical LSeries.notation

/-- The exact phase decomposition represents the original convergent
arithmetic series with every squarefree mark and excluded prime retained. -/
theorem hasSum_marked (J : ℕ) (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    {P : ℕ} (hP : Squarefree P) (hPS : ∀ a ∈ P.primeFactors, a ∉ S)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (RoughSquarefreeBare.coefficient S P) s
      (squarefreeEulerMultiplier ∅ P s *
        Complex.exp (-phase J S s + remainder J S s) * squarefreeEulerResponse s) := by
  have h := LSeriesHasSum_markedSquarefreeEuler S hS hP hPS hs
  rw [multiplier_eq J S hS P hPS (by linarith)] at h
  exact h

/-- Every finite retained harmonic sum is continuous on the whole plane. -/
theorem continuous_phase (J : ℕ) (S : Finset ℕ) : Continuous (phase J S) := by
  unfold phase Complex.logTaylor zetaPrimeFeature
  fun_prop

/-- The actual two-harmonic phase retains the prime angles and their
doubled angles with their distinct damping factors and opposite signs. -/
theorem phase_two_re (S : Finset ℕ) (s : ℂ) :
    (phase 2 S s).re =
      (∑ a ∈ S, zetaPrimeExpWeight s.re a * Real.cos (s.im * Real.log a)) -
      (1 / 2 : ℝ) * ∑ a ∈ S,
        zetaPrimeExpWeight (2 * s.re) a * Real.cos (2 * s.im * Real.log a) := by
  rw [phase_two]
  norm_num [map_sum, CoprimeEulerPhase.feature_re]

/-- The signed phase cost on the complete closed Cauchy disc. -/
def envelope (J : ℕ) (S : Finset ℕ) (c : ℂ) (r : ℝ) : ℝ :=
  sSup ((fun s ↦ Real.exp (-(phase J S s).re)) '' Metric.closedBall c r)

/-- Every point of the disc is bounded by its actual finite phase maximum. -/
theorem le_envelope (J : ℕ) (S : Finset ℕ) (c : ℂ) (r : ℝ)
    {s : ℂ} (hs : s ∈ Metric.closedBall c r) :
    Real.exp (-(phase J S s).re) ≤ envelope J S c r := by
  have hc : Continuous (fun z ↦ Real.exp (-(phase J S z).re)) :=
    ((Complex.continuous_re.comp (continuous_phase J S)).neg).rexp
  exact le_csSup ((isCompact_closedBall c r).bddAbove_image hc.continuousOn) ⟨s, hs, rfl⟩

/-- At every nonnegative radius, the finite phase maximum is positive. -/
theorem envelope_pos (J : ℕ) (S : Finset ℕ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    0 < envelope J S c r :=
  (Real.exp_pos _).trans_le (le_envelope J S c r (Metric.mem_closedBall_self hr))

/-- A uniformly bounded family of actual analytic quotient discs has
one common arithmetic constant. Every center, radius, mark and polynomial
retains its own signed two-harmonic envelope. -/
theorem exists_uniform_response_bound_of_analytic (Y : Set ℝ) (outer M : ℝ)
    (houtu : outer ≤ 9 / 8) (hM0 : 0 ≤ M)
    (hQ : ∀ y ∈ Y, AnalyticOnNhd ℂ squarefreeEulerResponse
      (Metric.closedBall (3 / 2 + I * y) outer))
    (hM : ∀ y ∈ Y, ∀ s ∈ Metric.closedBall (3 / 2 + I * y) outer,
      ‖squarefreeEulerResponse s‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ Y, ∀ (r : ℝ), 0 < r → r ≤ outer →
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
        ∀ (p : Polynomial ℂ) (N : ℕ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨K, hK, hb⟩ := exists_uniform_mark_bound 2
    (by norm_num : (0 : ℝ) < 3 / 8) (by norm_num)
  refine ⟨(M + 1) * K, mul_pos (by linarith) hK, ?_⟩
  intro y hy r hr hro S hS P hP hPS p N
  let c : ℂ := 3 / 2 + I * y
  let A := envelope 2 S c r
  have hA : 0 < A := envelope_pos 2 S c hr.le
  have hedge (s : ℂ) (hs : s ∈ Metric.closedBall c r) : 3 / 8 ≤ s.re := by
    have h := (Complex.abs_re_le_norm (s - c)).trans (mem_closedBall_iff_norm.mp hs)
    dsimp [c] at h
    norm_num at h
    linarith [(abs_le.mp h).1]
  have hsub : Metric.closedBall c r ⊆ Metric.closedBall c outer :=
    Metric.closedBall_subset_closedBall hro
  have hf : AnalyticOnNhd ℂ (squarefreeEulerMultiplier S P) (Metric.closedBall c r) :=
    fun s hs ↦ analyticAt_squarefreeEulerMultiplier S hS P (by linarith [hedge s hs])
  have hfA (s : ℂ) (hs : s ∈ Metric.closedBall c r) :
      ‖squarefreeEulerMultiplier S P s‖ ≤ K * A :=
    (hb S hS P hP hPS s (hedge s hs)).trans
      (mul_le_mul_of_nonneg_left (le_envelope 2 S c r hs) hK.le)
  have ha : AnalyticOnNhd ℂ (fun s ↦ squarefreeEulerMultiplier S P s * squarefreeEulerResponse s)
      (Metric.closedBall c r) := fun s hs ↦ (hf s hs).mul (hQ y hy s (hsub hs))
  have hd : DiffContOnCl ℂ (fun s ↦ squarefreeEulerMultiplier S P s * squarefreeEulerResponse s)
      (Metric.ball c r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    exact ha.differentiableOn
  have hboundary (s : ℂ) (hs : s ∈ Metric.sphere c r) :
      ‖squarefreeEulerMultiplier S P s * squarefreeEulerResponse s‖ ≤
        ((M + 1) * K) * A := by
    have hsB := Metric.sphere_subset_closedBall hs
    have hbound := hM y hy s (hsub hsB)
    rw [norm_mul]
    exact (mul_le_mul (hfA s hsB) (show ‖squarefreeEulerResponse s‖ ≤ M + 1 by linarith)
      (norm_nonneg _) (mul_nonneg hK.le hA.le)).trans_eq (by ring)
  have hmoment (k : ℕ) :
      ‖signedTaylorMoment k (fun s ↦ squarefreeEulerMultiplier S P s * squarefreeEulerResponse s) c‖ ≤
        ((M + 1) * K) * A * r⁻¹ ^ k := by
    simpa only [div_eq_mul_inv, inv_pow] using norm_signedTaylorMoment_le hr hd hboundary k
  rw [RoughSquarefreeBare.response, (hasSum_markedSquarefreeEuler_filter S hS hP hPS p N
    (by norm_num : (1 : ℝ) < (3 / 2 + I * y : ℂ).re)).tsum_eq,
    zetaMomentSequenceFilter, Polynomial.sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * (((M + 1) * K) * A * r⁻¹ ^ (N + k)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hmoment (N + k)) (norm_nonneg _)
    _ = _ := by
      simp_rw [pow_add, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ by ring)

/-- Any proved squarefree analytic disc of radius at most `9/8`
transports to all smaller radii and all valid marked arithmetic filters.
The only prime-set cost is the signed two-harmonic maximum; the constant
controls every higher harmonic and every squarefree mark independently. -/
theorem exists_response_bound_of_analytic (y outer : ℝ)
    (hout : 0 < outer) (houtu : outer ≤ 9 / 8)
    (hQ : AnalyticOnNhd ℂ squarefreeEulerResponse
      (Metric.closedBall (3 / 2 + I * y) outer)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ outer →
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
        ∀ (p : Polynomial ℂ) (N : ℕ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  let c : ℂ := 3 / 2 + I * y
  obtain ⟨M, hM⟩ := ((isCompact_closedBall c outer).image_of_continuousOn
    hQ.continuousOn.norm).isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM _ ⟨c, Metric.mem_closedBall_self hout.le, rfl⟩)
  obtain ⟨C, hC, hb⟩ := exists_uniform_response_bound_of_analytic {y} outer M houtu hM0
    (by intro z hz; simpa only [Set.mem_singleton_iff.mp hz] using hQ)
    (by
      intro z hz s hs
      subst z
      have h := hM _ ⟨s, hs, rfl⟩
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using h)
  exact ⟨C, hC, hb y rfl⟩

/-- The existing unconditional Fermi disc discharges the analytic
premise for the original arithmetic response at every `abs(y)>1`. -/
theorem exists_response_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ squarefreeEulerFermiRadius y →
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
        ∀ (p : Polynomial ℂ) (N : ℕ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k :=
  exists_response_bound_of_analytic y (squarefreeEulerFermiRadius y)
    (by linarith [(squarefreeEulerFermiRadius_bounds hy).1])
    (squarefreeEulerFermiRadius_bounds hy).2.2.1.le
    (analyticOnNhd_squarefreeEulerResponse_fermi hy)

end
end RiemannGaussian.SquarefreeEulerPhase

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeDensityEulerBudget

/-!
# Unscaled squarefree decay under the actual quadratic prime sieve

The Cauchy radius moves down to one from above. Chebyshev prime density
then pays for the entire quadratic sieve, uniformly in every moving
divisibility mark. These are bounds on the genuine complete squarefree
series. Ordinary primes are still included, and growing divisor-pair
families are not asserted to satisfy the same uniform estimate.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Topology
open scoped Classical

/-- Any proved analytic disc transports to every smaller positive
radius and all valid arithmetic marks. The finite Euler allowance and
full complex polynomial envelope remain explicit. -/
theorem exists_squarefreeEuler_variable_radius_bound_of_analytic
    (y outer : ℝ) (hout : 0 < outer) (houtu : outer < 3 / 2)
    (hQ : AnalyticOnNhd ℂ squarefreeEulerResponse
      (Metric.closedBall (3 / 2 + I * y) outer)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ outer →
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
        ∀ (p : Polynomial ℂ) (N : ℕ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * squarefreeEulerBudget (3 / 2 - r) S P * r⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  let c : ℂ := 3 / 2 + I * y
  obtain ⟨M, hM⟩ := ((isCompact_closedBall c outer).image_of_continuousOn
    hQ.continuousOn.norm).isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ ⟨c, Metric.mem_closedBall_self hout.le, rfl⟩)
  refine ⟨M + 1, by linarith, ?_⟩
  intro r hr hro S hS P hP hPS p N
  let A := squarefreeEulerBudget (3 / 2 - r) S P
  have hσ : 0 < 3 / 2 - r := by linarith
  have hedge (s : ℂ) (hs : s ∈ Metric.closedBall c r) : 3 / 2 - r ≤ s.re := by
    have h := (Complex.abs_re_le_norm (s - c)).trans (mem_closedBall_iff_norm.mp hs)
    dsimp [c] at h
    norm_num at h
    linarith [(abs_le.mp h).1]
  have hsub : Metric.closedBall c r ⊆ Metric.closedBall c outer := Metric.closedBall_subset_closedBall hro
  have hf : AnalyticOnNhd ℂ (squarefreeEulerMultiplier S P) (Metric.closedBall c r) :=
    fun s hs ↦ analyticAt_squarefreeEulerMultiplier S hS P (hσ.trans_le (hedge s hs))
  have hfA (s : ℂ) (hs : s ∈ Metric.closedBall c r) : ‖squarefreeEulerMultiplier S P s‖ ≤ A :=
    norm_squarefreeEulerMultiplier_le S hS P hσ (hedge s hs)
  have hA : 0 ≤ A := (norm_nonneg _).trans (hfA c (Metric.mem_closedBall_self hr.le))
  have ha : AnalyticOnNhd ℂ (fun s ↦ squarefreeEulerMultiplier S P s * squarefreeEulerResponse s)
      (Metric.closedBall c r) := fun s hs ↦ (hf s hs).mul (hQ s (hsub hs))
  have hd : DiffContOnCl ℂ (fun s ↦ squarefreeEulerMultiplier S P s * squarefreeEulerResponse s)
      (Metric.ball c r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    exact ha.differentiableOn
  have hb (s : ℂ) (hs : s ∈ Metric.sphere c r) :
      ‖squarefreeEulerMultiplier S P s * squarefreeEulerResponse s‖ ≤ (M + 1) * A := by
    have hsB := Metric.sphere_subset_closedBall hs
    have hbound := hM _ ⟨s, hsub hsB, rfl⟩
    rw [Real.norm_of_nonneg (norm_nonneg _)] at hbound
    rw [norm_mul]
    exact (mul_le_mul (hfA s hsB) (show ‖squarefreeEulerResponse s‖ ≤ M + 1 by linarith)
      (norm_nonneg _) hA).trans_eq (by ring)
  have hmoment (k : ℕ) :
      ‖signedTaylorMoment k (fun s ↦ squarefreeEulerMultiplier S P s * squarefreeEulerResponse s) c‖ ≤
        (M + 1) * A * r⁻¹ ^ k := by
    simpa only [div_eq_mul_inv, inv_pow] using norm_signedTaylorMoment_le hr hd hb k
  rw [RoughSquarefreeBare.response, (hasSum_markedSquarefreeEuler_filter S hS hP hPS p N
    (by norm_num : (1 : ℝ) < (3 / 2 + I * y : ℂ).re)).tsum_eq,
    zetaMomentSequenceFilter, Polynomial.sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * ((M + 1) * A * r⁻¹ ^ (N + k)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hmoment (N + k)) (norm_nonneg _)
    _ = _ := by
      simp_rw [pow_add, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ by ring)

/-- The preceding signed-pole region supplies the original common
Cauchy constant, with every arithmetic mark and polynomial unchanged. -/
theorem exists_squarefreeEuler_variable_radius_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ squarefreeEulerRadius y →
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
        ∀ (p : Polynomial ℂ) (N : ℕ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * squarefreeEulerBudget (3 / 2 - r) S P * r⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k :=
  exists_squarefreeEuler_variable_radius_bound_of_analytic y (squarefreeEulerRadius y)
    (by linarith [(squarefreeEulerRadius_bounds hy).1])
    (by linarith [(squarefreeEulerRadius_bounds hy).2.2.1])
    (analyticOnNhd_squarefreeEulerResponse hy)

private theorem moving_radius_budget (N R : ℕ) (hR : 4 ≤ Real.log (R + 2 : ℝ))
    (hcut : Real.sqrt R ≤ (N : ℝ) / 40) :
    Real.exp (30 * Real.sqrt R / Real.log (R + 2 : ℝ)) *
        (squarefreeEulerMovingRadius R)⁻¹ ^ N ≤
      Real.exp (-(N : ℝ) / (20 * Real.log (R + 2 : ℝ))) := by
  let L := Real.log (R + 2 : ℝ)
  have hL : 0 < L := by dsimp [L]; linarith
  have hi : 0 < L⁻¹ := inv_pos.mpr hL
  have hi4 : L⁻¹ ≤ 1 / 4 := by
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 4) hR
    norm_num at h
    exact h
  have hr0 : 0 < squarefreeEulerMovingRadius R := by
    dsimp [squarefreeEulerMovingRadius, L] at *
    linarith
  have hlog : (4 / 5) * L⁻¹ ≤ Real.log (squarefreeEulerMovingRadius R) := by
    have h := Real.one_sub_inv_le_log_of_pos hr0
    apply le_trans _ h
    change (4 / 5) * L⁻¹ ≤ 1 - (1 + L⁻¹)⁻¹
    have hd : 0 < 1 + L⁻¹ := by positivity
    apply (le_sub_iff_add_le).mpr
    have hx : (1 + L⁻¹)⁻¹ ≤ 1 - (4 / 5) * L⁻¹ := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hd).mpr
      nlinarith
    linarith
  have he : (squarefreeEulerMovingRadius R)⁻¹ ^ N =
      Real.exp (-(N : ℝ) * Real.log (squarefreeEulerMovingRadius R)) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hr0, inv_pow]
  rw [he, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg N)
  have hcut' : 30 * Real.sqrt R / L ≤ (3 / 4) * (N : ℝ) / L := by
    apply div_le_div_of_nonneg_right _ hL.le
    linarith
  dsimp [L] at hmul hcut' ⊢
  simp only [div_eq_mul_inv, mul_inv_rev] at hmul hcut' ⊢
  nlinarith

/-- The complete unscaled squarefree arithmetic response decays for
every prime subset of a growing cutoff with sqrt(R_N) at most N/40.
The same estimate holds simultaneously for all marks and polynomials. -/
theorem exists_squarefreeEuler_quadratic_sieve_bound (y : ℝ) (hy : 1 < |y|)
    (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hcut : ∀ᶠ N in atTop, Real.sqrt (R N) ≤ (N : ℝ) / 40) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime ∧ a ≤ R N) → ∀ (P : ℕ) (p : Polynomial ℂ),
        ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
          C * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) *
            ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_squarefreeEuler_variable_radius_bound y hy
  obtain ⟨A, hA, hbudget⟩ := exists_squarefreeEulerBudget_moving_radius_bound
  have hrad := ((tendsto_squarefreeEulerMovingRadius.comp hR).eventually
    (gt_mem_nhds (squarefreeEulerRadius_bounds hy).1))
  have hx : Tendsto (fun N : ℕ ↦ (R N : ℝ) + 2) atTop atTop :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hR).atTop_add tendsto_const_nhds
  have hlog := (Real.tendsto_log_atTop.comp hx).eventually_ge_atTop 4
  refine ⟨C * A, mul_pos hC hA, ?_⟩
  filter_upwards [hR.eventually hbudget, hcut, hrad, hlog] with N hbudget hcut hrad hlog S hS P p
  change squarefreeEulerMovingRadius (R N) < squarefreeEulerRadius y at hrad
  change 4 ≤ Real.log (R N + 2 : ℝ) at hlog
  let r := squarefreeEulerMovingRadius (R N)
  have hr1 : 1 ≤ r := by
    have hL : 0 < Real.log (R N + 2 : ℝ) := by linarith
    exact le_add_of_nonneg_right (inv_nonneg.mpr hL.le)
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have henv : (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) ≤ ∑ k ∈ p.support, ‖p.coeff k‖ := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (inv_nonneg.mpr hr.le)
      (inv_le_one_of_one_le₀ hr1))
  by_cases hgood : Squarefree P ∧ ∀ a ∈ P.primeFactors, a ∉ S
  · obtain ⟨hP, hPS⟩ := hgood
    have h := hb r hr hrad.le S (fun a ha ↦ (hS a ha).1) P hP hPS p N
    have ha := hbudget S hS P hP hPS
    have hrate := moving_radius_budget N (R N) hlog hcut
    calc
      _ ≤ C * squarefreeEulerBudget (3 / 2 - r) S P * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := h
      _ ≤ C * (A * Real.exp (30 * Real.sqrt (R N) / Real.log (R N + 2 : ℝ))) * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ := by
        apply mul_le_mul _ henv (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hC.le) (by positivity)
      _ = (C * A) * (Real.exp (30 * Real.sqrt (R N) / Real.log (R N + 2 : ℝ)) * r⁻¹ ^ N) *
          ∑ k ∈ p.support, ‖p.coeff k‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrate (by positivity))
        (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
  · have hz (n : ℕ) : RoughSquarefreeBare.coefficient S P n = 0 := by
      have hn : ¬(Squarefree n ∧ (¬∃ a ∈ S, a ∣ n) ∧ P ∣ n) := by
        rintro ⟨hn, hs, hd⟩
        exact hgood ⟨hn.squarefree_of_dvd hd,
          fun a ha haS ↦ hs ⟨a, haS, (Nat.dvd_of_mem_primeFactors ha).trans hd⟩⟩
      simp only [RoughSquarefreeBare.coefficient, if_neg hn]
    simp only [RoughSquarefreeBare.response, hz, zero_mul, tsum_zero, norm_zero]
    positivity

/-- The explicit quadratic-sieve allowance tends to zero. No lower
growth condition on the cutoff is needed for this numerical limit. -/
theorem tendsto_squarefreeEuler_quadratic_sieve_allowance (R : ℕ → ℕ)
    (hcut : ∀ᶠ N in atTop, Real.sqrt (R N) ≤ (N : ℝ) / 40) :
    Tendsto (fun N : ℕ ↦ Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))))
      atTop (𝓝 0) := by
  have hx : Tendsto (fun N : ℕ ↦ (N : ℝ) + 2) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N + 2 : ℝ) / N) atTop (𝓝 0) := by
    convert (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 (by norm_num)).comp hx using 1
    funext N
    simp
  have hbound : ∀ᶠ N in atTop,
      Real.log (R N + 2 : ℝ) / N ≤ 2 * (Real.log (N + 2 : ℝ) / N) := by
    filter_upwards [hcut, eventually_ge_atTop 1] with N hcut hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hs := Real.sq_sqrt (Nat.cast_nonneg (R N))
    have hR : (R N : ℝ) ≤ (N : ℝ) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (R N)]
    have h := Real.log_le_log (show (0 : ℝ) < R N + 2 by positivity)
      (show (R N + 2 : ℝ) ≤ (N + 2 : ℝ) ^ 2 by nlinarith)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h hN0.le
  have hzero : Tendsto (fun N : ℕ ↦ Real.log (R N + 2 : ℝ) / N) atTop (𝓝 0) := by
    apply squeeze_zero' _ hbound (by simpa using hlog.const_mul 2)
    exact Eventually.of_forall (fun N ↦ div_nonneg
      (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (R N); linarith)) (Nat.cast_nonneg _))
  have hpos : ∀ᶠ N in atTop, Real.log (R N + 2 : ℝ) / N ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact div_pos (Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) (R N); linarith))
      (by exact_mod_cast (show 0 < N by omega))
  have hinv := (tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩).inv_tendsto_nhdsGT_zero
  have hscale := hinv.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 20)
  have hneg := tendsto_neg_atTop_atBot.comp hscale
  convert (Real.tendsto_exp_atBot.comp hneg) using 1
  funext N
  simp only [Function.comp_apply, Pi.inv_apply, inv_div]
  congr 1
  ring

/-- Every changing prime subset and every changing natural mark
satisfy unscaled arithmetic decay under the stated quadratic cutoff.
There is no coefficient search and no zeta-zero hypothesis. -/
theorem tendsto_squarefreeEuler_quadratic_sieve (y : ℝ) (hy : 1 < |y|)
    (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hcut : ∀ᶠ N in atTop, Real.sqrt (R N) ≤ (N : ℝ) / 40)
    (S : ℕ → Finset ℕ) (hS : ∀ N a, a ∈ S N → a.Prime ∧ a ≤ R N)
    (P : ℕ → ℕ) (p : Polynomial ℂ) :
    Tendsto (fun N ↦ RoughSquarefreeBare.response p (S N) (P N) N (3 / 2 + I * y))
      atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_squarefreeEuler_quadratic_sieve_bound y hy R hR hcut
  apply squeeze_zero_norm' (hb.mono (fun N hN ↦ hN (S N) (hS N) (P N) p))
  simpa only [mul_zero, zero_mul] using
    ((tendsto_squarefreeEuler_quadratic_sieve_allowance R hcut).const_mul C).mul_const
      (∑ k ∈ p.support, ‖p.coeff k‖)

/-- The actual quadratic prime sieve satisfies the required slope
bound at every order, with its integer rounding fully retained. -/
theorem sqrt_zetaRightHalfPrimePatternCutoff_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    Real.sqrt (zetaRightHalfPrimePatternCutoff rho N) ≤ (N : ℝ) / 40 := by
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 1 / 2 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu0 : 0 < u := by linarith
  have hs : 25 / 36 < Real.sqrt u := by
    nlinarith [Real.sq_sqrt hu0.le, Real.sqrt_nonneg u]
  have ht : 5 / 6 < Real.sqrt (Real.sqrt u) := by
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg u), Real.sqrt_nonneg (Real.sqrt u)]
  have hq : zetaMoebiusHeadGrowth u ≤ 6 / 5 := by
    unfold zetaMoebiusHeadGrowth
    rw [← one_div]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hu0))).mpr
    linarith
  have hq0 : 0 < zetaMoebiusHeadGrowth u := zero_lt_one.trans
    (one_lt_zetaMoebiusHeadGrowth hu0 (by dsimp [u]; linarith))
  have hlog : Real.log (zetaMoebiusHeadGrowth u) ≤ 1 / 5 := by
    have h := Real.log_le_sub_one_of_pos hq0
    linarith
  have hc : zetaRightHalfPrimePatternSlope rho ≤ 1 / 40 := by
    dsimp [zetaRightHalfPrimePatternSlope, u] at *
    linarith
  rw [zetaRightHalfPrimePatternCutoff, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]
  apply (Nat.floor_le (mul_nonneg (zetaRightHalfPrimePatternSlope_pos rho hrho).le
    (Nat.cast_nonneg N))).trans
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- The full sieve used by the current RH carrier now has independent
unscaled squarefree decay for every moving mark and every fixed complex
polynomial. The original ordinary-prime terms remain included. -/
theorem tendsto_squarefreeEuler_actual_quadratic_sieve (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (P : ℕ → ℕ) (p : Polynomial ℂ) :
    Tendsto (fun N ↦ RoughSquarefreeBare.response p (zetaRightHalfPrimePatternPrimes rho N)
      (P N) N (3 / 2 + I * rho.1.im)) atTop (𝓝 0) := by
  exact tendsto_squarefreeEuler_quadratic_sieve rho.1.im (nontrivialZetaZero_one_lt_abs_im rho)
    (zetaRightHalfPrimePatternCutoff rho) (tendsto_zetaRightHalfPrimePatternCutoff rho hrho)
    (Eventually.of_forall (sqrt_zetaRightHalfPrimePatternCutoff_le rho hrho))
    (zetaRightHalfPrimePatternPrimes rho) (zetaRightHalfPrimePatternPrimes_eligible rho) P p

end
end RiemannGaussian

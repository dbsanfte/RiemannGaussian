/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeWindowLocalization
import RiemannGaussian.ZetaSquarefreeEulerPrimeTailSource
import RiemannGaussian.ZetaMoebiusFractionalBudgetAudit

/-!
# Mandatory cancellation between actual prime-tail windows

The all-filter local growth theorem applies to the actual zero-isolating
pole-jet polynomial. Its logarithmic window around `N/u` lies beyond both
original arithmetic cutoffs. The window norm diverges at source scale,
while the complete signed tail has its previously proved finite source
limit. Thus cancellation with the complement must be retained. This is an
obstruction to intervalwise norm estimates, not an independent prime-tail
floor or a new zero-free region.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian.PrimeWindow
noncomputable section

/-- A fixed positive logarithmic width with phase variation below one. -/
def phaseWidth (y : ℝ) : ℝ := 1 / (|y| + 1)

/-- The phase window is nonempty in logarithmic coordinates at every height. -/
theorem phaseWidth_pos (y : ℝ) : 0 < phaseWidth y := by
  unfold phaseWidth
  positivity

/-- The complete phase changes by at most one radian over the window. -/
theorem mul_phaseWidth_le_one (y : ℝ) : |y| * phaseWidth y ≤ 1 := by
  rw [phaseWidth, mul_one_div, div_le_one (by positivity)]
  linarith

/-- The squared divisor schedule lies below `exp(N)`, with the integer
floor preserved. This is below the normalized window at every right-half zero. -/
theorem square_divisor_cutoff_le_exp {u : ℝ} (hu : 1 / 2 < u) (N D : ℕ)
    (hD : D ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N) ^ 2) :
    (D : ℝ) ≤ Real.exp (N : ℝ) := by
  have hu0 : 0 < u := by linarith
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hhalf : 1 / 2 ≤ Real.sqrt u := by
    nlinarith [Real.sq_sqrt hu0.le, Real.sqrt_nonneg u]
  have hq : 0 ≤ zetaMoebiusHeadGrowth u := by unfold zetaMoebiusHeadGrowth; positivity
  have hq2 : zetaMoebiusHeadGrowth u ^ 2 ≤ 2 := by
    rw [zetaMoebiusHeadGrowth, inv_pow, Real.sq_sqrt (Real.sqrt_nonneg u), ← one_div]
    exact (div_le_iff₀ hs).mpr (by linarith)
  have hf : (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N : ℝ) ≤
      zetaMoebiusHeadGrowth u ^ N := Nat.floor_le (pow_nonneg hq N)
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N : ℝ) ^ 2 := by exact_mod_cast hD
    _ ≤ (zetaMoebiusHeadGrowth u ^ N) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hf 2
    _ = (zetaMoebiusHeadGrowth u ^ 2) ^ N := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (2 : ℝ) ^ N := pow_le_pow_left₀ (sq_nonneg _) hq2 N
    _ ≤ Real.exp 1 ^ N := pow_le_pow_left₀ (by norm_num) he N
    _ = _ := by rw [← Real.exp_nat_mul, mul_one]

/-- The original simultaneous prime sieve also ends below `exp(N)`;
its exact square-root budget is enough at every order. -/
theorem prime_sieve_cutoff_le_exp (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    (zetaRightHalfPrimePatternCutoff rho N : ℝ) ≤ Real.exp (N : ℝ) := by
  have hs := sqrt_zetaRightHalfPrimePatternCutoff_le rho hrho N
  have hs0 := Real.sqrt_nonneg (zetaRightHalfPrimePatternCutoff rho N : ℝ)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (zetaRightHalfPrimePatternCutoff rho N))
  have ht := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) 2
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at ht
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Every prime in the all-filter window survives both original cutoffs.
The obstruction is in the unchanged surviving prime tail. -/
theorem source_window_primes_survive (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N D : ℕ) (h : ℝ)
    (hD : D ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2)
    {a : ℕ} (ha : a ∈ primesInWindow
      (Real.exp ((3 / 2 - rho.1.re)⁻¹ * N)) (Real.exp h)) :
    a.Prime ∧ D < a ∧ a ∉ zetaRightHalfPrimePatternPrimes rho N := by
  have hu : 1 / 2 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu0 : 0 < 3 / 2 - rho.1.re := by linarith
  have hc : 1 ≤ (3 / 2 - rho.1.re)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hu0]
    linarith
  have he : Real.exp (N : ℝ) ≤ Real.exp ((3 / 2 - rho.1.re)⁻¹ * N) :=
    Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  have hm := mem_primesInWindow_bounds (Real.exp_pos _).le (Real.exp_pos h).le ha
  have hDb := (square_divisor_cutoff_le_exp hu N D hD).trans he
  have hRb := (prime_sieve_cutoff_le_exp rho hrho N).trans he
  refine ⟨hm.2.2, ?_, ?_⟩
  · exact_mod_cast hDb.trans_lt hm.1
  · intro haS
    have h := (zetaRightHalfPrimePatternPrimes_eligible rho N a haS).2
    have haR : (a : ℝ) ≤ zetaRightHalfPrimePatternCutoff rho N := by exact_mod_cast h
    linarith [hm.1]

/-- A finite restriction of the original prime-tail coefficient, with
its sieve and polynomial kernel retained in the definition. -/
def tailMoment (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (y h t : ℝ) : ℂ :=
  ∑ a ∈ primesInWindow (Real.exp t) (Real.exp h),
    SquarefreeEulerQuadratic.primeCorrectionCoefficient D S a *
      zetaPrimeFilterKernel p N (3 / 2 + I * y) a

/-- Subtracting the finite window is exactly the convergent sum outside
that window. The complex arithmetic summand and both cutoffs are unchanged. -/
theorem primeLogResponse_sub_tailMoment_eq (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (N : ℕ) (y h t : ℝ) :
    SquarefreeEulerQuadratic.primeLogResponse p D S N (3 / 2 + I * y) -
      tailMoment p D S N y h t =
        ∑' a, if a ∈ primesInWindow (Real.exp t) (Real.exp h) then 0 else
          SquarefreeEulerQuadratic.primeCorrectionCoefficient D S a *
            zetaPrimeFilterKernel p N (3 / 2 + I * y) a := by
  let f : ℕ → ℂ := fun a ↦ SquarefreeEulerQuadratic.primeCorrectionCoefficient D S a *
    zetaPrimeFilterKernel p N (3 / 2 + I * y) a
  let W := primesInWindow (Real.exp t) (Real.exp h)
  change (∑' a, f a) - ∑ a ∈ W, f a = ∑' a, if a ∈ W then 0 else f a
  have hf : Summable f := SquarefreeEulerQuadratic.summable_primeLogResponse p D S hS N
    (by norm_num : (1 : ℝ) < (3 / 2 + I * y : ℂ).re)
  have hs := hf.sum_add_tsum_compl (s := W)
  rw [tsum_subtype] at hs
  have he : ((W : Set ℕ)ᶜ).indicator f = (fun a ↦ if a ∈ W then 0 else f a) := by
    funext a
    by_cases ha : a ∈ W <;> simp [ha]
  rw [he] at hs
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hs.symm)

/-- The all-filter window is exactly the corresponding finite restriction
of the actual prime tail, for every eligible divisor cutoff and polynomial. -/
theorem tailMoment_eq_filteredMoment (p : Polynomial ℂ)
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N D : ℕ) (h : ℝ)
    (hD1 : 1 ≤ D)
    (hD : D ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2) :
    tailMoment p D (zetaRightHalfPrimePatternPrimes rho N) N rho.1.im h
        ((3 / 2 - rho.1.re)⁻¹ * N) =
      filteredMoment p N rho.1.im h ((3 / 2 - rho.1.re)⁻¹ * N) := by
  apply Finset.sum_congr rfl
  intro a ha
  have hm := source_window_primes_survive rho hrho N D h hD ha
  rw [SquarefreeEulerQuadratic.primeCorrectionCoefficient_eq_prime_tail hD1 _
    (fun b hb ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N b hb).1)]
  simp [hm.1, hm.2.1, hm.2.2]

/-- The actual pole-jet filter's finite tail window, with its original
complex source normalization. -/
def normalizedTailWindow (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (N D : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    tailMoment (zetaRightHalfPoleJetFilter rho hrho) D (zetaRightHalfPrimePatternPrimes rho N)
      N rho.1.im (phaseWidth rho.1.im) ((3 / 2 - rho.1.re)⁻¹ * N)

/-- The full zero-isolating pole-jet filter has an unbounded raw window
inside the original prime tail. This follows from actual prime counting and
filter normalization, without using the signed source-limit theorem. -/
theorem norm_normalizedTailWindow_tendsto (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N ∧
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2) :
    Tendsto (fun N ↦ ‖normalizedTailWindow rho hrho N (D N)‖) atTop atTop := by
  have hu : 1 / 2 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu0 : 0 < 3 / 2 - rho.1.re := by linarith
  have h := every_normalized_filter_has_large_windows (zetaRightHalfPoleJetFilter rho hrho)
    hu (phaseWidth_pos rho.1.im) (mul_phaseWidth_le_one rho.1.im)
    (zetaRightHalfPoleJetFilter_eval_selected rho hrho)
  apply h.congr'
  filter_upwards [hD] with N hN
  rw [normalizedTailWindow, tailMoment_eq_filteredMoment _ rho hrho N (D N) _ hN.1 hN.2,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]

/-- Relative to the growing local window, the entire signed tail is
negligible. The finite source limit is used here, after the independent
window-growth theorem has already been proved. -/
theorem normalizedPrimeTail_div_window_tendsto_zero (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N ∧
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2) :
    Tendsto (fun N ↦ SquarefreeEulerQuadratic.normalizedPrimeLogResponse rho hrho N (D N) /
      normalizedTailWindow rho hrho N (D N)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_div] using
    (SquarefreeEulerQuadratic.tendsto_normalizedPrimeLogResponse rho hrho D hD).norm.div_atTop
      (norm_normalizedTailWindow_tendsto rho hrho D hD)

/-- The complementary signed tail has asymptotically the opposite full
complex amplitude of the local window. This records the cancellation that
separate interval norms would destroy, without proving the missing floor. -/
theorem complementaryPrimeTail_div_window_tendsto_neg_one (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N ∧
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2) :
    Tendsto (fun N ↦
      (SquarefreeEulerQuadratic.normalizedPrimeLogResponse rho hrho N (D N) -
        normalizedTailWindow rho hrho N (D N)) / normalizedTailWindow rho hrho N (D N))
      atTop (𝓝 (-1)) := by
  have h := (normalizedPrimeTail_div_window_tendsto_zero rho hrho D hD).sub_const 1
  simp only [zero_sub] at h
  apply h.congr'
  filter_upwards [(norm_normalizedTailWindow_tendsto rho hrho D hD).eventually_gt_atTop 0]
    with N hN
  rw [sub_div, div_self (norm_pos_iff.mp hN)]

end
end RiemannGaussian.PrimeWindow

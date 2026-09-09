/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusTailPrimePowers
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# The zero source requires interactions between distinct primes

The exact Möbius tail is partitioned into prime-power and distinct-prime
coefficients before any estimate. The independently negligible first part
leaves the full selected-zero source in a genuine convergent sum over
integers with at least two distinct prime factors. Its opposite signed
arithmetic estimate remains the open obligation.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The signed coefficient restricted to integers with at least two
distinct prime factors, with the original divisor cutoff unchanged. -/
def zetaMoebiusDistinctPrimeCoefficient (D n : ℕ) : ℂ :=
  if n.primeFactors.Nontrivial then zetaMoebiusLogTailCoefficient D n else 0

/-- Every literal divisor coefficient splits exactly into its
single-prime and distinct-prime contributions, including indices zero and one. -/
theorem zetaMoebiusLogTailCoefficient_eq_primePower_add_distinct (D n : ℕ) :
    zetaMoebiusLogTailCoefficient D n = zetaMoebiusTailPrimePowerCoefficient D n +
      zetaMoebiusDistinctPrimeCoefficient D n := by
  by_cases hn : 2 ≤ n
  · have he := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).symm
    simp only [zetaMoebiusTailPrimePowerCoefficient, zetaMoebiusDistinctPrimeCoefficient, he]
    split_ifs <;> simp_all
  · have hz := zetaMoebiusLogTailCoefficient_eq_zero_of_lt D n (by omega)
    simp [zetaMoebiusTailPrimePowerCoefficient, zetaMoebiusDistinctPrimeCoefficient, hz]

/-- A nonzero surviving coefficient requires two actual distinct prime
divisors, and its index lies beyond twice the first retained Möbius divisor. -/
theorem zetaMoebiusDistinctPrimeCoefficient_support (D n : ℕ)
    (hn : zetaMoebiusDistinctPrimeCoefficient D n ≠ 0) :
    2 * (D + 1) ≤ n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ n ∧ q ∣ n := by
  have hnon : n.primeFactors.Nontrivial := by
    by_contra h
    simp [zetaMoebiusDistinctPrimeCoefficient, h] at hn
  have hA : zetaMoebiusLogTailCoefficient D n ≠ 0 := by
    simpa [zetaMoebiusDistinctPrimeCoefficient, hnon] using hn
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hA (zetaMoebiusLogTailCoefficient_eq_zero_of_lt D n (lt_of_not_ge h))
  · obtain ⟨p, hp, q, hq, hpq⟩ := hnon
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    exact ⟨p, q, hpp, hqp, hpq, hpd, hqd⟩

/-- The actual factorial moment of the distinct-prime arithmetic tail. -/
def zetaMoebiusDistinctPrimeMoment (D k : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaMoebiusDistinctPrimeCoefficient D n * zetaPrimeLogKernel k s n

/-- The distinct-prime series genuinely converges and equals the
full Möbius-tail moment minus its independently controlled prime-power part. -/
theorem hasSum_zetaMoebiusDistinctPrimeMoment (D : ℕ) (hD : 1 ≤ D) (k : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaMoebiusDistinctPrimeCoefficient D n * zetaPrimeLogKernel k s n)
      (zetaMoebiusLogTailMoment D k s - zetaMoebiusTailPrimePowerMoment D k s) := by
  have h := (hasSum_zetaMoebiusLogTailMoment D k hs).sub
    (summable_zetaMoebiusTailPrimePowerMoment D hD k (by linarith : 1 / 2 < s.re)).hasSum
  apply h.congr_fun
  intro n
  rw [zetaMoebiusLogTailCoefficient_eq_primePower_add_distinct D n]
  unfold zetaPrimeLogKernel
  ring

/-- The higher-moment split retains both complete complex arithmetic parts. -/
theorem zetaMoebiusLogTailMoment_eq_primePower_add_distinct (D : ℕ) (hD : 1 ≤ D) (k : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    zetaMoebiusLogTailMoment D k s = zetaMoebiusTailPrimePowerMoment D k s +
      zetaMoebiusDistinctPrimeMoment D k s := by
  have h := (hasSum_zetaMoebiusDistinctPrimeMoment D hD k hs).tsum_eq
  change zetaMoebiusDistinctPrimeMoment D k s = _ at h
  rw [h]
  ring

/-- A polynomial filter of the full signed distinct-prime tail. -/
def zetaMoebiusDistinctPrimeFilter (p : Polynomial ℂ) (D N : ℕ) (s : ℂ) : ℂ :=
  zetaMomentSequenceFilter p (fun n ↦ zetaMoebiusDistinctPrimeMoment D n s) N

/-- The exact moment filter is a single convergent arithmetic sum with
all divisor signs and logarithmic phases still coupled. -/
theorem hasSum_zetaMoebiusDistinctPrimeFilter (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ zetaMoebiusDistinctPrimeCoefficient D n * zetaPrimeFeature s n *
      ∑ k ∈ p.support, p.coeff k * ((Real.log n : ℂ) ^ (N + k) / ((N + k).factorial : ℂ)))
      (zetaMoebiusDistinctPrimeFilter p D N s) := by
  have h := hasSum_sum (s := p.support) (fun k _ ↦
    (hasSum_zetaMoebiusDistinctPrimeMoment D hD (N + k) hs).summable.hasSum.mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold zetaPrimeLogKernel
  ring

/-- Polynomial filters preserve the exact prime-power/distinct-prime
decomposition before the first part is estimated. -/
theorem zetaMoebiusLogTailFilter_eq_primePower_add_distinct (p : Polynomial ℂ)
    (D N : ℕ) (hD : 1 ≤ D) {s : ℂ} (hs : 1 < s.re) :
    zetaMoebiusLogTailFilter p D N s = zetaMoebiusTailPrimePowerFilter p D N s +
      zetaMoebiusDistinctPrimeFilter p D N s := by
  simp only [zetaMoebiusLogTailFilter, zetaMoebiusTailPrimePowerFilter,
    zetaMoebiusDistinctPrimeFilter, zetaMomentSequenceFilter, Polynomial.sum,
    zetaMoebiusLogTailMoment_eq_primePower_add_distinct D hD _ hs, mul_add, Finset.sum_add_distrib]

/-- Both removed arithmetic pieces fit the same explicit geometric
error rate. Thus replacing the complete prime filter by distinct-prime
interactions alone has a proved independent error bound at every order. -/
theorem exists_zetaRightHalfDistinctPrimeTail_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaMoebiusDistinctPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
            (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) N
            (3 / 2 + I * rho.1.im))‖ ≤ C * (Real.sqrt (3 / 2 - rho.1.re)) ^ N := by
  let u := 3 / 2 - rho.1.re
  let p := zetaRightHalfPoleJetFilter rho hrho
  let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u)
  let s : ℂ := 3 / 2 + I * rho.1.im
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hD (N : ℕ) : 1 ≤ D N :=
    (Nat.one_le_floor_iff _).mpr (one_le_pow₀ (one_lt_zetaMoebiusHeadGrowth hu hu1).le)
  have hs : 1 < s.re := by dsimp [s]; norm_num
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_zetaRightHalfPoleJetTail_error_bound rho hrho
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_zetaMoebiusTailPrimePowerFilter_geometric_bound p rho.1.im D hD hu hu1
  refine ⟨C₁ + C₂, by linarith, fun N ↦ ?_⟩
  change ‖(u : ℂ) ^ (N + 1) * (zetaPrimeLogFilter p N s - zetaMoebiusDistinctPrimeFilter p (D N) N s)‖ ≤
    (C₁ + C₂) * (Real.sqrt u) ^ N
  have he : (u : ℂ) ^ (N + 1) * (zetaPrimeLogFilter p N s - zetaMoebiusDistinctPrimeFilter p (D N) N s) =
      (u : ℂ) ^ (N + 1) * (zetaPrimeLogFilter p N s - zetaMoebiusLogTailFilter p (D N) N s) +
        (u : ℂ) ^ (N + 1) * zetaMoebiusTailPrimePowerFilter p (D N) N s := by
    rw [zetaMoebiusLogTailFilter_eq_primePower_add_distinct p _ N (hD N) hs]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  have h₁ : ‖(u : ℂ) ^ (N + 1) * (zetaPrimeLogFilter p N s - zetaMoebiusLogTailFilter p (D N) N s)‖ ≤
      C₁ * (Real.sqrt u) ^ N := hb₁ N
  have h₂ : ‖(u : ℂ) ^ (N + 1) * zetaMoebiusTailPrimePowerFilter p (D N) N s‖ ≤
      C₂ * (Real.sqrt u) ^ N := hb₂ N
  nlinarith

/-- Every hypothetical right-half zero retains its full complex
multiplicity source on integers with at least two distinct prime factors.
The discarded prime-power contribution is independently bounded uniformly
over the actual growing cutoff. -/
theorem tendsto_zetaRightHalfDistinctPrimeTail (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusDistinctPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) N
        (3 / 2 + I * rho.1.im)) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hD := (tendsto_zetaRightHalfPoleJetCutoff rho hrho).eventually_ge_atTop 1
  have hu : 0 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have ha : ‖((3 / 2 - rho.1.re : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    linarith
  have h := (tendsto_zetaRightHalfPoleJetTail rho hrho).sub
    (tendsto_zetaMoebiusTailPrimePowerFilter_mul_pow (zetaRightHalfPoleJetFilter rho hrho) rho.1.im _ hD ha)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [hD] with N hN
  rw [zetaMoebiusLogTailFilter_eq_primePower_add_distinct _ _ _ hN (by norm_num),
    mul_add, add_sub_cancel_left]

/-- The actual signed real source survives in the distinct-prime tail. -/
theorem tendsto_zetaRightHalfDistinctPrimeTail_re (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ (3 / 2 - rho.1.re) ^ (N + 1) *
      (zetaMoebiusDistinctPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) N
        (3 / 2 + I * rho.1.im)).re) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℝ))) := by
  simpa only [Function.comp_def, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.neg_re, Complex.natCast_re] using
    (Complex.continuous_re.tendsto _).comp (tendsto_zetaRightHalfDistinctPrimeTail rho hrho)

/-- The selected zero forces an eventual negative real source in the
distinct-prime interactions alone. Their independent opposite signed
estimate is the remaining open arithmetic target. -/
theorem zetaRightHalfDistinctPrimeTail_eventually_negative (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∀ᶠ N : ℕ in atTop,
      (zetaMoebiusDistinctPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) N
        (3 / 2 + I * rho.1.im)).re <
          -(analyticZetaZeroMultiplicity rho : ℝ) / (2 * (3 / 2 - rho.1.re) ^ (N + 1)) := by
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hu : 0 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (tendsto_zetaRightHalfDistinctPrimeTail_re rho hrho).eventually
    (gt_mem_nhds (by linarith : -(analyticZetaZeroMultiplicity rho : ℝ) <
      -(analyticZetaZeroMultiplicity rho : ℝ) / 2))
  filter_upwards [h] with N hN
  rw [lt_div_iff₀ (mul_pos (by norm_num) (pow_pos hu _))]
  nlinarith

end

end RiemannGaussian

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAnnulusJoint

/-!
# Independent control of the mixed completion prefix

The mixed prefix pairs an intermediate prime with a prime at most N^2.
Its actual logarithmic mark belongs to the intermediate prime. Unique
integer support and the physical cutoff give a polynomial times strict
geometric bound on 1/2<u<exp(-1/2), for every changing selected family.
No zero or prime-cancellation premise is used.
-/

namespace RiemannGaussian.ZetaRieszMixedPrefix
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszGeneralCofactorTilt ZetaRieszCofactorTiltRate
open ZetaRieszCrossCompletion ZetaRieszSemiprimeCompletion

/-- A linear logarithmic allowance retains the exact physical floor and
the entire quadratic multiplicative head. -/
theorem log_quadratic_physical_le {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (N n : ℕ) (hn : 0 < n)
    (hbound : n ≤ (N + 1) ^ 2 *
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    Real.log n ≤ (2 * (1 + Real.log 3 + Real.log u⁻¹)) * (N + 1) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hi : 0 ≤ Real.log u⁻¹ := Real.log_nonneg ((one_le_inv₀ hu).mpr hu1)
  have hl3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hcut := ZetaRieszExponentialCofactor.cutoff_add_two_le hu hu1 N
  have hb : (n : ℝ) ≤ ((N : ℝ) + 1) ^ 2 * (3 * u⁻¹ ^ N) ^ 2 := by
    calc
      _ ≤ ((N : ℝ) + 1) ^ 2 *
          (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ^ 2 := by
        exact_mod_cast hbound
      _ ≤ _ := by gcongr
  calc
    Real.log n ≤ Real.log (((N : ℝ) + 1) ^ 2 * (3 * u⁻¹ ^ N) ^ 2) :=
      Real.log_le_log (by exact_mod_cast hn) hb
    _ = 2 * Real.log ((N : ℝ) + 1) +
        2 * (Real.log 3 + (N : ℝ) * Real.log u⁻¹) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
        Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    _ ≤ 2 * (N : ℝ) + 2 * (Real.log 3 + (N : ℝ) * Real.log u⁻¹) := by
      gcongr
      have h := Real.log_le_sub_one_of_pos hN
      linarith
    _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Every coefficient bounded by one logarithm on this whole physical
prefix has a polynomial times geometric allowance, uniform in all phases
and in the selected integer set. No prime-distribution estimate is used. -/
theorem norm_log_prefix_le (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (T : Finset ℕ) (f : ℕ → ℂ) {u q : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hq : 1 / 2 < q) (hq1 : q ≤ 1)
    (hT : ∀ n ∈ T, 0 < n ∧ n ≤ (N + 1) ^ 2 *
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hf : ∀ n ∈ T, ‖f n‖ ≤ Real.log n) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ T,
      f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      (2 * (1 + Real.log 3 + Real.log u⁻¹) * tiltCost P u q) *
        ((N : ℝ) + 1) ^ 3 * tiltRate u q ^ N := by
  have hi : 0 ≤ Real.log u⁻¹ := Real.log_nonneg ((one_le_inv₀ hu).mpr hu1)
  have hl3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hC : 0 ≤ 2 * (1 + Real.log 3 + Real.log u⁻¹) := by positivity
  have hb := norm_sum_filter_square_cutoff_le_tilt P N ((N + 1) ^ 2) y T f
    (mul_nonneg hC (by positivity)) hu hu1 hq hT
    (fun n hn => (hf n hn).trans (log_quadratic_physical_le hu hu1 N n
      (hT n hn).1 (hT n hn).2))
  have hpow : (((N + 1) ^ 2 : ℕ) : ℝ) ^ (q - 1 / 2) ≤ ((N : ℝ) + 1) ^ 2 := by
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ (((N : ℝ) + 1) ^ 2) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · nlinarith [Nat.cast_nonneg (α := ℝ) N]
        · linarith
      _ = _ := Real.rpow_one _
  have hrate0 : 0 ≤ tiltRate u q ^ N := pow_nonneg (tiltRate_pos u (by linarith)).le N
  calc
    _ ≤ (2 * (1 + Real.log 3 + Real.log u⁻¹) * tiltCost P u q) *
        ((N : ℝ) + 1) * (((N + 1) ^ 2 : ℕ) : ℝ) ^ (q - 1 / 2) * tiltRate u q ^ N := by
      convert hb using 1
      unfold tiltCost
      ring
    _ ≤ (2 * (1 + Real.log 3 + Real.log u⁻¹) * tiltCost P u q) *
        ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ 2 * tiltRate u q ^ N := by
      apply mul_le_mul_of_nonneg_right _ hrate0
      exact mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (mul_nonneg hC (tiltCost_nonneg P hu hq)) (by positivity))
    _ = _ := by ring

/-- A strict admissible tilt independently removes every changing
logarithm-bounded prefix of the stated size, for every fixed filter and height. -/
theorem tendsto_log_prefix (P : Polynomial ℂ) (y : ℝ)
    (T : ℕ → Finset ℕ) (f : ℕ → ℕ → ℂ) {u q : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hq : 1 / 2 < q) (hq1 : q ≤ 1)
    (hrate : tiltRate u q < 1)
    (hT : ∀ N n, n ∈ T N → 0 < n ∧ n ≤ (N + 1) ^ 2 *
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hf : ∀ N n, n ∈ T N → ‖f N n‖ ≤ Real.log n) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * ∑ n ∈ T N,
      f N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (nhds 0) := by
  have hr0 := (tiltRate_pos u (by linarith : 0 < q)).le
  have ht0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 hr0 hrate
  have ht1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hr0 hrate
  have ht2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hr0 hrate
  have ht3 := tendsto_pow_const_mul_const_pow_of_lt_one 3 hr0 hrate
  have ht : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ 3 * tiltRate u q ^ N) atTop (nhds 0) := by
    convert ((ht3.add (ht2.const_mul 3)).add (ht1.const_mul 3)).add ht0 using 1
    · ext N
      simp only [pow_zero, pow_one]
      ring
    · norm_num
  apply squeeze_zero_norm (fun N => norm_log_prefix_le P N y (T N) (f N)
    hu hu1 hq hq1 (hT N) (hf N))
  simpa only [mul_zero, mul_assoc] using
    ht.const_mul (2 * (1 + Real.log 3 + Real.log u⁻¹) * tiltCost P u q)

/-- The mixed labels pair a selected intermediate prime with any prime
at most the quadratic head. Integer labels, rather than incidences, index
the response. -/
def mixedLabels (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (A ×ˢ Nat.primesLE (N ^ 2)).image (fun ap => ap.1 * ap.2)

/-- The two disjoint prime ranges leave exactly one selected cofactor
incidence at every mixed label in the actual completed prefix. -/
theorem prefixCoefficient_mixed (A : Finset ℕ) (u : ℝ) (N : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ N ^ 2 < a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    {a p : ℕ} (ha : a ∈ A) (hp : p.Prime) (hpN : p ≤ N ^ 2) :
    prefixCoefficient A u N (a * p) =
      pairLift (SquarefreeVaughanLogSource.length u N) a (a * p) := by
  unfold prefixCoefficient
  rw [Finset.sum_eq_single a]
  · rw [Nat.mul_div_cancel_left _ (hA a ha).1.pos,
      if_pos (hpN.trans_lt ((hA a ha).2.1.trans (hA a ha).2.2))]
  · intro b hb hba
    have hnd : ¬ b ∣ a * p := by
      intro hd
      rcases (hA b hb).1.dvd_mul.mp hd with h | h
      · exact hba ((Nat.prime_dvd_prime_iff_eq (hA b hb).1 (hA a ha).1).mp h)
      · have he := (Nat.prime_dvd_prime_iff_eq (hA b hb).1 hp).mp h
        have hlarge := (hA b hb).2.1
        omega
    have hz : pairLift (SquarefreeVaughanLogSource.length u N) b (a * p) = 0 :=
      if_neg (fun h => hnd h.1)
    simp only [hz, ite_self]
  · exact fun h => (h ha).elim

/-- The actual mixed coefficient, with its INTERMEDIATE-prime logarithm,
is bounded by one product logarithm. No small-log replacement is made. -/
theorem norm_prefixCoefficient_mixed_le (A : Finset ℕ) (u : ℝ) (N : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ N ^ 2 < a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    {n : ℕ} (hn : n ∈ mixedLabels A N) :
    ‖prefixCoefficient A u N n‖ ≤ Real.log n := by
  obtain ⟨⟨a, p⟩, hap, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨ha, hp⟩ := Finset.mem_product.mp hap
  obtain ⟨hpN, hp⟩ := Nat.mem_primesLE.mp hp
  rw [prefixCoefficient_mixed A u N hA ha hp hpN]
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hlog : Real.log a ≤ SquarefreeVaughanLogSource.length u N := by
    apply Real.log_le_log (by exact_mod_cast (hA a ha).1.pos)
    exact_mod_cast (hA a ha).2.2.le
  rw [pairLift, if_pos ⟨dvd_mul_right a p, by
    simpa only [Nat.mul_div_cancel_left _ (hA a ha).1.pos] using hp⟩,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_neg,
    abs_of_nonneg (Real.log_natCast_nonneg (a * p)),
    abs_of_nonneg (Real.log_natCast_nonneg a), abs_of_pos hL]
  exact (div_le_iff₀ hL).mpr
    (mul_le_mul_of_nonneg_left hlog (Real.log_natCast_nonneg (a * p)))

/-- Every actual mixed label lies in the complete quadratic-times-physical
prefix, with no original-band condition needed for this independent bound. -/
theorem mixedLabels_physical_bound (A : Finset ℕ) (u : ℝ) (N : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ N ^ 2 < a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    {n : ℕ} (hn : n ∈ mixedLabels A N) :
    0 < n ∧ n ≤ (N + 1) ^ 2 *
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
  obtain ⟨⟨a, p⟩, hap, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨ha, hp⟩ := Finset.mem_product.mp hap
  obtain ⟨hpN, hp⟩ := Nat.mem_primesLE.mp hp
  refine ⟨Nat.mul_pos (hA a ha).1.pos hp.pos, ?_⟩
  calc
    a * p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 * (N + 1) ^ 2 := by
      apply Nat.mul_le_mul (hA a ha).2.2.le
      exact hpN.trans (Nat.pow_le_pow_left (Nat.le_succ N) 2)
    _ = _ := Nat.mul_comm _ _

/-- The complete actual mixed correction keeps its original sign,
common physical length and full factorial and product phases. -/
def mixedResponse (A : Finset ℕ) (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ mixedLabels A N, prefixCoefficient A u N n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- Every actual mixed response has a uniform explicit polynomial times
geometric bound, independent of the selected intermediate-prime family. -/
theorem norm_mixedResponse_le (A : Finset ℕ) (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u q : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hq : 1 / 2 < q) (hq1 : q ≤ 1)
    (hA : ∀ a ∈ A, a.Prime ∧ N ^ 2 < a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ‖(u : ℂ) ^ (N + 1) * mixedResponse A P u y N‖ ≤
      (2 * (1 + Real.log 3 + Real.log u⁻¹) * tiltCost P u q) *
        ((N : ℝ) + 1) ^ 3 * tiltRate u q ^ N :=
  norm_log_prefix_le P N y _ _ hu hu1 hq hq1
    (fun _ hn => mixedLabels_physical_bound A u N hA hn)
    (fun _ hn => norm_prefixCoefficient_mixed_le A u N hA hn)

/-- On the full strict quadratic-head interval the actual mixed prefix
vanishes independently. Its intermediate-prime logarithmic mark is fully
paid, for every changing selected family and every fixed filter and height. -/
theorem tendsto_mixedResponse (A : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hcontact : u < Real.exp (-(1 / 2 : ℝ)))
    (hA : ∀ N a, a ∈ A N → a.Prime ∧ N ^ 2 < a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * mixedResponse (A N) P u y N)
      atTop (nhds 0) := by
  obtain ⟨q, hq, hq1, hrate⟩ := ZetaRieszSmoothPrimePrefix.exists_quadratic_head_tilt hu hcontact
  exact tendsto_log_prefix P y _ _ (by linarith)
    (hcontact.trans (Real.exp_lt_one_iff.mpr (by norm_num))).le hq hq1 hrate
    (fun N _ hn => mixedLabels_physical_bound (A N) u N (hA N) hn)
    (fun N _ hn => norm_prefixCoefficient_mixed_le (A N) u N (hA N) hn)

end

end RiemannGaussian.ZetaRieszMixedPrefix

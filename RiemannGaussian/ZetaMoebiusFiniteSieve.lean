/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteDivisibilitySieve
import RiemannGaussian.ZetaMoebiusMultipleDecay

/-!
# Independent arithmetic control of simultaneous divisibility deletions

The actual arithmetic sum on a finite union of mixed-prime multiple
sectors is exactly its grouped inclusion-exclusion response. The new
uniform sector estimate pays only the actual grouped coefficient mass.
This controls simultaneous deletions, with the entire original signed
source retained in the genuine complementary series.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The original signed coefficient on the union of selected multiple
sectors. Each product is included once, irrespective of its overlaps. -/
def zetaMoebiusSieveCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  if ∃ P ∈ S, P ∣ n then zetaMoebiusLogTailCoefficient D n else 0

/-- The actual union coefficient equals the full signed overlap family. -/
theorem zetaMoebiusSieveCoefficient_eq_grouped (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    zetaMoebiusSieveCoefficient D S n =
      ∑ P ∈ divisibilitySieveSupport S,
        divisibilitySieveCoefficient S P * zetaMoebiusMultipleCoefficient D P n :=
  divisibilitySieve_eq_grouped S (zetaMoebiusLogTailCoefficient D) n

/-- The literal infinite arithmetic sum over the selected union. -/
def zetaMoebiusSieveFilter (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaMoebiusSieveCoefficient D S n * zetaPrimeFilterKernel p N s n

/-- The literal complementary products, with all signs and phases retained. -/
def zetaMoebiusSievedRemainderFilter (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, if ¬(∃ P ∈ S, P ∣ n) then
    zetaMoebiusLogTailCoefficient D n * zetaPrimeFilterKernel p N s n else 0

/-- Every union kernel is genuinely summable in the Euler half-plane. -/
theorem summable_zetaMoebiusSieveKernel (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ zetaMoebiusSieveCoefficient D S n * zetaPrimeFilterKernel p N s n) := by
  have h := (hasSum_zetaMoebiusLogTailFilter_kernel p D N hs).summable.indicator {n | ∃ P ∈ S, P ∣ n}
  apply h.congr
  intro n
  by_cases hn : ∃ P ∈ S, P ∣ n <;> simp [Set.indicator, zetaMoebiusSieveCoefficient, hn]

/-- The complete remaining kernel is also genuinely summable. -/
theorem summable_zetaMoebiusSievedRemainderKernel (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ if ¬(∃ P ∈ S, P ∣ n) then
      zetaMoebiusLogTailCoefficient D n * zetaPrimeFilterKernel p N s n else 0) := by
  have h := (hasSum_zetaMoebiusLogTailFilter_kernel p D N hs).summable.indicator
    {n | ¬(∃ P ∈ S, P ∣ n)}
  apply h.congr
  intro n
  by_cases hn : ∃ P ∈ S, P ∣ n <;> simp [Set.indicator, hn]

/-- The union series has exactly the grouped finite analytic response;
every intersection satisfies the proved mixed-prime hypotheses. -/
theorem hasSum_zetaMoebiusSieveFilter (p : Polynomial ℂ) (D N : ℕ) (S : Finset ℕ)
    (hS : ∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaMoebiusSieveCoefficient D S n * zetaPrimeFilterKernel p N s n)
      (∑ P ∈ divisibilitySieveSupport S,
        divisibilitySieveCoefficient S P * zetaMoebiusMultipleFilter p D P N s) := by
  have h := hasSum_sum (s := divisibilitySieveSupport S) (fun P hP ↦
    (hasSum_zetaMoebiusMultipleFilter p D N (divisibilitySieveSupport_eligible S hS hP).1
      (divisibilitySieveSupport_eligible S hS hP).2.1
      (divisibilitySieveSupport_eligible S hS hP).2.2 hs).mul_left (divisibilitySieveCoefficient S P))
  apply h.congr_fun
  intro n
  rw [zetaMoebiusSieveCoefficient_eq_grouped, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P _
  ring

/-- Simultaneous deletion is exactly the existing arithmetic factor
family, with the actual grouped overlap coefficients rather than fitted weights. -/
theorem zetaMoebiusSieveFilter_eq_grouped (p : Polynomial ℂ) (D N : ℕ) (S : Finset ℕ)
    (hS : ∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) {s : ℂ} (hs : 1 < s.re) :
    zetaMoebiusSieveFilter p D S N s =
      ∑ P ∈ divisibilitySieveSupport S, divisibilitySieveCoefficient S P *
        ∑' n, zetaMoebiusMultipleCoefficient D P n * zetaPrimeFilterKernel p N s n := by
  rw [zetaMoebiusSieveFilter, (hasSum_zetaMoebiusSieveFilter p D N S hS hs).tsum_eq]
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨hP0, hP1, hmix⟩ := divisibilitySieveSupport_eligible S hS hP
  rw [(hasSum_zetaMoebiusMultipleFilter p D N hP0 hP1 hmix hs).tsum_eq]

/-- The independent union bound charges the exact grouped overlap cost.
No cardinality, size, or disjointness hypothesis on the factor family is needed. -/
theorem exists_zetaMoebiusSieveFilter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N : ℕ) (S : Finset ℕ),
      (∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) →
      ‖zetaMoebiusSieveFilter p D S N (3 / 2 + I * y)‖ ≤
        C * D * (∑ k ∈ p.support, ‖p.coeff k‖) * divisibilitySieveCost S := by
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusMultipleFamily_bound y hy
  refine ⟨C, hC, ?_⟩
  intro p D N S hS
  rw [zetaMoebiusSieveFilter_eq_grouped p D N S hS (by norm_num)]
  exact hb p D N (divisibilitySieveSupport S) (divisibilitySieveCoefficient S)
    (fun _ hP ↦ divisibilitySieveSupport_eligible S hS hP)

/-- The actual normalized union has one geometric bound uniformly over
all eligible sieves whose exact grouped cost fits the original cutoff. -/
theorem exists_zetaRightHalfMoebiusSieve_uniform_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (S : Finset ℕ),
      (∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) →
      divisibilitySieveCost S ≤
        zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaMoebiusSieveFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) S N
          (3 / 2 + I * rho.1.im)‖ ≤ C * (Real.sqrt (3 / 2 - rho.1.re)) ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let p := zetaRightHalfPoleJetFilter rho hrho
  let B : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq : 1 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu hu1).le
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusSieveFilter_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho)
  refine ⟨C * u * B + 1, by positivity, ?_⟩
  intro N S hS hcost
  let D := zetaMoebiusGeometricCutoff q N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg (zero_le_one.trans hq) N)
  have hw : divisibilitySieveCost S ≤ q ^ N := hcost.trans hD
  have hbound := hb p D N S hS
  have hcost0 : 0 ≤ divisibilitySieveCost S := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * D * B * divisibilitySieveCost S) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ u ^ (N + 1) * (C * q ^ N * B * q ^ N) := by gcongr
    _ = (C * u * B) * (u * q ^ 2) ^ N := by
      rw [mul_pow, pow_succ, show (q ^ 2) ^ N = (q ^ N) ^ 2 by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      ring
    _ = (C * u * B) * (Real.sqrt u) ^ N := by rw [zetaMoebiusHeadGrowth_rate hu]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- Every moving finite sieve whose actual overlap cost is within the
original divisor cutoff deletes a negligible part of the source. -/
theorem tendsto_zetaRightHalfMoebiusSieve (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (S : ℕ → Finset ℕ)
    (hS : ∀ᶠ N in atTop, (∀ P ∈ S N, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) ∧
      divisibilitySieveCost (S N) ≤
        zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusSieveFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) (S N) N
        (3 / 2 + I * rho.1.im)) atTop (𝓝 0) := by
  have h := tendsto_zetaRightHalfMoebiusMultipleFamily_actualSum rho hrho
    (fun N ↦ divisibilitySieveSupport (S N)) (fun N ↦ divisibilitySieveCoefficient (S N))
    (hS.mono (fun N hN ↦ ⟨fun _ hP ↦ divisibilitySieveSupport_eligible (S N) hN.1 hP, hN.2⟩))
  apply h.congr'
  filter_upwards [hS] with N hN
  rw [zetaMoebiusSieveFilter_eq_grouped _ _ N (S N) hN.1 (by norm_num)]

/-- Exact reconstruction from the actual union and actual complement,
without any eligibility or cost assumption on the finite sieve. -/
theorem zetaMoebiusLogTailFilter_eq_sieve_add_remainder (p : Polynomial ℂ) (D N : ℕ) (S : Finset ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    zetaMoebiusLogTailFilter p D N s = zetaMoebiusSieveFilter p D S N s +
      zetaMoebiusSievedRemainderFilter p D S N s := by
  rw [← (hasSum_zetaMoebiusLogTailFilter_kernel p D N hs).tsum_eq,
    zetaMoebiusSieveFilter, zetaMoebiusSievedRemainderFilter,
    ← (summable_zetaMoebiusSieveKernel p D S N hs).tsum_add
      (summable_zetaMoebiusSievedRemainderKernel p D S N hs)]
  apply tsum_congr
  intro n
  by_cases hn : ∃ P ∈ S, P ∣ n <;> simp [zetaMoebiusSieveCoefficient, hn]

/-- The full negative multiplicity source survives simultaneous
deletion whenever its explicit grouped overlap cost meets the budget. -/
theorem tendsto_zetaRightHalfMoebiusSievedRemainder (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (S : ℕ → Finset ℕ)
    (hS : ∀ᶠ N in atTop, (∀ P ∈ S N, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) ∧
      divisibilitySieveCost (S N) ≤
        zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusSievedRemainderFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) (S N) N
        (3 / 2 + I * rho.1.im)) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_zetaRightHalfPoleJetTail rho hrho).sub (tendsto_zetaRightHalfMoebiusSieve rho hrho S hS)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaMoebiusLogTailFilter_eq_sieve_add_remainder _ _ N (S N) (by norm_num),
    mul_add, add_sub_cancel_left]

end
end RiemannGaussian

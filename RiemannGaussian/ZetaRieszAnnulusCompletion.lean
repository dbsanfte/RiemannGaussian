/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszInfinitePhysical
import RiemannGaussian.ZetaRieszCrossSupport

/-!
# A geometric bound for actual annular prime completion

The original cross-prime contribution is replaced by a genuinely complete
prime head minus its exact physical prefix. Every prior support cut and
integer multiplicity is discharged, and the remaining infinite product
tail has independently vanishing geometric error on 1/2<=u<exp(-2/3).
The finite prefix remains coupled to the rest of the signed carrier.
-/

namespace RiemannGaussian.ZetaRieszAnnulusCompletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszCrossCompletion ZetaRieszCrossSupport
open ZetaRieszInfinitePhysical ZetaRieszLowerDegreeBounds

/-- The genuinely completed upper-prime response minus its exact physical
prefix. This retains all prefix incidences, including its diagonal. -/
def completedCross (A : Finset ℕ) (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ZetaPrimeCofactorCompletion.completedCofactorHead A P N (3 / 2 + Complex.I * y)
    (SquarefreeVaughanLogSource.length u N) -
    ∑ n ∈ Finset.range (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2),
      prefixCoefficient A u N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The full completed cross response differs from its physical product
truncation by exactly an infinite mask of the original coefficient. -/
theorem completedCross_sub_range_eq_upper (A : Finset ℕ) (P : Polynomial ℂ) (u y : ℝ) (N : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    completedCross A P u y N -
      ∑ n ∈ Finset.range (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2),
        crossCoefficient A u N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n =
      zetaArithmeticFilter (upperCoefficient (fun _ n => (crossIncidences A u N n).Nonempty) u N)
        P N (3 / 2 + Complex.I * y) := by
  let M := ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2
  let f := fun n => crossCoefficient A u N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n
  have hsmall : HasSum (fun n => if n < M then f n else 0)
      (∑ n ∈ Finset.range M, f n) := by
    have h : HasSum (fun n => if n < M then f n else 0)
        (∑ n ∈ Finset.range M, if n < M then f n else 0) := by
      apply hasSum_sum_of_ne_finset_zero
      intro n hn
      exact if_neg (by simpa only [Finset.mem_range] using hn)
    convert h using 1
    exact (Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_range.mp hn))).symm
  have hfull : HasSum f (completedCross A P u y N) :=
    hasSum_crossCoefficient A u N P hA (by norm_num)
  have hupper : HasSum (fun n => upperCoefficient
      (fun _ n => (crossIncidences A u N n).Nonempty) u N n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
      (completedCross A P u y N - ∑ n ∈ Finset.range M, f n) := by
    apply (hfull.sub hsmall).congr_fun
    intro n
    by_cases hn : n < M
    · simp only [if_pos hn, sub_self, upperCoefficient]
      rw [if_neg (fun h => (not_le_of_gt hn) h.2), zero_mul]
    · simp only [if_neg hn, sub_zero, f, crossCoefficient, upperCoefficient]
      have hMn : M ≤ n := le_of_not_gt hn
      by_cases hc : (crossIncidences A u N n).Nonempty
      · rw [if_pos hc, if_pos ⟨hc, hMn⟩]
      · rw [if_neg hc, if_neg (fun h => hc h.1)]
  exact hupper.tsum_eq.symm

/-- The actual annular cross-prime response is eventually precisely the
physical product truncation of the complete series. Every previous support
cut is discharged for this class, rather than imposed on the prime sum. -/
theorem eventually_sum_cross_annulus_eq_range (A : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hA : ∀ N a, a ∈ A N → a.Prime ∧ N ^ 2 < a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ ZetaRieszPhysicalAnnulus.annulusBand u N,
        crossCoefficient (A N) u N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      ∑ n ∈ Finset.range (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2),
        crossCoefficient (A N) u N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  filter_upwards [eventually_cross_semiprime_mem_annulus hu huh] with N hN
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_range.mpr ((ZetaRieszPhysicalAnnulus.mem_annulusBand huh).mp hn).2.2
  · intro n hn hnot
    have hz : ¬ (crossIncidences (A N) u N n).Nonempty := by
      rintro ⟨a, ha⟩
      obtain ⟨haA, had, hp, hXp⟩ := Finset.mem_filter.mp ha
      have he : n / a * a = n := Nat.div_mul_cancel had
      have hm := hN a (n / a) (hA N a haA).1 hp (hA N a haA).2.1
        (hA N a haA).2.2 hXp (by rw [he]; exact Finset.mem_range.mp hn)
      exact hnot (he ▸ hm)
    simp only [crossCoefficient, if_neg hz, zero_mul]

/-- A fully independent geometric allowance now pays the entire prime
completion error of the actual annular cross class. The finite physical
prefix is retained exactly, and no signed floor is assumed or concluded. -/
theorem eventually_norm_annulus_completion_error_le (A : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hA : ∀ N a, a ∈ A N → a.Prime ∧ N ^ 2 < a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ∀ᶠ N : ℕ in atTop,
      ‖(u : ℂ) ^ (N + 1) * (completedCross (A N) P u y N -
        ∑ n ∈ ZetaRieszPhysicalAnnulus.annulusBand u N,
          crossCoefficient (A N) u N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)‖ ≤
      degreeRate 2 (2 / 3) (3 / 8) (257 / 256) ^ N *
        (u * ZetaArithmeticLogWindow.tiltConstant P (3 / 8) (257 / 256)) := by
  have hb := eventually_norm_infinite_upper_le
    (fun N n => (crossIncidences (A N) u N n).Nonempty) P y (by linarith : 0 < u) huh
  filter_upwards [hb, eventually_sum_cross_annulus_eq_range A P y hu huh hA] with N hN he
  rw [he, completedCross_sub_range_eq_upper (A N) P u y N (fun a ha => ⟨(hA N a ha).1, (hA N a ha).2.2⟩)]
  exact hN

/-- The actual annular cross class differs from the genuinely completed
prime head minus its exact prefix by o(1) at the original source scale. -/
theorem tendsto_annulus_completion_error (A : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hA : ∀ N a, a ∈ A N → a.Prime ∧ N ^ 2 < a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * (completedCross (A N) P u y N -
      ∑ n ∈ ZetaRieszPhysicalAnnulus.annulusBand u N,
        crossCoefficient (A N) u N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_annulus_completion_error_le A P y hu huh hA)
  have hr0 : 0 ≤ degreeRate 2 (2 / 3) (3 / 8) (257 / 256) := by unfold degreeRate; positivity
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 two_degree_rate_lt_one).mul_const
      (u * ZetaArithmeticLogWindow.tiltConstant P (3 / 8) (257 / 256))

end
end RiemannGaussian.ZetaRieszAnnulusCompletion

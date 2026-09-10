/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaFiniteDirichlet
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-!
# Exact finite divisibility sieves with signed overlap coefficients

The union of any finite family of divisibility conditions is an exact
signed sum over least common multiples. Equal intersection indices are
grouped before estimating their coefficient mass. The full complex
test function remains inside the identities.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- All nonempty intersection patterns in the chosen finite sieve. -/
def divisibilitySieveIntersections (S : Finset ℕ) : Finset (Finset ℕ) :=
  S.powerset.filter Finset.Nonempty

/-- Distinct least common multiples of the actual intersection patterns. -/
def divisibilitySieveSupport (S : Finset ℕ) : Finset ℕ :=
  (divisibilitySieveIntersections S).image (fun T ↦ T.lcm id)

/-- The exact signed coefficient after all coincident intersection
indices have been combined. These coefficients are prescribed by the sieve. -/
def divisibilitySieveCoefficient (S : Finset ℕ) (P : ℕ) : ℂ :=
  ∑ T ∈ divisibilitySieveIntersections S,
    if T.lcm id = P then (-1 : ℂ) ^ (T.card + 1) else 0

/-- Inclusion-exclusion retains the complete complex value at each
product index; every intersection is represented by its least common multiple. -/
theorem divisibilitySieve_eq_intersections (S : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) :
    (if ∃ P ∈ S, P ∣ n then f n else 0) =
      ∑ T ∈ divisibilitySieveIntersections S, (-1 : ℂ) ^ (T.card + 1) *
        (if T.lcm id ∣ n then f n else 0) := by
  have h := Finset.indicator_biUnion_eq_sum_powerset S (fun P : ℕ ↦ {m : ℕ | P ∣ m}) f n
  simpa [divisibilitySieveIntersections, Set.indicator, Finset.lcm_dvd_iff, zsmul_eq_mul] using h

/-- Equal intersection indices are grouped exactly, retaining all
signed cancellations before any coefficient norm is taken. -/
theorem sum_divisibilitySieveCoefficient (S : Finset ℕ) (F : ℕ → ℂ) :
    (∑ P ∈ divisibilitySieveSupport S, divisibilitySieveCoefficient S P * F P) =
      ∑ T ∈ divisibilitySieveIntersections S, (-1 : ℂ) ^ (T.card + 1) * F (T.lcm id) := by
  simp only [divisibilitySieveCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  have hm : T.lcm id ∈ divisibilitySieveSupport S := Finset.mem_image_of_mem _ hT
  simp [ite_mul, Finset.sum_ite_eq, hm]

/-- The union mask is a finite complex combination of divisibility
sectors with the actual grouped overlap coefficients. -/
theorem divisibilitySieve_eq_grouped (S : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) :
    (if ∃ P ∈ S, P ∣ n then f n else 0) =
      ∑ P ∈ divisibilitySieveSupport S, divisibilitySieveCoefficient S P *
        (if P ∣ n then f n else 0) := by
  rw [sum_divisibilitySieveCoefficient, divisibilitySieve_eq_intersections]

/-- The exact total absolute weight of the grouped coefficients. -/
def divisibilitySieveCost (S : Finset ℕ) : ℝ :=
  ∑ P ∈ divisibilitySieveSupport S, ‖divisibilitySieveCoefficient S P‖

/-- Grouping cannot cost more than the actual number of nonempty
intersection patterns, including all cancellations within each group. -/
theorem divisibilitySieveCost_le_card (S : Finset ℕ) :
    divisibilitySieveCost S ≤ (divisibilitySieveIntersections S).card := by
  unfold divisibilitySieveCost
  calc
    _ ≤ ∑ P ∈ divisibilitySieveSupport S, ∑ T ∈ divisibilitySieveIntersections S,
        if T.lcm id = P then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro P _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro T _
      by_cases hT : T.lcm id = P <;> simp [hT]
    _ = (divisibilitySieveIntersections S).card := by
      rw [Finset.sum_comm]
      have he (T : Finset ℕ) (hT : T ∈ divisibilitySieveIntersections S) :
          (∑ P ∈ divisibilitySieveSupport S, if T.lcm id = P then (1 : ℝ) else 0) = 1 := by
        have hm : T.lcm id ∈ divisibilitySieveSupport S := Finset.mem_image_of_mem _ hT
        simp [Finset.sum_ite_eq, hm]
      simp only [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A fully explicit powerset envelope for the overlap cost. The exact
grouped cost remains available for stronger estimates. -/
theorem divisibilitySieveCost_le_pow (S : Finset ℕ) :
    divisibilitySieveCost S ≤ (2 : ℝ) ^ S.card := by
  apply (divisibilitySieveCost_le_card S).trans
  exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ S.powerset)).trans_eq
    (Finset.card_powerset S)

/-- Every intersection of positive mixed-prime factors is again a
positive mixed-prime factor, so its analytic sector bound is available. -/
theorem divisibilitySieveSupport_eligible (S : Finset ℕ)
    (hS : ∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) {Q : ℕ}
    (hQ : Q ∈ divisibilitySieveSupport S) : 0 < Q ∧ Q ≠ 1 ∧ ¬IsPrimePow Q := by
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨hsub, hne⟩ := Finset.mem_filter.mp hT
  have hTS : T ⊆ S := Finset.mem_powerset.mp hsub
  have h0 : T.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun P hP ↦ (hS P (hTS hP)).1.ne')
  obtain ⟨P, hP⟩ := hne
  have hPd : P ∣ T.lcm id := Finset.dvd_lcm (f := id) hP
  have hP1 := (hS P (hTS hP)).2.1
  refine ⟨Nat.pos_of_ne_zero h0, ?_, ?_⟩
  · intro h1
    exact hP1 (Nat.eq_one_of_dvd_one (h1 ▸ hPd))
  · intro hprime
    exact (hS P (hTS hP)).2.2 (hprime.dvd hPd hP1)

end
end RiemannGaussian

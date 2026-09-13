/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovSignedCongruence

/-!
# From complete moment equations to conditioned congruence counts

The full binomial translation retains all lower moments and integer weights.
When both tail tuples lie in one residue class modulo p^b, the surviving
signed block satisfies its actual degree-j congruence modulo p^(jb).
The nonsingular block projection therefore receives the previously proved
signed translated count. This does not count the tail completions or
control the singular block part of the whole moment system.
-/

namespace RiemannGaussian.VinogradovConditionedMoment
noncomputable section
open scoped BigOperators Classical
open VinogradovSignedCongruence

/-- Translation of a weighted power sum retains every lower-degree moment
and every original coefficient in its exact binomial expansion. -/
theorem translated_weighted_power_sum {r : ℕ} (c v : Fin r → ℤ) (eta : ℤ) (n : ℕ) :
    (∑ i, c i * (v i - eta) ^ n) = ∑ d ∈ Finset.range (n + 1),
      ((n.choose d : ℕ) : ℤ) * (-eta) ^ (n - d) * (∑ i, c i * v i ^ d) := by
  simp_rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The entire mixed weighted moment equation survives a common integer
translation. Its degree-zero identity is paid by matching coefficients
and tail lengths. -/
theorem translated_moment_equation {k r n : ℕ}
    (c x y : Fin k → ℤ) (v w : Fin r → ℤ) (eta : ℤ)
    (h : ∀ d, 1 ≤ d → d ≤ n →
      (∑ i, c i * x i ^ d) + (∑ i, v i ^ d) =
        (∑ i, c i * y i ^ d) + ∑ i, w i ^ d) :
    (∑ i, c i * (x i - eta) ^ n) + (∑ i, (v i - eta) ^ n) =
      (∑ i, c i * (y i - eta) ^ n) + ∑ i, (w i - eta) ^ n := by
  have hunweighted {s : ℕ} (u : Fin s → ℤ) :
      (∑ i, (u i - eta) ^ n) = ∑ d ∈ Finset.range (n + 1),
      ((n.choose d : ℕ) : ℤ) * (-eta) ^ (n - d) * (∑ i, u i ^ d) := by
    simpa only [one_mul] using translated_weighted_power_sum (fun _ => 1) u eta n
  simp only [translated_weighted_power_sum, hunweighted, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have he : (∑ i, c i * x i ^ d) + (∑ i, v i ^ d) =
      (∑ i, c i * y i ^ d) + ∑ i, w i ^ d := by
    by_cases hd0 : d = 0
    · subst d
      simp
    · exact h d (by omega) (by simpa using Finset.mem_range.mp hd)
  rw [← mul_add, ← mul_add, he]

/-- When both tail tuples lie in one coarse residue class, the original
complete weighted moment system forces all degree-specific divisibilities
of the surviving translated block. -/
theorem conditioned_power_difference {p b k r n : ℕ}
    (c x y : Fin k → ℤ) (v w : Fin r → ℤ) (eta : ℤ)
    (hv : ∀ i, (p : ℤ) ^ b ∣ v i - eta)
    (hw : ∀ i, (p : ℤ) ^ b ∣ w i - eta)
    (h : ∀ d, 1 ≤ d → d ≤ n →
      (∑ i, c i * x i ^ d) + (∑ i, v i ^ d) =
        (∑ i, c i * y i ^ d) + ∑ i, w i ^ d) :
    (p : ℤ) ^ (n * b) ∣ (∑ i, c i * (x i - eta) ^ n) -
      ∑ i, c i * (y i - eta) ^ n := by
  have he := translated_moment_equation c x y v w eta h
  have hx : (∑ i, c i * (x i - eta) ^ n) - (∑ i, c i * (y i - eta) ^ n) =
      (∑ i, (w i - eta) ^ n) - ∑ i, (v i - eta) ^ n := by linarith
  rw [hx]
  apply dvd_sub
  · apply Finset.dvd_sum
    intro i hi
    simpa only [← pow_mul, mul_comm b n] using pow_dvd_pow_of_dvd (hw i) n
  · apply Finset.dvd_sum
    intro i hi
    simpa only [← pow_mul, mul_comm b n] using pow_dvd_pow_of_dvd (hv i) n

/-- Count the actual surviving residue blocks of complete signed moment
solutions with both tails conditioned to eta modulo p^b. The tails may be
arbitrary integer tuples: their existence implies the counted congruences. -/
theorem conditioned_block_card_le {p k b r : ℕ} [Fact p.Prime] (hkp : k < p)
    (colour : Fin k → Bool) (eta : ℤ) (y : Fin k → ℤ) :
    (Finset.univ.filter (fun x : Fin k → Fin (p ^ (k * b)) =>
      Function.Injective (fun j => ((x j).val : ZMod p)) ∧
      ∃ v w : Fin r → ℤ,
        (∀ j, (p : ℤ) ^ b ∣ v j - eta) ∧ (∀ j, (p : ℤ) ^ b ∣ w j - eta) ∧
        ∀ d, 1 ≤ d → d ≤ k →
          (∑ i, sign (colour i) * ((x i).val : ℤ) ^ d) + (∑ i, v i ^ d) =
            (∑ i, sign (colour i) * y i ^ d) + ∑ i, w i ^ d)).card ≤
      p ^ (b * (k * (k - 1) / 2)) * colourFactorial colour := by
  classical
  apply le_trans (Finset.card_le_card ?_)
    (degree_moduli_card_le hkp colour eta
      (fun i => ∑ j, sign (colour j) * (y j - eta) ^ (i.val + 1)))
  intro x hx
  obtain ⟨hxprime, v, w, hv, hw, hmoment⟩ := (Finset.mem_filter.mp hx).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxprime, ?_⟩
  intro i
  apply conditioned_power_difference (fun j => sign (colour j))
    (fun j => ((x j).val : ℤ)) y v w eta hv hw
  intro d hd hdi
  exact hmoment d hd (by omega)

end
end RiemannGaussian.VinogradovConditionedMoment

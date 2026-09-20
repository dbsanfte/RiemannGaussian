/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszDominantAllocation

/-!
# Independent decay of the entire dominant-prime sector

The actual unassigned coefficient has a complete-arithmetic geometric bound
whenever an eligible selected prime carries at least thirteen twentieths of
the product logarithm. The high-prime endpoint is paid by the physical cutoff,
without a second lower bound on the cofactor logarithm.
-/

namespace RiemannGaussian.ZetaRieszDominantAllocation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszMaskSupport ZetaRieszCompanionMask

/-- Both missing allocation tails are paid jointly with the actual factorial kernel and prime cutoff. -/
theorem normalized_missing_kernel_bound (N n : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u L x : ℝ} (hu : 0 ≤ u) (huhi : u ≤ 503 / 1000)
    (hx : 0 ≤ x) (hxhi : x ≤ 7 / 20)
    (hcut : (1 - x) * Real.log n ≤ L) (hL : L ≤ (139 / 100 : ℝ) * N) :
    u ^ (N + 1) *
      (1 - ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N + 1) k x) *
        ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      (upperRate ^ N + lowerRate ^ N) * zetaPrimeExpWeight referenceExponent n := by
  let w : ℝ := (5 / 6 : ℝ) * x + (1 - x)
  have hw0 : 0 ≤ w := by dsimp [w]; linarith
  have hw1 : w ≤ 1 := by dsimp [w]; linarith
  have hwN : w ^ (N + 1) ≤ w ^ N := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hw0 _) hw1
  have hk : ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      (12000 / 5999 : ℝ) ^ N * zetaPrimeExpWeight referenceExponent n := by
    convert norm_zetaPrimeLogKernel_le N (3 / 2 + Complex.I * y) n
      (by norm_num : (0 : ℝ) < 5999 / 12000) using 1
    norm_num [referenceExponent]
  have hwk : w ^ N * ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      (10000 / 5999 : ℝ) ^ N * Real.exp ((5999 / 10000 : ℝ) * L / 6) *
        zetaPrimeExpWeight referenceExponent n := by
    have h := weighted_kernel_bound N n y hw0 (by norm_num : (0 : ℝ) < 5999 / 10000)
      (σ := referenceExponent) (B := (5999 / 10000 : ℝ) * L / 6) (by
        dsimp only [w, referenceExponent]
        nlinarith)
    simp only [inv_div] at h
    exact h
  have hupper : u ^ (N + 1) * ((87 / 80 : ℝ) * Real.exp (-(N : ℝ) / 160)) *
      ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      upperRate ^ N * zetaPrimeExpWeight referenceExponent n := by
    calc
      _ ≤ u ^ (N + 1) * ((87 / 80 : ℝ) * Real.exp (-(N : ℝ) / 160)) *
          ((12000 / 5999 : ℝ) ^ N * zetaPrimeExpWeight referenceExponent n) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ _ := by
        simpa only [mul_assoc, zetaPrimeExpWeight] using mul_le_mul_of_nonneg_right
          (upper_scalar N hu huhi) (Real.exp_pos _).le
  have hlower : u ^ (N + 1) *
      (Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ)) * w ^ (N + 1)) *
        ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      lowerRate ^ N * zetaPrimeExpWeight referenceExponent n := by
    calc
      _ ≤ (u ^ (N + 1) * Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ))) *
          (w ^ N * ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hwN (norm_nonneg _)) (by positivity :
            0 ≤ u ^ (N + 1) * Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ)))
      _ ≤ (u ^ (N + 1) * Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ))) *
          ((10000 / 5999 : ℝ) ^ N * Real.exp ((5999 / 10000 : ℝ) * L / 6) *
            zetaPrimeExpWeight referenceExponent n) := mul_le_mul_of_nonneg_left hwk (by positivity)
      _ ≤ _ := by
        simpa only [mul_assoc, zetaPrimeExpWeight] using mul_le_mul_of_nonneg_right
          (cutoff_scalar N hu huhi hL) (Real.exp_pos _).le
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (missing_allocation_cutoff_bound N hN hx hxhi)
      (pow_nonneg hu (N + 1))) (norm_nonneg (zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n))
  dsimp only [w] at hlower
  nlinarith [hupper, hlower]

/-- One original unassigned arithmetic atom has a summable two-rate bound on the enlarged dominant-prime sector. -/
theorem normalized_residual_dominant_atom (A : Finset ℕ) (N : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u L : ℝ} (hu : 0 ≤ u) (huhi : u ≤ 503 / 1000) (hL0 : 0 < L)
    (hL : L ≤ (139 / 100 : ℝ) * N) {n p : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n) (hnp : ¬n.Prime)
    (hp : p ∈ n.primeFactors) (hpA : p ∈ A) (hel : eligibleCofactor p (n / p))
    (hpL : Real.log p ≤ L) (hdom : (13 / 20 : ℝ) * Real.log n ≤ Real.log p) :
    ‖(u : ℂ) ^ (N + 1) *
      (residualCoefficient A L N n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n)‖ ≤
      (upperRate ^ N + lowerRate ^ N) *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight referenceExponent n) := by
  let x := Real.log (n / p : ℕ) / Real.log n
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hlog : Real.log (n / p : ℕ) = Real.log n - Real.log p := by
    rw [Nat.cast_div hpd (by exact_mod_cast hpp.ne_zero),
      Real.log_div (by exact_mod_cast hn.ne_zero) (by exact_mod_cast hpp.ne_zero)]
  have hx : 0 ≤ x := div_nonneg (Real.log_natCast_nonneg _) hln.le
  have hxhi : x ≤ 7 / 20 := by
    apply (div_le_iff₀ hln).mpr
    rw [hlog]
    linarith
  have hcut : (1 - x) * Real.log n ≤ L := by
    have he : (1 - x) * Real.log n = Real.log p := by
      dsimp only [x]
      rw [hlog]
      field_simp
      ring
    rw [he]
    exact hpL
  let β := 1 - allocationShare A N n
  have hβ : 0 ≤ β := by dsimp [β]; linarith [(allocationShare_bounds A N hn hn1).2]
  have hβle : β ≤ 1 - ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N + 1) k x := by
    have h := single_prime_mass_le_share A N hn hn1 hp hpA hel
    dsimp only [β, x]
    linarith
  have hc : ‖residualCoefficient A L N n‖ ≤ β * zetaMoebiusLogMajorant n := by
    rw [residualCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      boundedShare, if_pos ⟨hn, hn1, hnp⟩, abs_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left (SquarefreeVaughanLogSource.norm_coefficient_le hL0 n) hβ
  have hb : u ^ (N + 1) * β * ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      (upperRate ^ N + lowerRate ^ N) * zetaPrimeExpWeight referenceExponent n := by
    apply le_trans _ (normalized_missing_kernel_bound N n hN y hu huhi hx hxhi hcut hL)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβle (pow_nonneg hu _))
      (norm_nonneg _)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  calc
    _ ≤ u ^ (N + 1) * ((β * zetaMoebiusLogMajorant n) *
        ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) (pow_nonneg hu _)
    _ = zetaMoebiusLogMajorant n * (u ^ (N + 1) * β *
        ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hb (zetaMoebiusLogMajorant_nonneg n)).trans_eq (by ring)

/-- The enlarged sector on the actual retained support, with all eligibility conditions explicit. -/
def dominantSector (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (retainedBand u N K).filter (fun n => Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
    ∃ p ∈ n.primeFactors, p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N ∧
      eligibleCofactor p (n / p) ∧ (13 / 20 : ℝ) * Real.log n ≤ Real.log p)

/-- The entire enlarged sector of the literal retained carrier has an independent geometric bound, uniform in height and count cutoff. -/
theorem dominantSector_bound (N K : ℕ) (hN : 320 ≤ N) (y : ℝ) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u ≤ Real.exp (-(11 / 16 : ℝ))) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ dominantSector u N K,
      residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N n *
          zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      (upperRate ^ N + lowerRate ^ N) * zetaMoebiusLogMajorantMass referenceExponent := by
  have hu0 : 0 ≤ u := by linarith
  have huhi := huh.trans radius_ceiling
  have hL : SquarefreeVaughanLogSource.length u N ≤ (139 / 100 : ℝ) * N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu (by omega : 2 ≤ N)
    have hlog : 2 * Real.log 2 ≤ (139 / 100 : ℝ) := by linarith [Real.log_two_lt_d9]
    exact h.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ dominantSector u N K, (upperRate ^ N + lowerRate ^ N) *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight referenceExponent n) := by
      apply Finset.sum_le_sum
      intro n hnS
      obtain ⟨_, hn, hn1, hnp, p, hp, hpA, hel, hdom⟩ := Finset.mem_filter.mp hnS
      have hp' := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hpA
      have hpL : Real.log p ≤ SquarefreeVaughanLogSource.length u N :=
        (Real.log_lt_log (by exact_mod_cast hp'.1.pos) (by exact_mod_cast hp'.2.2)).le
      exact normalized_residual_dominant_atom _ N hN y hu0 huhi
        (SquarefreeVaughanLogSource.length_pos u N) hL hn hn1 hnp hp hpA hel hpL hdom
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num [referenceExponent])))
        (add_nonneg (pow_nonneg rates_bounds.1.1 N) (pow_nonneg rates_bounds.2.1 N))

end
end RiemannGaussian.ZetaRieszDominantAllocation

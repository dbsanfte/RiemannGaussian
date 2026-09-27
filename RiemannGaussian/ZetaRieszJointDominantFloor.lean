/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointAllocationFloor

/-!
# A smaller dominant-prime deletion for the joint floor

On the restricted radius interval, the original residual allocation pays
every eligible prime carrying at least `121/200` of the total logarithm,
with a refined bound down to `601/1000`. The lower missing tail retains the physical prime cutoff. All remaining
labels stay inside one signed observation; no packet is completed.
-/

namespace RiemannGaussian.ZetaRieszJointDominantFloor
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszDominantAllocation
open ZetaRieszWideOwnerAudit ZetaRieszParityPacket ZetaRieszAnnulusJoint
open ZetaRieszPrimeCountFrequency ZetaRieszMaskSupport

private theorem upper_log_rate :
    Real.log (4079/4000 : ℝ)-(13/32 : ℝ)*Real.log (21/20 : ℝ) ≤ -(1/4000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1/41)
    (by norm_num : (1/41 : ℝ) < 1) 1
  norm_num [Finset.sum_range_succ] at hlo
  have hhi : Real.log (4079/4000 : ℝ) ≤ 489/25000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 489/25000) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  linarith

/-- The smaller radius pays the high missing tail with an explicit
`exp(-N/8000)` rate after the original source normalization. -/
theorem upper_scalar (N : ℕ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) :
    u^(N+1)*((4079/4000 : ℝ)*Real.exp (-(N : ℝ)/4000))*
      (262144/131071 : ℝ)^N ≤ Real.exp (-(1/8000 : ℝ))^N := by
  have hr : radiusCeiling*(262144/131071 : ℝ)*Real.exp (-(1/4000 : ℝ)) ≤
      Real.exp (-(1/8000 : ℝ)) := by
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
    norm_num
    have h := Real.add_one_le_exp (1/8000 : ℝ)
    norm_num [radiusCeiling]
    linarith
  have he : Real.exp (-(N : ℝ)/4000) = Real.exp (-(1/4000 : ℝ))^N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ radiusCeiling^(N+1)*((4079/4000 : ℝ)*Real.exp (-(N : ℝ)/4000))*
        (262144/131071 : ℝ)^N := by gcongr
    _ = (radiusCeiling*(4079/4000 : ℝ))*
        (radiusCeiling*(262144/131071 : ℝ)*Real.exp (-(1/4000 : ℝ)))^N := by
      rw [he,mul_pow,mul_pow,pow_succ]
      ring
    _ ≤ Real.exp (-(1/8000 : ℝ))^N := by
      have hp := pow_le_pow_left₀ (by unfold radiusCeiling; positivity) hr N
      have hc : 0 ≤ radiusCeiling*(4079/4000 : ℝ) ∧
          radiusCeiling*(4079/4000 : ℝ) ≤ 1 := by norm_num [radiusCeiling]
      exact (mul_le_mul_of_nonneg_left hp hc.1).trans
        (mul_le_of_le_one_left (by positivity) hc.2)

/-- Both original missing tails, with the upper one retuned to cofactor share `79/200`. The lower tail still retains its exact logarithm dependence. -/
theorem missing_allocation_cutoff_bound (N : ℕ) (hN : 320 ≤ N) {x : ℝ}
    (hx : 0 ≤ x) (hxhi : x ≤ 79 / 200) :
    1 - (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N + 1) k x) ≤
      (4079 / 4000 : ℝ) * Real.exp (-(N : ℝ) / 4000) +
      Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ)) *
        ((5 / 6 : ℝ) * x + (1 - x)) ^ (N + 1) := by
  have hx1 : x ≤ 1 := by linarith
  have ht : 0 ≤ Real.log (21 / 20 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have h := missed_mass_bound N hN hx hx1
    (Real.exp_pos (-(13 / 32 : ℝ) * N * Real.log (21 / 20 : ℝ))).le
    (Real.exp_pos (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ))).le
    (by norm_num : (0 : ℝ) ≤ 21 / 20) (by norm_num : (0 : ℝ) ≤ 5 / 6) ?_ ?_
  · apply h.trans
    apply add_le_add _ le_rfl
    have hb : ((21 / 20 : ℝ) * x + (1 - x)) ^ (N + 1) ≤ (4079 / 4000 : ℝ) ^ (N + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have he : Real.exp (-(13 / 32 : ℝ) * N * Real.log (21 / 20 : ℝ)) *
        (4079 / 4000 : ℝ) ^ (N + 1) = (4079 / 4000 : ℝ) *
          Real.exp ((N : ℝ) * (Real.log (4079 / 4000 : ℝ) -
            (13 / 32 : ℝ) * Real.log (21 / 20 : ℝ))) := by
      rw [pow_succ]
      have hp : (4079 / 4000 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log (4079 / 4000 : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [hp, show (N : ℝ) * (Real.log (4079 / 4000 : ℝ) -
        (13 / 32 : ℝ) * Real.log (21 / 20 : ℝ)) =
          -(13 / 32 : ℝ) * N * Real.log (21 / 20 : ℝ) +
            (N : ℝ) * Real.log (4079 / 4000 : ℝ) by ring, Real.exp_add]
      ring
    calc
      _ ≤ Real.exp (-(13 / 32 : ℝ) * N * Real.log (21 / 20 : ℝ)) * (4079 / 4000 : ℝ) ^ (N + 1) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = _ := he
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left upper_log_rate (Nat.cast_nonneg (α := ℝ) N)]))
          (by norm_num)
  · intro k hk hcut
    have hc : (13 / 32 : ℝ) * N ≤ k := by
      have hn : 13 * N < 32 * k := by omega
      have hnR : (13 : ℝ) * N < 32 * k := by exact_mod_cast hn
      linarith
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 21 / 20),
      ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    simp only [Real.log_exp]
    nlinarith [mul_le_mul_of_nonneg_right hc ht]
  · intro k hk hcut
    have hkN : k ≤ N + 1 := by have := Finset.mem_range.mp hk; omega
    have hc : (k : ℝ) ≤ (N : ℝ) / 5 + 1 := by
      have hn : 5 * k ≤ N + 5 := by omega
      have hnR : (5 : ℝ) * k ≤ N + 5 := by exact_mod_cast hn
      linarith
    have he : (5 / 6 : ℝ) = Real.exp (-Real.log (6 / 5 : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc hl]

/-- The physical lower missing tail is paid as before, while any checked
upper-kernel bound can keep additional radial information. No source or
arithmetic cancellation premise is used by this finite comparison. -/
theorem normalized_missing_of_kernel_bound (N n : ℕ) (y : ℝ)
    {u L x B δ r : ℝ} (hu : 0 ≤ u) (huhi : u ≤ radiusCeiling)
    (hx : 0 ≤ x) (hxhi : x ≤ 1)
    (hcut : (1-x)*Real.log n ≤ L) (hL : L ≤ (139/100 : ℝ)*N)
    (hmissing : 1-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x ≤
      B*Real.exp (-(N : ℝ)*δ)+
        Real.exp (((N : ℝ)/5+1)*Real.log (6/5 : ℝ))*
          ((5/6 : ℝ)*x+(1-x))^(N+1))
    (hupper : u^(N+1)*(B*Real.exp (-(N : ℝ)*δ))*
      ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        r^N*zetaPrimeExpWeight (1+1/262144) n) :
    u^(N+1)*(1-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x)*
      ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (r^N+lowerRate^N)*zetaPrimeExpWeight (1+1/262144) n := by
  let w : ℝ := (5 / 6 : ℝ) * x + (1 - x)
  have hw0 : 0 ≤ w := by dsimp [w]; linarith
  have hw1 : w ≤ 1 := by dsimp [w]; linarith
  have hwN : w ^ (N + 1) ≤ w ^ N := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hw0 _) hw1
  have hwk : w ^ N * ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      (10000 / 5999 : ℝ) ^ N * Real.exp ((5999 / 10000 : ℝ) * L / 6) *
        zetaPrimeExpWeight (1+1/262144) n := by
    have h := weighted_kernel_bound N n y hw0 (by norm_num : (0 : ℝ) < 5999 / 10000)
      (σ := (1+1/262144)) (B := (5999 / 10000 : ℝ) * L / 6) (by
        dsimp only [w]
        nlinarith [Real.log_natCast_nonneg n])
    simp only [inv_div] at h
    exact h
  have hlower : u ^ (N + 1) *
      (Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ)) * w ^ (N + 1)) *
        ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      lowerRate ^ N * zetaPrimeExpWeight (1+1/262144) n := by
    calc
      _ ≤ (u ^ (N + 1) * Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ))) *
          (w ^ N * ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hwN (norm_nonneg _)) (by positivity :
            0 ≤ u ^ (N + 1) * Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ)))
      _ ≤ (u ^ (N + 1) * Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ))) *
          ((10000 / 5999 : ℝ) ^ N * Real.exp ((5999 / 10000 : ℝ) * L / 6) *
            zetaPrimeExpWeight (1+1/262144) n) := mul_le_mul_of_nonneg_left hwk (by positivity)
      _ ≤ _ := by
        simpa only [mul_assoc, zetaPrimeExpWeight] using mul_le_mul_of_nonneg_right
          (cutoff_scalar N hu (huhi.trans (by norm_num [radiusCeiling])) hL) (Real.exp_pos _).le
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmissing
      (pow_nonneg hu (N + 1))) (norm_nonneg (zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n))
  dsimp only [w] at hlower
  nlinarith [hupper, hlower]

private theorem kernel_of_missing (N n : ℕ) (y : ℝ)
    {u L x B δ r : ℝ} (hu : 0 ≤ u) (huhi : u ≤ radiusCeiling)
    (hx : 0 ≤ x) (hxhi : x ≤ 1) (hB : 0 ≤ B)
    (hcut : (1-x)*Real.log n ≤ L) (hL : L ≤ (139/100 : ℝ)*N)
    (hmissing : 1-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x ≤
      B*Real.exp (-(N : ℝ)*δ)+
        Real.exp (((N : ℝ)/5+1)*Real.log (6/5 : ℝ))*
          ((5/6 : ℝ)*x+(1-x))^(N+1))
    (hupper : u^(N+1)*(B*Real.exp (-(N : ℝ)*δ))*(262144/131071 : ℝ)^N ≤ r^N) :
    u^(N+1)*(1-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x)*
      ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (r^N+lowerRate^N)*zetaPrimeExpWeight (1+1/262144) n := by
  have hk : ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      (262144 / 131071 : ℝ) ^ N * zetaPrimeExpWeight (1+1/262144) n := by
    convert norm_zetaPrimeLogKernel_le N (3 / 2 + Complex.I * y) n
      (by norm_num : (0 : ℝ) < 131071 / 262144) using 1
    norm_num
  have hupper : u ^ (N + 1) * (B * Real.exp (-(N : ℝ) *δ)) *
      ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      r^N * zetaPrimeExpWeight (1+1/262144) n := by
    calc
      _ ≤ u ^ (N + 1) * (B * Real.exp (-(N : ℝ) *δ)) *
          ((262144 / 131071 : ℝ) ^ N * zetaPrimeExpWeight (1+1/262144) n) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ _ := by
        simpa only [mul_assoc, zetaPrimeExpWeight] using mul_le_mul_of_nonneg_right
          hupper (Real.exp_pos _).le
  exact normalized_missing_of_kernel_bound N n y hu huhi hx hxhi hcut hL
    hmissing hupper

/-- Both missing allocation tails are paid jointly with the actual factorial kernel and prime cutoff. -/
theorem normalized_missing_kernel_bound (N n : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u L x : ℝ} (hu : 0 ≤ u) (huhi : u ≤ radiusCeiling)
    (hx : 0 ≤ x) (hxhi : x ≤ 79 / 200)
    (hcut : (1 - x) * Real.log n ≤ L) (hL : L ≤ (139 / 100 : ℝ) * N) :
    u ^ (N + 1) *
      (1 - ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N + 1) k x) *
        ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      (Real.exp (-(1/8000 : ℝ))^N + lowerRate ^ N) * zetaPrimeExpWeight (1+1/262144) n := by
  exact kernel_of_missing N n y hu huhi hx (by linarith) (by norm_num)
    hcut hL (missing_allocation_cutoff_bound N hN hx hxhi) (upper_scalar N hu huhi)

/-- Transfer a proved missing-mass kernel bound to the original residual
coefficient without changing its allocation or phase. -/
theorem normalized_residual_of_missing_kernel (A : Finset ℕ) (N : ℕ) (y : ℝ)
    {u L c r : ℝ} (hu : 0 ≤ u) (hL0 : 0 < L)
    {n p : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n) (hnp : ¬n.Prime)
    (hp : p ∈ n.primeFactors) (hpA : p ∈ A) (hel : eligibleCofactor p (n / p))
    (hpL : Real.log p ≤ L) (hdom : c * Real.log n ≤ Real.log p)
    (hk : ∀ x : ℝ, 0 ≤ x → x ≤ 1-c → (1-x)*Real.log n ≤ L →
      u^(N+1)*(1-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x)*
        ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (r^N+lowerRate^N)*zetaPrimeExpWeight (1+1/262144) n) :
    ‖(u : ℂ) ^ (N + 1) *
      (residualCoefficient A L N n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n)‖ ≤
      (r^N + lowerRate ^ N) *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (1+1/262144) n) := by
  let x := Real.log (n / p : ℕ) / Real.log n
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hlog : Real.log (n / p : ℕ) = Real.log n - Real.log p := by
    rw [Nat.cast_div hpd (by exact_mod_cast hpp.ne_zero),
      Real.log_div (by exact_mod_cast hn.ne_zero) (by exact_mod_cast hpp.ne_zero)]
  have hx : 0 ≤ x := div_nonneg (Real.log_natCast_nonneg _) hln.le
  have hxhi : x ≤ 1-c := by
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
      (r^N + lowerRate ^ N) * zetaPrimeExpWeight (1+1/262144) n := by
    apply le_trans _ (hk x hx hxhi hcut)
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

/-- One original unassigned arithmetic atom has a summable two-rate bound on the enlarged dominant-prime sector. -/
theorem normalized_residual_dominant_atom (A : Finset ℕ) (N : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u L : ℝ} (hu : 0 ≤ u) (huhi : u ≤ radiusCeiling) (hL0 : 0 < L)
    (hL : L ≤ (139 / 100 : ℝ) * N) {n p : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n) (hnp : ¬n.Prime)
    (hp : p ∈ n.primeFactors) (hpA : p ∈ A) (hel : eligibleCofactor p (n / p))
    (hpL : Real.log p ≤ L) (hdom : (121 / 200 : ℝ) * Real.log n ≤ Real.log p) :
    ‖(u : ℂ) ^ (N + 1) *
      (residualCoefficient A L N n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n)‖ ≤
      (Real.exp (-(1/8000 : ℝ))^N + lowerRate ^ N) *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (1+1/262144) n) := by
  apply normalized_residual_of_missing_kernel A N y hu hL0 hn hn1 hnp hp hpA hel hpL hdom
  intro x hx hxhi hcut
  exact normalized_missing_kernel_bound N n hN y hu huhi hx (by linarith) hcut hL

/-- The entire selected subband is paid independently, uniformly in the
height, label count and every additional finite mask. -/
theorem norm_scaled_sum_le (A D : Finset ℕ) (N : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u L : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (hL0 : 0 < L)
    (hL : L ≤ (139/100 : ℝ)*N)
    (hD : ∀ n ∈ D, Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
      ∃ p ∈ n.primeFactors, p ∈ A ∧ eligibleCofactor p (n/p) ∧
        Real.log p ≤ L ∧ (121/200 : ℝ)*Real.log n ≤ Real.log p) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ D,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      2*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/8000) := by
  have hl : lowerRate^N ≤ Real.exp (-(1/8000 : ℝ))^N := by
    apply pow_le_pow_left₀ (by unfold lowerRate; positivity)
    exact Real.exp_le_exp.mpr (by norm_num)
  have he : Real.exp (-(1/8000 : ℝ))^N = Real.exp (-(N : ℝ)/8000) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ D, (Real.exp (-(1/8000 : ℝ))^N+lowerRate^N)*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
      apply Finset.sum_le_sum
      intro n hnD
      obtain ⟨hn,hn1,hnp,p,hp,hpA,hel,hpL,hdom⟩ := hD n hnD
      exact normalized_residual_dominant_atom A N hN y hu hU hL0 hL
        hn hn1 hnp hp hpA hel hpL hdom
    _ ≤ (Real.exp (-(1/8000 : ℝ))^N+lowerRate^N)*
        zetaMoebiusLogMajorantMass (1+1/262144) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (add_nonneg (by positivity) (pow_nonneg rates_bounds.2.1 N))
    _ ≤ _ := by
      rw [he] at hl ⊢
      nlinarith [mul_le_mul_of_nonneg_right hl (zetaMoebiusLogMajorantMass_nonneg (1+1/262144))]

/-- A direct lower bound for the EXISTING core: delete only the newly
paid eligible large-prime labels, and keep the whole signed complement
together. The signed main sum is not claimed bounded. -/
theorem re_core_ge_without_large (N K : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u : ℝ} (hu : 1/2 ≤ u) (hU : u ≤ radiusCeiling) :
    ((u : ℂ)^(N+1)*∑ n ∈ (coreBand u N K).filter (fun n =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u N ∧
          eligibleCofactor p (n/p) ∧ (121/200 : ℝ)*Real.log n ≤ Real.log p)),
      residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
      2*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/8000) ≤
    ((u : ℂ)^(N+1)*coreResponse u y N K).re := by
  let P := fun n => Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
    ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u N ∧
      eligibleCofactor p (n/p) ∧ (121/200 : ℝ)*Real.log n ≤ Real.log p
  let f := fun n => residualCoefficient (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hL : SquarefreeVaughanLogSource.length u N ≤ (139/100 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu (by omega : 2 ≤ N)
    have hlog : 2*Real.log 2 ≤ (139/100 : ℝ) := by linarith [Real.log_two_lt_d9]
    exact h.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
  have hb := norm_scaled_sum_le (intermediatePrimes u N) ((coreBand u N K).filter P)
    N hN y (by linarith : 0 ≤ u) hU (SquarefreeVaughanLogSource.length_pos u N) hL (by
      intro n hnD
      obtain ⟨_,hn,hn1,hnp,p,hp,hpA,hel,hdom⟩ := Finset.mem_filter.mp hnD
      refine ⟨hn,hn1,hnp,p,hp,hpA,hel,?_,hdom⟩
      have hp' := (mem_intermediatePrimes u N p).mp hpA
      exact (Real.log_lt_log (by exact_mod_cast hp'.1.pos) (by exact_mod_cast hp'.2.2)).le)
  have hs := Finset.sum_filter_add_sum_filter_not (coreBand u N K) P f
  change (∑ n ∈ (coreBand u N K).filter P, f n)+
    (∑ n ∈ (coreBand u N K).filter (fun n => ¬P n), f n) = coreResponse u y N K at hs
  have he := congrArg (fun z : ℂ => ((u : ℂ)^(N+1)*z).re) hs
  rw [mul_add,Complex.add_re] at he
  have hr := (abs_le.mp (Complex.abs_re_le_norm
    ((u : ℂ)^(N+1)*∑ n ∈ (coreBand u N K).filter P, f n))).1
  dsimp only [P,f] at hr hb he
  linarith

/-- On the original cofinal schedule, eligibility is automatic for any
large prime in a nonzero remaining atom. Thus the signed main sum really
has ALL prime logarithms below `121/200` of the total, not just a selected
subset of its primes. -/
theorem remaining_prime_log_lt (j : ℕ) (hj : 32 ≤ j) (u : ℝ) {n : ℕ}
    (hnB : n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter (fun n =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u (dyadicMomentOrder j) ∧
          eligibleCofactor p (n/p) ∧ (121/200 : ℝ)*Real.log n ≤ Real.log p)))
    (hcoeff : residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n ≠ 0) :
    ∀ p ∈ n.primeFactors, Real.log p < (121/200 : ℝ)*Real.log n := by
  let N := dyadicMomentOrder j
  obtain ⟨hncore,hnnot⟩ := Finset.mem_filter.mp hnB
  have hnnarrow := (Finset.mem_filter.mp hncore).1
  have hnnondominant := (Finset.mem_filter.mp hnnarrow).1
  have hnret := (Finset.mem_sdiff.mp hnnondominant).1
  have hnS := (Finset.mem_sdiff.mp hnret).1
  obtain ⟨hnfew,hw⟩ := Finset.mem_filter.mp hnS
  obtain ⟨hncentral,hc3,hcK⟩ := Finset.mem_filter.mp hnfew
  have hn : Squarefree n := by
    by_contra h
    apply hcoeff
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,h]
  have hnp : ¬n.Prime := by
    intro h
    rw [h.primeFactors,Finset.card_singleton] at hc3
    omega
  have hpX : ∀ p ∈ n.primeFactors,
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hncentral).1).1).2
  intro p hp
  by_contra hdom
  have hdom' : (121/200 : ℝ)*Real.log n ≤ Real.log p := le_of_not_gt hdom
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hn1 : 1 < n := lt_of_lt_of_le hpp.one_lt
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) hpd)
  have hpN : N^2 < p := by
    by_contra hh
    have hpN' : p ≤ N^2 := le_of_not_gt hh
    have hsmall := few_smooth_divisor_log_le j hj hn hpd hcK (by
      intro q hq
      have hqp : q = p := by simpa only [hpp.primeFactors,Finset.mem_singleton] using hq
      simpa only [hqp] using hpN')
    have hlo : (7/4 : ℝ)*N < Real.log n := hw.1
    change Real.log p ≤ (N : ℝ)/4 at hsmall
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hpA : p ∈ intermediatePrimes u N :=
    (mem_intermediatePrimes u N p).mpr ⟨hpp,hpN,hpX p hp⟩
  exact hnnot ⟨hn,hn1,hnp,p,hp,hpA,eligible_of_three_prime_factors hn hc3 hp,hdom'⟩

/-- The allowance in the joint signed inequality vanishes on the original
order scale, without any zero or fixed-height hypothesis. -/
theorem tendsto_allowance :
    Tendsto (fun N : ℕ => 2*zetaMoebiusLogMajorantMass (1+1/262144)*
      Real.exp (-(N : ℝ)/8000)) atTop (𝓝 0) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (Real.exp_pos (-(1/8000 : ℝ))).le
    (Real.exp_lt_one_iff.mpr (by norm_num : -(1/8000 : ℝ) < 0))).const_mul
      (2*zetaMoebiusLogMajorantMass (1+1/262144))
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [] with N
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-! A second concrete tilt enlarges the paid sector. The earlier faster
bound remains available verbatim on its original smaller sector. -/
namespace Refined

private theorem upper_log_rate :
    Real.log (101197/100000 : ℝ)-(13/32 : ℝ)*Real.log (103/100 : ℝ) ≤ -(1/9200 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 3/203)
    (by norm_num : (3/203 : ℝ) < 1) 2
  norm_num [Finset.sum_range_succ] at hlo
  have hhi : Real.log (101197/100000 : ℝ) ≤ 23799/2000000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 23799/2000000) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  linarith

/-- The restricted radius pays the high missing tail with an explicit
`exp(-N/1000000)` rate after the original source normalization. -/
theorem upper_scalar (N : ℕ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) :
    u^(N+1)*((101197/100000 : ℝ)*Real.exp (-(N : ℝ)/9200))*
      (262144/131071 : ℝ)^N ≤ Real.exp (-(1/1000000 : ℝ))^N := by
  have hr : radiusCeiling*(262144/131071 : ℝ)*Real.exp (-(1/9200 : ℝ)) ≤
      Real.exp (-(1/1000000 : ℝ)) := by
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
    norm_num
    have h := Real.add_one_le_exp (1/9200-1/1000000 : ℝ)
    norm_num [radiusCeiling]
    linarith
  have he : Real.exp (-(N : ℝ)/9200) = Real.exp (-(1/9200 : ℝ))^N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ radiusCeiling^(N+1)*((101197/100000 : ℝ)*Real.exp (-(N : ℝ)/9200))*
        (262144/131071 : ℝ)^N := by gcongr
    _ = (radiusCeiling*(101197/100000 : ℝ))*
        (radiusCeiling*(262144/131071 : ℝ)*Real.exp (-(1/9200 : ℝ)))^N := by
      rw [he,mul_pow,mul_pow,pow_succ]
      ring
    _ ≤ Real.exp (-(1/1000000 : ℝ))^N := by
      have hp := pow_le_pow_left₀ (by unfold radiusCeiling; positivity) hr N
      have hc : 0 ≤ radiusCeiling*(101197/100000 : ℝ) ∧
          radiusCeiling*(101197/100000 : ℝ) ≤ 1 := by norm_num [radiusCeiling]
      exact (mul_le_mul_of_nonneg_left hp hc.1).trans
        (mul_le_of_le_one_left (by positivity) hc.2)

/-- Both original missing tails, with the upper one retuned to cofactor share `399/1000`. The lower tail still retains its exact logarithm dependence. -/
theorem missing_allocation_cutoff_bound (N : ℕ) (hN : 320 ≤ N) {x : ℝ}
    (hx : 0 ≤ x) (hxhi : x ≤ 399 / 1000) :
    1 - (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N + 1) k x) ≤
      (101197 / 100000 : ℝ) * Real.exp (-(N : ℝ) / 9200) +
      Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ)) *
        ((5 / 6 : ℝ) * x + (1 - x)) ^ (N + 1) := by
  have hx1 : x ≤ 1 := by linarith
  have ht : 0 ≤ Real.log (103 / 100 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have h := missed_mass_bound N hN hx hx1
    (Real.exp_pos (-(13 / 32 : ℝ) * N * Real.log (103 / 100 : ℝ))).le
    (Real.exp_pos (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ))).le
    (by norm_num : (0 : ℝ) ≤ 103 / 100) (by norm_num : (0 : ℝ) ≤ 5 / 6) ?_ ?_
  · apply h.trans
    apply add_le_add _ le_rfl
    have hb : ((103 / 100 : ℝ) * x + (1 - x)) ^ (N + 1) ≤ (101197 / 100000 : ℝ) ^ (N + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have he : Real.exp (-(13 / 32 : ℝ) * N * Real.log (103 / 100 : ℝ)) *
        (101197 / 100000 : ℝ) ^ (N + 1) = (101197 / 100000 : ℝ) *
          Real.exp ((N : ℝ) * (Real.log (101197 / 100000 : ℝ) -
            (13 / 32 : ℝ) * Real.log (103 / 100 : ℝ))) := by
      rw [pow_succ]
      have hp : (101197 / 100000 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log (101197 / 100000 : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [hp, show (N : ℝ) * (Real.log (101197 / 100000 : ℝ) -
        (13 / 32 : ℝ) * Real.log (103 / 100 : ℝ)) =
          -(13 / 32 : ℝ) * N * Real.log (103 / 100 : ℝ) +
            (N : ℝ) * Real.log (101197 / 100000 : ℝ) by ring, Real.exp_add]
      ring
    calc
      _ ≤ Real.exp (-(13 / 32 : ℝ) * N * Real.log (103 / 100 : ℝ)) * (101197 / 100000 : ℝ) ^ (N + 1) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = _ := he
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left upper_log_rate (Nat.cast_nonneg (α := ℝ) N)]))
          (by norm_num)
  · intro k hk hcut
    have hc : (13 / 32 : ℝ) * N ≤ k := by
      have hn : 13 * N < 32 * k := by omega
      have hnR : (13 : ℝ) * N < 32 * k := by exact_mod_cast hn
      linarith
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 103 / 100),
      ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    simp only [Real.log_exp]
    nlinarith [mul_le_mul_of_nonneg_right hc ht]
  · intro k hk hcut
    have hkN : k ≤ N + 1 := by have := Finset.mem_range.mp hk; omega
    have hc : (k : ℝ) ≤ (N : ℝ) / 5 + 1 := by
      have hn : 5 * k ≤ N + 5 := by omega
      have hnR : (5 : ℝ) * k ≤ N + 5 := by exact_mod_cast hn
      linarith
    have he : (5 / 6 : ℝ) = Real.exp (-Real.log (6 / 5 : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc hl]

/-- The source-normalized original factorial kernel is controlled down to
cofactor share `399/1000`, with the physical lower tail unchanged. -/
theorem normalized_missing_kernel_bound (N n : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u L x : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hx : 0 ≤ x) (hxhi : x ≤ 399/1000)
    (hcut : (1-x)*Real.log n ≤ L) (hL : L ≤ (139/100 : ℝ)*N) :
    u^(N+1)*(1-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x)*
      ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (Real.exp (-(1/1000000 : ℝ))^N+lowerRate^N)*zetaPrimeExpWeight (1+1/262144) n := by
  exact kernel_of_missing N n y hu hU hx (by linarith) (by norm_num)
    hcut hL (missing_allocation_cutoff_bound N hN hx hxhi) (upper_scalar N hu hU)

/-- One original unassigned arithmetic atom has a summable two-rate bound on the enlarged dominant-prime sector. -/
theorem normalized_residual_dominant_atom (A : Finset ℕ) (N : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u L : ℝ} (hu : 0 ≤ u) (huhi : u ≤ radiusCeiling) (hL0 : 0 < L)
    (hL : L ≤ (139 / 100 : ℝ) * N) {n p : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n) (hnp : ¬n.Prime)
    (hp : p ∈ n.primeFactors) (hpA : p ∈ A) (hel : eligibleCofactor p (n / p))
    (hpL : Real.log p ≤ L) (hdom : (601 / 1000 : ℝ) * Real.log n ≤ Real.log p) :
    ‖(u : ℂ) ^ (N + 1) *
      (residualCoefficient A L N n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n)‖ ≤
      (Real.exp (-(1/1000000 : ℝ))^N + lowerRate ^ N) *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (1+1/262144) n) := by
  apply normalized_residual_of_missing_kernel A N y hu hL0 hn hn1 hnp hp hpA hel hpL hdom
  intro x hx hxhi hcut
  exact normalized_missing_kernel_bound N n hN y hu huhi hx (by linarith) hcut hL

/-- The entire selected subband is paid independently, uniformly in the
height, label count and every additional finite mask. -/
theorem norm_scaled_sum_le (A D : Finset ℕ) (N : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u L : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (hL0 : 0 < L)
    (hL : L ≤ (139/100 : ℝ)*N)
    (hD : ∀ n ∈ D, Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
      ∃ p ∈ n.primeFactors, p ∈ A ∧ eligibleCofactor p (n/p) ∧
        Real.log p ≤ L ∧ (601/1000 : ℝ)*Real.log n ≤ Real.log p) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ D,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      2*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000) := by
  have hl : lowerRate^N ≤ Real.exp (-(1/1000000 : ℝ))^N := by
    apply pow_le_pow_left₀ (by unfold lowerRate; positivity)
    exact Real.exp_le_exp.mpr (by norm_num)
  have he : Real.exp (-(1/1000000 : ℝ))^N = Real.exp (-(N : ℝ)/1000000) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ D, (Real.exp (-(1/1000000 : ℝ))^N+lowerRate^N)*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
      apply Finset.sum_le_sum
      intro n hnD
      obtain ⟨hn,hn1,hnp,p,hp,hpA,hel,hpL,hdom⟩ := hD n hnD
      exact normalized_residual_dominant_atom A N hN y hu hU hL0 hL
        hn hn1 hnp hp hpA hel hpL hdom
    _ ≤ (Real.exp (-(1/1000000 : ℝ))^N+lowerRate^N)*
        zetaMoebiusLogMajorantMass (1+1/262144) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (add_nonneg (by positivity) (pow_nonneg rates_bounds.2.1 N))
    _ ≤ _ := by
      rw [he] at hl ⊢
      nlinarith [mul_le_mul_of_nonneg_right hl (zetaMoebiusLogMajorantMass_nonneg (1+1/262144))]

/-- A direct lower bound for the EXISTING core: delete only the newly
paid eligible large-prime labels, and keep the whole signed complement
together. The signed main sum is not claimed bounded. -/
theorem re_core_ge_without_large (N K : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u : ℝ} (hu : 1/2 ≤ u) (hU : u ≤ radiusCeiling) :
    ((u : ℂ)^(N+1)*∑ n ∈ (coreBand u N K).filter (fun n =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u N ∧
          eligibleCofactor p (n/p) ∧ (601/1000 : ℝ)*Real.log n ≤ Real.log p)),
      residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
      2*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000) ≤
    ((u : ℂ)^(N+1)*coreResponse u y N K).re := by
  let P := fun n => Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
    ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u N ∧
      eligibleCofactor p (n/p) ∧ (601/1000 : ℝ)*Real.log n ≤ Real.log p
  let f := fun n => residualCoefficient (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hL : SquarefreeVaughanLogSource.length u N ≤ (139/100 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu (by omega : 2 ≤ N)
    have hlog : 2*Real.log 2 ≤ (139/100 : ℝ) := by linarith [Real.log_two_lt_d9]
    exact h.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
  have hb := norm_scaled_sum_le (intermediatePrimes u N) ((coreBand u N K).filter P)
    N hN y (by linarith : 0 ≤ u) hU (SquarefreeVaughanLogSource.length_pos u N) hL (by
      intro n hnD
      obtain ⟨_,hn,hn1,hnp,p,hp,hpA,hel,hdom⟩ := Finset.mem_filter.mp hnD
      refine ⟨hn,hn1,hnp,p,hp,hpA,hel,?_,hdom⟩
      have hp' := (mem_intermediatePrimes u N p).mp hpA
      exact (Real.log_lt_log (by exact_mod_cast hp'.1.pos) (by exact_mod_cast hp'.2.2)).le)
  have hs := Finset.sum_filter_add_sum_filter_not (coreBand u N K) P f
  change (∑ n ∈ (coreBand u N K).filter P, f n)+
    (∑ n ∈ (coreBand u N K).filter (fun n => ¬P n), f n) = coreResponse u y N K at hs
  have he := congrArg (fun z : ℂ => ((u : ℂ)^(N+1)*z).re) hs
  rw [mul_add,Complex.add_re] at he
  have hr := (abs_le.mp (Complex.abs_re_le_norm
    ((u : ℂ)^(N+1)*∑ n ∈ (coreBand u N K).filter P, f n))).1
  dsimp only [P,f] at hr hb he
  linarith

/-- On the original cofinal schedule, eligibility is automatic for any
large prime in a nonzero remaining atom. Thus the signed main sum really
has ALL prime logarithms below `601/1000` of the total, not just a selected
subset of its primes. -/
theorem remaining_prime_log_lt (j : ℕ) (hj : 32 ≤ j) (u : ℝ) {n : ℕ}
    (hnB : n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter (fun n =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u (dyadicMomentOrder j) ∧
          eligibleCofactor p (n/p) ∧ (601/1000 : ℝ)*Real.log n ≤ Real.log p)))
    (hcoeff : residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n ≠ 0) :
    ∀ p ∈ n.primeFactors, Real.log p < (601/1000 : ℝ)*Real.log n := by
  let N := dyadicMomentOrder j
  obtain ⟨hncore,hnnot⟩ := Finset.mem_filter.mp hnB
  have hnnarrow := (Finset.mem_filter.mp hncore).1
  have hnnondominant := (Finset.mem_filter.mp hnnarrow).1
  have hnret := (Finset.mem_sdiff.mp hnnondominant).1
  have hnS := (Finset.mem_sdiff.mp hnret).1
  obtain ⟨hnfew,hw⟩ := Finset.mem_filter.mp hnS
  obtain ⟨hncentral,hc3,hcK⟩ := Finset.mem_filter.mp hnfew
  have hn : Squarefree n := by
    by_contra h
    apply hcoeff
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,h]
  have hnp : ¬n.Prime := by
    intro h
    rw [h.primeFactors,Finset.card_singleton] at hc3
    omega
  have hpX : ∀ p ∈ n.primeFactors,
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hncentral).1).1).2
  intro p hp
  by_contra hdom
  have hdom' : (601/1000 : ℝ)*Real.log n ≤ Real.log p := le_of_not_gt hdom
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hn1 : 1 < n := lt_of_lt_of_le hpp.one_lt
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) hpd)
  have hpN : N^2 < p := by
    by_contra hh
    have hpN' : p ≤ N^2 := le_of_not_gt hh
    have hsmall := few_smooth_divisor_log_le j hj hn hpd hcK (by
      intro q hq
      have hqp : q = p := by simpa only [hpp.primeFactors,Finset.mem_singleton] using hq
      simpa only [hqp] using hpN')
    have hlo : (7/4 : ℝ)*N < Real.log n := hw.1
    change Real.log p ≤ (N : ℝ)/4 at hsmall
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hpA : p ∈ intermediatePrimes u N :=
    (mem_intermediatePrimes u N p).mpr ⟨hpp,hpN,hpX p hp⟩
  exact hnnot ⟨hn,hn1,hnp,p,hp,hpA,eligible_of_three_prime_factors hn hc3 hp,hdom'⟩

/-- The allowance in the joint signed inequality vanishes on the original
order scale, without any zero or fixed-height hypothesis. -/
theorem tendsto_allowance :
    Tendsto (fun N : ℕ => 2*zetaMoebiusLogMajorantMass (1+1/262144)*
      Real.exp (-(N : ℝ)/1000000)) atTop (𝓝 0) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (Real.exp_pos (-(1/1000000 : ℝ))).le
    (Real.exp_lt_one_iff.mpr (by norm_num : -(1/1000000 : ℝ) < 0))).const_mul
      (2*zetaMoebiusLogMajorantMass (1+1/262144))
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [] with N
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-- The two independently paid errors are combined before observing the
whole core. The raw small-prime part and the remaining transition stay
inside one real part; neither is assumed nonnegative or small. -/
theorem re_core_ge_joint_reduced (N K : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u : ℝ} (hu : 1/2 ≤ u) (hU : u ≤ radiusCeiling) :
    let S := (coreBand u N K).filter (fun n =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u N ∧
          eligibleCofactor p (n/p) ∧ (601/1000 : ℝ)*Real.log n ≤ Real.log p))
    ∀ D : Finset ℕ, D ⊆ S →
      (∀ n ∈ D, ∀ p ∈ n.primeFactors, p ∈ intermediatePrimes u N →
        eligibleCofactor p (n/p) → Real.log p ≤ (293/500 : ℝ)*Real.log n) →
    ((u : ℂ)^(N+1)*
      ((∑ n ∈ D, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
        ∑ n ∈ S\D,
          residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re-
      ((4*radiusCeiling)*((N : ℝ)+1)*ZetaRieszJointAllocationFloor.Refined.allocationRate^N+
        2*Real.exp (-(N : ℝ)/1000000))*zetaMoebiusLogMajorantMass (1+1/262144) ≤
      ((u : ℂ)^(N+1)*coreResponse u y N K).re := by
  dsimp only
  intro D hD hbal
  have hwindow : D ⊆ literalWindow N := by
    intro n hn
    have hw := (Finset.mem_filter.mp (Finset.mem_filter.mp (hD hn)).1).2
    apply (mem_literalWindow N n).mpr
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) N]
  have hlo := ZetaRieszJointAllocationFloor.Refined.re_sum_ge_joint_unallocated
    _ _ D (SquarefreeVaughanLogSource.length_pos u N) N hD hwindow hbal y
      (by linarith : 0 ≤ u) hU
  have hhi := re_core_ge_without_large N K hN y hu hU
  dsimp only [coreResponse] at hlo hhi ⊢
  linarith

/-- Both costs of the combined one-sided inequality tend to zero. -/
theorem tendsto_joint_allowance :
    Tendsto (fun N : ℕ =>
      ((4*radiusCeiling)*((N : ℝ)+1)*ZetaRieszJointAllocationFloor.Refined.allocationRate^N+
        2*Real.exp (-(N : ℝ)/1000000))*zetaMoebiusLogMajorantMass (1+1/262144))
      atTop (𝓝 0) := by
  have h := ZetaRieszJointAllocationFloor.Refined.tendsto_allowance.add tendsto_allowance
  simp only [add_zero] at h
  exact h.congr' (Eventually.of_forall fun _ => by ring)

end Refined

/-- Every positive exponential tilt at the 60% share boundary still grows
under the current fixed source envelope at its upper radius. This does not
exclude a signed bound or a different joint arithmetic estimate. -/
theorem sixty_percent_all_tilts_grow {q : ℝ} (hq : 0 < q) :
    (1/60000 : ℝ) <
      Real.log (ZetaRieszWideOwnerAudit.radiusCeiling*(262144/131071 : ℝ))+
        Real.log ((2/5 : ℝ)*q+3/5)-(13/32 : ℝ)*Real.log q := by
  let a := (2/5 : ℝ)*q+3/5
  have ha : 0 < a := by dsimp [a]; positivity
  have h1 := Real.log_le_sub_one_of_pos (show 0 < ((64/65 : ℝ)*q)/a by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show 0 < (96/95 : ℝ)/a by positivity)
  have hs : (13/32 : ℝ)*(((64/65 : ℝ)*q)/a-1)+
      (19/32 : ℝ)*((96/95 : ℝ)/a-1) = 0 := by
    dsimp [a]
    field_simp
    ring
  have h := add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 13/32))
    (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 19/32))
  rw [hs, Real.log_div (by positivity) ha.ne', Real.log_div (by norm_num) ha.ne',
    Real.log_mul (by norm_num) hq.ne'] at h
  have hupper : Real.log (65/64 : ℝ) ≤ 3101/200000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3101/200000) 4
    norm_num [Finset.sum_range_succ] at he
    linarith
  have hinv : Real.log (64/65 : ℝ) = -Real.log (65/64 : ℝ) := by
    rw [show (64/65 : ℝ) = (65/64 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1/191)
    (by norm_num : (1/191 : ℝ) < 1) 1
  norm_num [Finset.sum_range_succ] at hlo
  have hbest : -(1/12000 : ℝ) < Real.log a-(13/32 : ℝ)*Real.log q := by
    rw [hinv] at h
    linarith
  have hcost : (1/10000 : ℝ) <
      Real.log (ZetaRieszWideOwnerAudit.radiusCeiling*(262144/131071 : ℝ)) := by
    have he := Real.log_le_sub_one_of_pos
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
        0 < (ZetaRieszWideOwnerAudit.radiusCeiling*(262144/131071 : ℝ))⁻¹)
    rw [Real.log_inv] at he
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at he ⊢
    linarith
  dsimp [a] at hbest
  linarith

/-- The other allocation tail also has a genuine limit to scalar tuning:
at a 59% share, no positive exponential tilt beats the same fixed envelope
at the upper source radius. This concerns the estimate, not the signed sum. -/
theorem fifty_nine_percent_all_tilts_grow {q : ℝ} (hq : 0 < q) :
    (1/60000 : ℝ) <
      Real.log (ZetaRieszWideOwnerAudit.radiusCeiling*(262144/131071 : ℝ))+
        Real.log ((41/100 : ℝ)*q+59/100)-(13/32 : ℝ)*Real.log q := by
  let a := (41/100 : ℝ)*q+59/100
  have ha : 0 < a := by dsimp [a]; positivity
  have h1 := Real.log_le_sub_one_of_pos (show 0 < ((328/325 : ℝ)*q)/a by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show 0 < (472/475 : ℝ)/a by positivity)
  have hs : (13/32 : ℝ)*(((328/325 : ℝ)*q)/a-1)+
      (19/32 : ℝ)*((472/475 : ℝ)/a-1) = 0 := by
    dsimp [a]
    field_simp
    ring
  have h := add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 13/32))
    (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 19/32))
  rw [hs,Real.log_div (by positivity) ha.ne',Real.log_div (by norm_num) ha.ne',
    Real.log_mul (by norm_num) hq.ne'] at h
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 328/325)
  have hr := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 472/475)
  norm_num at hl hr
  have hbest : -(1/12000 : ℝ) < Real.log a-(13/32 : ℝ)*Real.log q := by linarith
  have hcost := Real.one_sub_inv_le_log_of_pos
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
      0 < ZetaRieszWideOwnerAudit.radiusCeiling*(262144/131071 : ℝ))
  norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hcost ⊢
  dsimp [a] at hbest
  linarith


end
end RiemannGaussian.ZetaRieszJointDominantFloor

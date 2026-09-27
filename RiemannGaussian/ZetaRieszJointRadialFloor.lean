/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointDominantFloor

/-!
# Joint radial and allocation savings in the literal core

The allocation tail and total-log position are estimated together. This
pays additional 60% dominant-prime labels away from the factorial saddle,
where neither the old share-only bound nor the radial bound suffices.
Every undeleted term stays inside the same signed core comparison.
-/

namespace RiemannGaussian.ZetaRieszJointRadialFloor
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszBalancedCompanion
open ZetaRieszDominantAllocation ZetaRieszWideOwnerAudit ZetaRieszParityPacket
open ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint

private theorem dominant_lower_log_rate :
    Real.log (radiusCeiling*(248/125 : ℝ))+1-
      (131071/262144 : ℝ)*(248/125)-(1/12500) ≤ -(1/400000 : ℝ) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 2469/622531)
    (by norm_num : (2469/622531 : ℝ) < 1) 2
  have he : (1+(2469/622531 : ℝ))/(1-(2469/622531)) =
      (radiusCeiling*(248/125))⁻¹ := by norm_num [radiusCeiling]
  rw [he,Real.log_inv] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem dominant_upper_log_rate :
    Real.log (radiusCeiling*(252/125 : ℝ))+1-
      (131071/262144 : ℝ)*(252/125)-(1/12500) ≤ -(1/400000 : ℝ) := by
  have hlog : Real.log (radiusCeiling*(252/125 : ℝ)) ≤ (1652697/204800000 : ℝ) := by
    apply (Real.log_le_iff_le_exp (by norm_num [radiusCeiling])).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1652697/204800000) 4
    norm_num [Finset.sum_range_succ,radiusCeiling] at h ⊢
    linarith
  linarith

private theorem assigned_lower_log_rate :
    Real.log (radiusCeiling*(987/500 : ℝ))+1-
      (131071/262144 : ℝ)*(987/500)-(1/35000) ≤ -(1/400000 : ℝ) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 129013/19870987)
    (by norm_num : (129013/19870987 : ℝ) < 1) 2
  have he : (1+(129013/19870987 : ℝ))/(1-(129013/19870987)) =
      (radiusCeiling*(987/500))⁻¹ := by norm_num [radiusCeiling]
  rw [he,Real.log_inv] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem assigned_upper_log_rate :
    Real.log (radiusCeiling*(507/250 : ℝ))+1-
      (131071/262144 : ℝ)*(507/250)-(1/35000) ≤ -(1/400000 : ℝ) := by
  have hlog : Real.log (radiusCeiling*(507/250 : ℝ)) ≤ (160773483/11468800000 : ℝ) := by
    apply (Real.log_le_iff_le_exp (by norm_num [radiusCeiling])).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 160773483/11468800000) 4
    norm_num [Finset.sum_range_succ,radiusCeiling] at h ⊢
    linarith
  linarith

private theorem rate_with_saving {t δ : ℝ} (ht : 0 < t)
    (hlog : Real.log (radiusCeiling*t)+1-(131071/262144 : ℝ)*t-δ ≤ -(1/400000 : ℝ)) :
    radiusCeiling*zetaLogMomentRate (131071/262144) t*Real.exp (-δ) ≤
      Real.exp (-(1/400000 : ℝ)) := by
  have htU : 0 < radiusCeiling*t := by unfold radiusCeiling; positivity
  rw [zetaLogMomentRate]
  calc
    _ = Real.exp (Real.log (radiusCeiling*t)+1-(131071/262144 : ℝ)*t-δ) := by
      rw [show Real.log (radiusCeiling*t)+1-(131071/262144 : ℝ)*t-δ =
        Real.log (radiusCeiling*t)+(1-(131071/262144 : ℝ)*t)+(-δ) by ring,
        Real.exp_add,Real.exp_add,Real.exp_log htU]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hlog

private theorem kernel_radial_saving (N n : ℕ) (y : ℝ)
    {u a b δ : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (ha : 0 < a) (hb : 0 < b)
    (ha0 : (131071/262144 : ℝ)*a ≤ 1) (hb0 : 1 ≤ (131071/262144 : ℝ)*b)
    (hra : radiusCeiling*zetaLogMomentRate (131071/262144) a*Real.exp (-δ) ≤
      Real.exp (-(1/400000 : ℝ)))
    (hrb : radiusCeiling*zetaLogMomentRate (131071/262144) b*Real.exp (-δ) ≤
      Real.exp (-(1/400000 : ℝ)))
    (hn : Real.log n ≤ a*N ∨ b*N ≤ Real.log n) :
    u^(N+1)*Real.exp (-(N : ℝ)*δ)*‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      radiusCeiling*Real.exp (-(1/400000 : ℝ))^N*zetaPrimeExpWeight (1+1/262144) n := by
  have hstep (t : ℝ) (ht : 0 < t)
      (hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        zetaLogMomentRate (131071/262144) t^N*zetaPrimeExpWeight (1+1/262144) n)
      (hr : radiusCeiling*zetaLogMomentRate (131071/262144) t*Real.exp (-δ) ≤
        Real.exp (-(1/400000 : ℝ))) :
      u^(N+1)*Real.exp (-(N : ℝ)*δ)*‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        radiusCeiling*Real.exp (-(1/400000 : ℝ))^N*zetaPrimeExpWeight (1+1/262144) n := by
    have he : Real.exp (-(N : ℝ)*δ) = Real.exp (-δ)^N := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hp := pow_le_pow_left₀ (by unfold radiusCeiling zetaLogMomentRate; positivity) hr N
    calc
      _ ≤ radiusCeiling^(N+1)*Real.exp (-(N : ℝ)*δ)*
          (zetaLogMomentRate (131071/262144) t^N*zetaPrimeExpWeight (1+1/262144) n) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu hU _) (Real.exp_pos _).le
        · exact hk
        · exact norm_nonneg _
        · unfold radiusCeiling
          positivity
      _ = radiusCeiling*(radiusCeiling*zetaLogMomentRate (131071/262144) t*
          Real.exp (-δ))^N*zetaPrimeExpWeight (1+1/262144) n := by
        rw [he,mul_pow,mul_pow,pow_succ]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by norm_num [radiusCeiling])) (Real.exp_pos _).le
  rcases hn with hn | hn
  · apply hstep a ha _ hra
    have h := norm_zetaPrimeLogKernel_le_lower_chernoff N 0 n (3/2+Complex.I*y)
      (τ := 1+1/262144) ha (by norm_num; exact ha0) hn
    have hr : (3/2+Complex.I*(y : ℂ)).re-(1+1/262144) = (131071/262144 : ℝ) := by norm_num
    rw [hr] at h
    simpa only [Nat.add_zero,pow_zero,mul_one] using h
  · apply hstep b hb _ hrb
    have h := norm_zetaPrimeLogKernel_le_upper_chernoff N 0 n (3/2+Complex.I*y)
      (τ := 1+1/262144) hb (by norm_num; exact hb0) hn
    have hr : (3/2+Complex.I*(y : ℂ)).re-(1+1/262144) = (131071/262144 : ℝ) := by norm_num
    rw [hr] at h
    simpa only [Nat.add_zero,pow_zero,mul_one] using h

private theorem upper_log_rate :
    Real.log (101/100 : ℝ)-(13/32 : ℝ)*Real.log (41/40 : ℝ) ≤ -(1/12500 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1/81)
    (by norm_num : (1/81 : ℝ) < 1) 1
  norm_num [Finset.sum_range_succ] at hlo
  have hhi : Real.log (101/100 : ℝ) ≤ 497517/50000000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 497517/50000000) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  linarith

private theorem missing_allocation_cutoff_bound (N : ℕ) (hN : 320 ≤ N) {x : ℝ}
    (hx : 0 ≤ x) (hxhi : x ≤ 2 / 5) :
    1 - (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N + 1) k x) ≤
      (101 / 100 : ℝ) * Real.exp (-(N : ℝ) / 12500) +
      Real.exp (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ)) *
        ((5 / 6 : ℝ) * x + (1 - x)) ^ (N + 1) := by
  have hx1 : x ≤ 1 := by linarith
  have ht : 0 ≤ Real.log (41 / 40 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have h := missed_mass_bound N hN hx hx1
    (Real.exp_pos (-(13 / 32 : ℝ) * N * Real.log (41 / 40 : ℝ))).le
    (Real.exp_pos (((N : ℝ) / 5 + 1) * Real.log (6 / 5 : ℝ))).le
    (by norm_num : (0 : ℝ) ≤ 41 / 40) (by norm_num : (0 : ℝ) ≤ 5 / 6) ?_ ?_
  · apply h.trans
    apply add_le_add _ le_rfl
    have hb : ((41 / 40 : ℝ) * x + (1 - x)) ^ (N + 1) ≤ (101 / 100 : ℝ) ^ (N + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have he : Real.exp (-(13 / 32 : ℝ) * N * Real.log (41 / 40 : ℝ)) *
        (101 / 100 : ℝ) ^ (N + 1) = (101 / 100 : ℝ) *
          Real.exp ((N : ℝ) * (Real.log (101 / 100 : ℝ) -
            (13 / 32 : ℝ) * Real.log (41 / 40 : ℝ))) := by
      rw [pow_succ]
      have hp : (101 / 100 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log (101 / 100 : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [hp, show (N : ℝ) * (Real.log (101 / 100 : ℝ) -
        (13 / 32 : ℝ) * Real.log (41 / 40 : ℝ)) =
          -(13 / 32 : ℝ) * N * Real.log (41 / 40 : ℝ) +
            (N : ℝ) * Real.log (101 / 100 : ℝ) by ring, Real.exp_add]
      ring
    calc
      _ ≤ Real.exp (-(13 / 32 : ℝ) * N * Real.log (41 / 40 : ℝ)) * (101 / 100 : ℝ) ^ (N + 1) :=
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
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40),
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

/-- Joint radial information pays the high missing allocation tail at
60% prime share. The original physical cutoff still pays its lower tail. -/
theorem normalized_missing_kernel_bound (N n : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u L x : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hx : 0 ≤ x) (hxhi : x ≤ 2/5)
    (hcut : (1-x)*Real.log n ≤ L) (hL : L ≤ (139/100 : ℝ)*N)
    (hrad : Real.log n ≤ (248/125 : ℝ)*N ∨ (252/125 : ℝ)*N ≤ Real.log n) :
    u^(N+1)*(1-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x)*
      ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (Real.exp (-(1/400000 : ℝ))^N+lowerRate^N)*zetaPrimeExpWeight (1+1/262144) n := by
  apply ZetaRieszJointDominantFloor.normalized_missing_of_kernel_bound N n y hu hU
    hx (by linarith) hcut hL (missing_allocation_cutoff_bound N hN hx hxhi)
  have hk := kernel_radial_saving N n y hu hU (by norm_num : (0 : ℝ) < 248/125)
    (by norm_num : (0 : ℝ) < 252/125) (by norm_num) (by norm_num)
    (rate_with_saving (by norm_num) dominant_lower_log_rate)
    (rate_with_saving (by norm_num) dominant_upper_log_rate) hrad
  have h := mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 101/100)
  have hpre : (101/100 : ℝ)*radiusCeiling ≤ 1 := by norm_num [radiusCeiling]
  have hc := mul_le_mul_of_nonneg_right hpre
    (show 0 ≤ Real.exp (-(1/400000 : ℝ))^N*zetaPrimeExpWeight (1+1/262144) n by
      unfold zetaPrimeExpWeight
      positivity)
  calc
    _ = (101/100 : ℝ)*(u^(N+1)*Real.exp (-(N : ℝ)*(1/12500))*
        ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) := by
      ring
    _ ≤ (101/100 : ℝ)*(radiusCeiling*Real.exp (-(1/400000 : ℝ))^N*
        zetaPrimeExpWeight (1+1/262144) n) := h
    _ ≤ _ := by simpa only [mul_assoc,one_mul] using hc

/-- The actual unassigned coefficient, phase and kernel have geometric
saving on the joint radial/share region, with no prime-count ceiling. -/
theorem normalized_residual_atom (A : Finset ℕ) (N : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u L : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (hL0 : 0 < L)
    (hL : L ≤ (139/100 : ℝ)*N) {n p : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n) (hnp : ¬n.Prime)
    (hp : p ∈ n.primeFactors) (hpA : p ∈ A) (hel : eligibleCofactor p (n/p))
    (hpL : Real.log p ≤ L) (hshare : (3/5 : ℝ)*Real.log n ≤ Real.log p)
    (hrad : Real.log n ≤ (248/125 : ℝ)*N ∨ (252/125 : ℝ)*N ≤ Real.log n) :
    ‖(u : ℂ)^(N+1)*(residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖ ≤
      (Real.exp (-(1/400000 : ℝ))^N+lowerRate^N)*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
  apply ZetaRieszJointDominantFloor.normalized_residual_of_missing_kernel
    A N y hu hL0 hn hn1 hnp hp hpA hel hpL hshare
  intro x hx hxhi hcut
  exact normalized_missing_kernel_bound N n hN y hu hU hx (by linarith) hcut hL hrad

/-- The entire actual selected sum is paid, uniformly in height and in
all further finite masks. The constant is the existing summable mass. -/
theorem norm_residual_sum_le (A D : Finset ℕ) (N : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u L : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (hL0 : 0 < L)
    (hL : L ≤ (139/100 : ℝ)*N)
    (hD : ∀ n ∈ D, Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
      ∃ p ∈ n.primeFactors, p ∈ A ∧ eligibleCofactor p (n/p) ∧
        Real.log p ≤ L ∧ (3/5 : ℝ)*Real.log n ≤ Real.log p)
    (hrad : ∀ n ∈ D, Real.log n ≤ (248/125 : ℝ)*N ∨ (252/125 : ℝ)*N ≤ Real.log n) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ D,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      2*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/400000) := by
  have hl : lowerRate^N ≤ Real.exp (-(1/400000 : ℝ))^N := by
    apply pow_le_pow_left₀ (by unfold lowerRate; positivity)
    exact Real.exp_le_exp.mpr (by norm_num)
  have he : Real.exp (-(1/400000 : ℝ))^N = Real.exp (-(N : ℝ)/400000) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ D, (Real.exp (-(1/400000 : ℝ))^N+lowerRate^N)*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
      apply Finset.sum_le_sum
      intro n hnD
      obtain ⟨hn,hn1,hnp,p,hp,hpA,hel,hpL,hdom⟩ := hD n hnD
      exact normalized_residual_atom A N hN y hu hU hL0 hL
        hn hn1 hnp hp hpA hel hpL hdom (hrad n hnD)
    _ ≤ (Real.exp (-(1/400000 : ℝ))^N+lowerRate^N)*
        zetaMoebiusLogMajorantMass (1+1/262144) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (add_nonneg (by positivity) (pow_nonneg rates_bounds.2.1 N))
    _ ≤ _ := by
      rw [he] at hl ⊢
      nlinarith [mul_le_mul_of_nonneg_right hl (zetaMoebiusLogMajorantMass_nonneg (1+1/262144))]


private theorem assigned_log_rate :
    Real.log (19877/20000 : ℝ)+(13/32 : ℝ)*Real.log (200/197 : ℝ) ≤ -(1/35000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 123/39877)
    (by norm_num : (123/39877 : ℝ) < 1) 1
  have he : (1+(123/39877 : ℝ))/(1-123/39877) = (19877/20000 : ℝ)⁻¹ := by norm_num
  rw [he,Real.log_inv] at hlo
  norm_num [Finset.sum_range_succ] at hlo
  have hhi : Real.log (200/197 : ℝ) ≤ 151137/10000000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 151137/10000000) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  linarith

private theorem unpaid_mass_interior_le (N : ℕ) {x : ℝ} (hx : (41/100:ℝ) ≤ x) (hx1 : x ≤ 1) :
    (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x) ≤
      Real.exp (-(N:ℝ)/35000) := by
  have hx0 : 0 ≤ x := by linarith
  have ht : 0 ≤ Real.log (200/197:ℝ) := Real.log_nonneg (by norm_num)
  have hUS : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+1+1) := by
    intro k hk
    have h := unpaid_orders_submajority N k hk
    simp only [Finset.mem_range]
    omega
  have hh := selected_tilt_bound (N+1) _ hUS hx0 hx1
    (by norm_num : (0:ℝ) ≤ 197/200)
    (Real.exp_pos ((13/32:ℝ)*N*Real.log (200/197:ℝ))).le ?_
  · have hb : ((197/200:ℝ)*x+(1-x))^(N+1) ≤ (19877/20000:ℝ)^(N+1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have he : Real.exp ((13/32:ℝ)*N*Real.log (200/197:ℝ)) * (19877/20000:ℝ)^(N+1) =
        (19877/20000:ℝ)*Real.exp ((N:ℝ)*(Real.log (19877/20000:ℝ)+(13/32:ℝ)*Real.log (200/197:ℝ))) := by
      rw [pow_succ]
      have hp : (19877/20000:ℝ)^N = Real.exp ((N:ℝ)*Real.log (19877/20000:ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<19877/20000)]
      rw [hp]
      rw [show (N:ℝ)*(Real.log (19877/20000:ℝ)+(13/32:ℝ)*Real.log (200/197:ℝ)) =
        (13/32:ℝ)*N*Real.log (200/197:ℝ)+(N:ℝ)*Real.log (19877/20000:ℝ) by ring, Real.exp_add]
      ring
    have hrate : Real.exp ((N:ℝ)*(Real.log (19877/20000:ℝ)+(13/32:ℝ)*Real.log (200/197:ℝ))) ≤
        Real.exp (-(N:ℝ)/35000) := Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_left assigned_log_rate (Nat.cast_nonneg (α:=ℝ) N)])
    have hprod := mul_le_mul_of_nonneg_left hb
      (Real.exp_pos ((13/32:ℝ)*N*Real.log (200/197:ℝ))).le
    rw [he] at hprod
    nlinarith [Real.exp_pos (-(N:ℝ)/35000)]
  · intro k hk
    have hkcut := (ZetaRieszWingHighOrders.unpaidOrders_support hk).2.1
    have hc : (k:ℝ) ≤ (13/32:ℝ)*N := by
      have hn : 32*k ≤ 13*N := by omega
      have hnR : (32:ℝ)*k ≤ 13*N := by exact_mod_cast hn
      linarith
    have he : (197/200:ℝ) = Real.exp (-Real.log (200/197:ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<200/197)]
      norm_num
    rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc ht]

/-- If all eligible selected primes are balanced, the complete assigned fraction has an exponential saving with its exact prime-count factor. -/
private theorem share_small_of_selected_primes_interior (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n)
    (hbal : ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ (59/100:ℝ)*Real.log n) :
    allocationShare A N n ≤ (n.primeFactors.card:ℝ)*Real.exp (-(N:ℝ)/35000) := by
  rw [share_eq_binomial_sum A N hn hn1]
  calc
    _ ≤ ∑ _p ∈ n.primeFactors, Real.exp (-(N:ℝ)/35000) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hel : p ∈ A ∧ eligibleCofactor p (n/p)
      · rw [if_pos hel]
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpd := Nat.dvd_of_mem_primeFactors hp
        have hlog : Real.log (n/p:ℕ) = Real.log n-Real.log p := by
          rw [Nat.cast_div hpd (by exact_mod_cast hpp.ne_zero), Real.log_div
            (by exact_mod_cast hn.ne_zero) (by exact_mod_cast hpp.ne_zero)]
        have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
        apply unpaid_mass_interior_le
        · apply (le_div_iff₀ hln).mpr
          rw [hlog]
          linarith [hbal p hp hel.1 hel.2]
        · apply (div_le_one hln).mpr
          rw [hlog]
          linarith [Real.log_natCast_nonneg p]
      · rw [if_neg hel]
        exact (Real.exp_pos _).le
    _ = _ := by simp

/-- The existing binomial estimate pays all counts in the literal window,
using its `4N` count bound rather than the old parity-box ceiling 39. -/
private theorem norm_assigned_interior_le (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (N : ℕ) {n : ℕ} (hnW : n ∈ literalWindow N)
    (hbal : ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ (59/100 : ℝ)*Real.log n) :
    ‖assignedCoefficient A L N n‖ ≤
      (4*((N : ℝ)+1)*Real.exp (-(N : ℝ)/35000))*zetaMoebiusLogMajorant n := by
  by_cases hn : Squarefree n ∧ 1 < n ∧ ¬n.Prime
  · have hs := share_small_of_selected_primes_interior A N hn.1 hn.2.1 hbal
    have hc := card_le_four_order N hn.1 hnW
    have hshare : allocationShare A N n ≤ 4*((N : ℝ)+1)*Real.exp (-(N : ℝ)/35000) := by
      nlinarith [Real.exp_pos (-(N : ℝ)/35000)]
    rw [assignedCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (boundedShare_bounds A N n).1,boundedShare,if_pos hn]
    exact mul_le_mul hshare (SquarefreeVaughanLogSource.norm_coefficient_le hL n)
      (norm_nonneg _) (by positivity)
  · simp only [assignedCoefficient,boundedShare,if_neg hn,Complex.ofReal_zero,zero_mul,norm_zero]
    exact mul_nonneg (by positivity) (zetaMoebiusLogMajorant_nonneg n)

/-- The original assigned sum is independently paid up to 59% prime
share in the stated outer radial regions. Every retained phase and count
is unchanged; this does not apply at the central saddle. -/
theorem norm_assigned_sum_le (A D : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hD : D ⊆ literalWindow N)
    (hbal : ∀ n ∈ D, ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ (59/100 : ℝ)*Real.log n)
    (hrad : ∀ n ∈ D, Real.log n ≤ (987/500 : ℝ)*N ∨ (507/250 : ℝ)*N ≤ Real.log n)
    (y : ℝ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ D, assignedCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (4*radiusCeiling)*((N : ℝ)+1)*Real.exp (-(N : ℝ)/400000)*
        zetaMoebiusLogMajorantMass (1+1/262144) := by
  have he : Real.exp (-(1/400000 : ℝ))^N = Real.exp (-(N : ℝ)/400000) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have ha (n : ℕ) (hn : n ∈ D) :
      ‖(u : ℂ)^(N+1)*(assignedCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖ ≤
        (4*radiusCeiling)*((N : ℝ)+1)*Real.exp (-(N : ℝ)/400000)*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    have hc := norm_assigned_interior_le A hL N (hD hn) (hbal n hn)
    have hk := kernel_radial_saving N n y hu hU (by norm_num : (0 : ℝ) < 987/500)
      (by norm_num : (0 : ℝ) < 507/250) (by norm_num) (by norm_num)
      (rate_with_saving (by norm_num) assigned_lower_log_rate)
      (rate_with_saving (by norm_num) assigned_upper_log_rate) (hrad n hn)
    rw [he] at hk
    simp only [mul_one_div] at hk
    have hk' := mul_le_mul_of_nonneg_left hk
      (mul_nonneg (show (0 : ℝ) ≤ 4*((N : ℝ)+1) by positivity) (zetaMoebiusLogMajorant_nonneg n))
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
    calc
      _ ≤ u^(N+1)*((4*((N : ℝ)+1)*Real.exp (-(N : ℝ)/35000))*zetaMoebiusLogMajorant n)*
          ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by
        have h := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hc
            (norm_nonneg (zetaPrimeLogKernel N (3/2+Complex.I*y) n))) (pow_nonneg hu (N+1))
        simpa only [mul_assoc] using h
      _ ≤ _ := by
        convert hk' using 1 <;> first | rfl | ring
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ D, (4*radiusCeiling)*((N : ℝ)+1)*Real.exp (-(N : ℝ)/400000)*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (by unfold radiusCeiling; positivity)


/-- The union of the old share-only region and the new radial/share
region is paid. This retains every improvement already proved. -/
theorem norm_residual_union_le (A D : Finset ℕ) (N : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u L : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (hL0 : 0 < L)
    (hL : L ≤ (139/100 : ℝ)*N)
    (hD : ∀ n ∈ D, Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
      ∃ p ∈ n.primeFactors, p ∈ A ∧ eligibleCofactor p (n/p) ∧ Real.log p ≤ L ∧
        ((601/1000 : ℝ)*Real.log n ≤ Real.log p ∨
          (3/5 : ℝ)*Real.log n ≤ Real.log p ∧
            (Real.log n ≤ (248/125 : ℝ)*N ∨ (252/125 : ℝ)*N ≤ Real.log n))) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ D,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      2*zetaMoebiusLogMajorantMass (1+1/262144)*
        (Real.exp (-(N : ℝ)/1000000)+Real.exp (-(N : ℝ)/400000)) := by
  let P := fun n => ∃ p ∈ n.primeFactors, p ∈ A ∧ eligibleCofactor p (n/p) ∧
    Real.log p ≤ L ∧ (601/1000 : ℝ)*Real.log n ≤ Real.log p
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have ho := ZetaRieszJointDominantFloor.Refined.norm_scaled_sum_le A (D.filter P)
    N hN y hu hU hL0 hL (by
      intro n hn
      obtain ⟨hnD,hp⟩ := Finset.mem_filter.mp hn
      have h := hD n hnD
      exact ⟨h.1,h.2.1,h.2.2.1,hp⟩)
  have hb (n : ℕ) (hn : n ∈ D.filter (fun n => ¬P n)) :
      Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        (∃ p ∈ n.primeFactors, p ∈ A ∧ eligibleCofactor p (n/p) ∧
          Real.log p ≤ L ∧ (3/5 : ℝ)*Real.log n ≤ Real.log p) ∧
        (Real.log n ≤ (248/125 : ℝ)*N ∨ (252/125 : ℝ)*N ≤ Real.log n) := by
    obtain ⟨hnD,hnP⟩ := Finset.mem_filter.mp hn
    obtain ⟨hs,h1,hp,p,hpf,hpA,hel,hpL,hcase⟩ := hD n hnD
    rcases hcase with hold | ⟨hnew,hrad⟩
    · exact (hnP ⟨p,hpf,hpA,hel,hpL,hold⟩).elim
    · exact ⟨hs,h1,hp,⟨p,hpf,hpA,hel,hpL,hnew⟩,hrad⟩
  have hn := norm_residual_sum_le A (D.filter (fun n => ¬P n)) N hN y hu hU hL0 hL
    (by intro n hn; have h := hb n hn; exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩)
    (by intro n hn; exact (hb n hn).2.2.2.2)
  have hs := Finset.sum_filter_add_sum_filter_not D P f
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ _
  rw [← hs,mul_add]
  exact (norm_add_le _ _).trans (by dsimp only [f] at *; nlinarith)

/-- The actual assigned coefficient can be removed on the union of the
old 58.6% region and the radial 59% region, with a vanishing allowance. -/
theorem norm_assigned_union_le (A D : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hD : D ⊆ literalWindow N)
    (hbal : ∀ n ∈ D,
      (∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
        Real.log p ≤ (293/500 : ℝ)*Real.log n) ∨
      ((∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
        Real.log p ≤ (59/100 : ℝ)*Real.log n) ∧
        (Real.log n ≤ (987/500 : ℝ)*N ∨ (507/250 : ℝ)*N ≤ Real.log n)))
    (y : ℝ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ D,
      assignedCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (4*radiusCeiling)*((N : ℝ)+1)*
        (ZetaRieszJointAllocationFloor.Refined.allocationRate^N+Real.exp (-(N : ℝ)/400000))*
          zetaMoebiusLogMajorantMass (1+1/262144) := by
  let P := fun n => ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
    Real.log p ≤ (293/500 : ℝ)*Real.log n
  let f := fun n => assignedCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have ho := ZetaRieszJointAllocationFloor.Refined.norm_scaled_assigned_sum_le
    A (D.filter P) hL N (Finset.Subset.trans (Finset.filter_subset _ _) hD)
      (by intro n hn; exact (Finset.mem_filter.mp hn).2) y hu hU
  have hb (n : ℕ) (hn : n ∈ D.filter (fun n => ¬P n)) :
      (∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
        Real.log p ≤ (59/100 : ℝ)*Real.log n) ∧
        (Real.log n ≤ (987/500 : ℝ)*N ∨ (507/250 : ℝ)*N ≤ Real.log n) := by
    obtain ⟨hnD,hnP⟩ := Finset.mem_filter.mp hn
    exact (hbal n hnD).resolve_left hnP
  have hn := norm_assigned_sum_le A (D.filter (fun n => ¬P n)) hL N
    (Finset.Subset.trans (Finset.filter_subset _ _) hD)
    (by intro n hn; exact (hb n hn).1) (by intro n hn; exact (hb n hn).2) y hu hU
  have hs := Finset.sum_filter_add_sum_filter_not D P f
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ _
  rw [← hs,mul_add]
  exact (norm_add_le _ _).trans (by dsimp only [f] at *; nlinarith)

/-- A signed comparison for the original sum with its entire complement
retained. Only the independently bounded assigned part is charged. -/
theorem re_sum_ge_joint_unallocated (A S D : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hDS : D ⊆ S) (hD : D ⊆ literalWindow N)
    (hbal : ∀ n ∈ D,
      (∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
        Real.log p ≤ (293/500 : ℝ)*Real.log n) ∨
      ((∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
        Real.log p ≤ (59/100 : ℝ)*Real.log n) ∧
        (Real.log n ≤ (987/500 : ℝ)*N ∨ (507/250 : ℝ)*N ≤ Real.log n)))
    (y : ℝ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) :
    ((u : ℂ)^(N+1)*
      ((∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
        ∑ n ∈ S\D, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re-
      (4*radiusCeiling)*((N : ℝ)+1)*
        (ZetaRieszJointAllocationFloor.Refined.allocationRate^N+Real.exp (-(N : ℝ)/400000))*
          zetaMoebiusLogMajorantMass (1+1/262144) ≤
    ((u : ℂ)^(N+1)*∑ n ∈ S, residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hb := norm_assigned_union_le A D hL N hD hbal y hu hU
  have he : (∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      ((∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
        ∑ n ∈ S\D, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
      ∑ n ∈ D, assignedCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
    have hs := Finset.sum_sdiff (f := fun n => residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n) hDS
    have hd : (∑ n ∈ D, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
        (∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)-
          ∑ n ∈ D, assignedCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      unfold residualCoefficient assignedCoefficient
      push_cast
      ring
    rw [hd] at hs
    linear_combination -hs
  rw [he,mul_sub,Complex.sub_re]
  have hr := Complex.re_le_norm ((u : ℂ)^(N+1)*∑ n ∈ D,
    assignedCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)
  linarith

/-- One signed inequality for the whole literal core combines every old
and new paid region. The raw subband and transition complement stay in
ONE real part. Its lower bound is still open. -/
theorem re_core_ge_joint_reduced (N K : ℕ) (hN : 320 ≤ N) (y : ℝ)
    {u : ℝ} (hu : 1/2 ≤ u) (hU : u ≤ radiusCeiling) :
    let P := fun n => Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
      ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u N ∧ eligibleCofactor p (n/p) ∧
        ((601/1000 : ℝ)*Real.log n ≤ Real.log p ∨
          (3/5 : ℝ)*Real.log n ≤ Real.log p ∧
            (Real.log n ≤ (248/125 : ℝ)*N ∨ (252/125 : ℝ)*N ≤ Real.log n))
    let S := (coreBand u N K).filter (fun n => ¬P n)
    ∀ D : Finset ℕ, D ⊆ S →
      (∀ n ∈ D,
        (∀ p ∈ n.primeFactors, p ∈ intermediatePrimes u N → eligibleCofactor p (n/p) →
          Real.log p ≤ (293/500 : ℝ)*Real.log n) ∨
        ((∀ p ∈ n.primeFactors, p ∈ intermediatePrimes u N → eligibleCofactor p (n/p) →
          Real.log p ≤ (59/100 : ℝ)*Real.log n) ∧
          (Real.log n ≤ (987/500 : ℝ)*N ∨ (507/250 : ℝ)*N ≤ Real.log n))) →
    ((u : ℂ)^(N+1)*
      ((∑ n ∈ D, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
        ∑ n ∈ S\D,
          residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re-
      ((4*radiusCeiling)*((N : ℝ)+1)*
          (ZetaRieszJointAllocationFloor.Refined.allocationRate^N+Real.exp (-(N : ℝ)/400000))+
        2*(Real.exp (-(N : ℝ)/1000000)+Real.exp (-(N : ℝ)/400000)))*
          zetaMoebiusLogMajorantMass (1+1/262144) ≤
      ((u : ℂ)^(N+1)*coreResponse u y N K).re := by
  intro P S D hD hbal
  have hwindow : D ⊆ literalWindow N := by
    intro n hn
    have hw := (Finset.mem_filter.mp (Finset.mem_filter.mp (hD hn)).1).2
    apply (mem_literalWindow N n).mpr
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) N]
  have hlo := re_sum_ge_joint_unallocated _ S D (SquarefreeVaughanLogSource.length_pos u N)
    N hD hwindow hbal y (by linarith : 0 ≤ u) hU
  have hL : SquarefreeVaughanLogSource.length u N ≤ (139/100 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu (by omega : 2 ≤ N)
    have hlog : 2*Real.log 2 ≤ (139/100 : ℝ) := by linarith [Real.log_two_lt_d9]
    exact h.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
  have hb := norm_residual_union_le (intermediatePrimes u N) ((coreBand u N K).filter P)
    N hN y (by linarith : 0 ≤ u) hU (SquarefreeVaughanLogSource.length_pos u N) hL (by
      intro n hnD
      obtain ⟨_,hn,hn1,hnp,p,hp,hpA,hel,hdom⟩ := Finset.mem_filter.mp hnD
      refine ⟨hn,hn1,hnp,p,hp,hpA,hel,?_,hdom⟩
      have hp' := (mem_intermediatePrimes u N p).mp hpA
      exact (Real.log_lt_log (by exact_mod_cast hp'.1.pos) (by exact_mod_cast hp'.2.2)).le)
  let f := fun n => residualCoefficient (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hs := Finset.sum_filter_add_sum_filter_not (coreBand u N K) P f
  change (∑ n ∈ (coreBand u N K).filter P, f n)+
    (∑ n ∈ S, f n) = coreResponse u y N K at hs
  have he := congrArg (fun z : ℂ => ((u : ℂ)^(N+1)*z).re) hs
  rw [mul_add,Complex.add_re] at he
  have hr := (abs_le.mp (Complex.abs_re_le_norm
    ((u : ℂ)^(N+1)*∑ n ∈ (coreBand u N K).filter P, f n))).1
  dsimp only [f] at hr he
  linarith

/-- On the original cofinal schedule, every prime of every nonzero
remaining outer-radial atom is below 60% share. Eligibility follows from
the literal support; it is not an extra arithmetic assumption. -/
theorem remaining_prime_log_lt_radial (j : ℕ) (hj : 32 ≤ j) (u : ℝ) {n : ℕ}
    (hnB : n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter (fun n =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u (dyadicMomentOrder j) ∧
          eligibleCofactor p (n/p) ∧ ((601/1000 : ℝ)*Real.log n ≤ Real.log p ∨
            (3/5 : ℝ)*Real.log n ≤ Real.log p ∧
              (Real.log n ≤ (248/125 : ℝ)*dyadicMomentOrder j ∨
                (252/125 : ℝ)*dyadicMomentOrder j ≤ Real.log n)))))
    (hrad : Real.log n ≤ (248/125 : ℝ)*dyadicMomentOrder j ∨
      (252/125 : ℝ)*dyadicMomentOrder j ≤ Real.log n)
    (hcoeff : residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n ≠ 0) :
    ∀ p ∈ n.primeFactors, Real.log p < (3/5 : ℝ)*Real.log n := by
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
  have hdom' : (3/5 : ℝ)*Real.log n ≤ Real.log p := le_of_not_gt hdom
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hn1 : 1 < n := lt_of_lt_of_le hpp.one_lt
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) hpd)
  have hpN : N^2 < p := by
    by_contra hh
    have hpN' : p ≤ N^2 := le_of_not_gt hh
    have hsmall := ZetaRieszMaskSupport.few_smooth_divisor_log_le j hj hn hpd hcK (by
      intro q hq
      have hqp : q = p := by simpa only [hpp.primeFactors,Finset.mem_singleton] using hq
      simpa only [hqp] using hpN')
    have hlo : (7/4 : ℝ)*N < Real.log n := hw.1
    change Real.log p ≤ (N : ℝ)/4 at hsmall
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hpA : p ∈ intermediatePrimes u N :=
    (mem_intermediatePrimes u N p).mpr ⟨hpp,hpN,hpX p hp⟩
  exact hnnot ⟨hn,hn1,hnp,p,hp,hpA,eligible_of_three_prime_factors hn hc3 hp,Or.inr ⟨hdom',hrad⟩⟩

/-- The extra cost of the joint radial inequalities vanishes. -/
theorem tendsto_radial_allowance :
    Tendsto (fun N : ℕ => ((4*radiusCeiling)*((N : ℝ)+1)+2)*
      Real.exp (-(N : ℝ)/400000)*zetaMoebiusLogMajorantMass (1+1/262144)) atTop (𝓝 0) := by
  have hr : 0 < Real.exp (-(1/400000 : ℝ)) := Real.exp_pos _
  have hr1 : Real.exp (-(1/400000 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hp := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 hr hr1).mul_const
    ((4*radiusCeiling)*zetaMoebiusLogMajorantMass (1+1/262144))
  have hc := (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).mul_const
    (2*zetaMoebiusLogMajorantMass (1+1/262144))
  have h := hp.add hc
  simp only [pow_one,zero_mul,add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [← Real.exp_nat_mul]
  rw [show (N : ℝ)*(-(1/400000 : ℝ)) = -(N : ℝ)/400000 by ring]
  ring

/-- The total allowance in the single signed core inequality tends to
zero. This is an error theorem, not a floor for its retained main sum. -/
theorem tendsto_joint_allowance :
    Tendsto (fun N : ℕ =>
      ((4*radiusCeiling)*((N : ℝ)+1)*
          (ZetaRieszJointAllocationFloor.Refined.allocationRate^N+Real.exp (-(N : ℝ)/400000))+
        2*(Real.exp (-(N : ℝ)/1000000)+Real.exp (-(N : ℝ)/400000)))*
          zetaMoebiusLogMajorantMass (1+1/262144)) atTop (𝓝 0) := by
  have h := ZetaRieszJointDominantFloor.Refined.tendsto_joint_allowance.add tendsto_radial_allowance
  simp only [add_zero] at h
  exact h.congr' (Eventually.of_forall fun _ => by ring)

end
end RiemannGaussian.ZetaRieszJointRadialFloor

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointFloor
import RiemannGaussian.ZetaRieszParityShareError

/-!
# A signed joint comparison without a packet count ceiling

The old allocation can be paid on every selected subband whose eligible
prime shares are at most `9/16`, and the refined tilt extends this to
`293/500`. The original logarithmic window pays the
actual prime count, so no parity box, least-share restriction, rectangle
selection or fixed count ceiling is needed. The final inequality retains
the complementary signed core verbatim. It does not bound that joint main
sum or assert the cofinal floor.
-/

namespace RiemannGaussian.ZetaRieszJointAllocationFloor
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszBalancedCompanion ZetaRieszParityOrderTail
open ZetaRieszWideOwnerAudit ZetaRieszParityPacket ZetaRieszAnnulusJoint

/-- An explicit rational upper bound for the already defined rate;
the displayed decimal is certified, not inferred from the probe. -/
theorem allocation_rate_lt : allocationBoxRate < 9991081/10000000 := by
  rw [allocationBoxRate,Real.exp_neg,mul_inv_lt_iff₀ (Real.exp_pos _)]
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/1000) 3
  norm_num [Finset.sum_range_succ,radiusCeiling] at he ⊢
  linarith

/-- The existing binomial estimate pays all counts in the literal window,
using its `4N` count bound rather than the old parity-box ceiling 39. -/
theorem norm_assigned_interior_le (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (N : ℕ) {n : ℕ} (hnW : n ∈ literalWindow N)
    (hbal : ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ (9/16 : ℝ)*Real.log n) :
    ‖assignedCoefficient A L N n‖ ≤
      (4*((N : ℝ)+1)*Real.exp (-(N : ℝ)/1000))*zetaMoebiusLogMajorant n := by
  by_cases hn : Squarefree n ∧ 1 < n ∧ ¬n.Prime
  · have hs := share_small_of_selected_primes_interior A N hn.1 hn.2.1 hbal
    have hc := card_le_four_order N hn.1 hnW
    have hshare : allocationShare A N n ≤ 4*((N : ℝ)+1)*Real.exp (-(N : ℝ)/1000) := by
      nlinarith [Real.exp_pos (-(N : ℝ)/1000)]
    rw [assignedCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (boundedShare_bounds A N n).1,boundedShare,if_pos hn]
    exact mul_le_mul hshare (SquarefreeVaughanLogSource.norm_coefficient_le hL n)
      (norm_nonneg _) (by positivity)
  · simp only [assignedCoefficient,boundedShare,if_neg hn,Complex.ofReal_zero,zero_mul,norm_zero]
    exact mul_nonneg (by positivity) (zetaMoebiusLogMajorant_nonneg n)

/-- The actual assigned sum has a geometric source-normalized bound,
uniform in height, selection, length and all retained prime counts. -/
theorem norm_scaled_assigned_sum_le (A D : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hD : D ⊆ literalWindow N)
    (hbal : ∀ n ∈ D, ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ (9/16 : ℝ)*Real.log n)
    (y : ℝ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ D, assignedCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (4*radiusCeiling)*((N : ℝ)+1)*allocationBoxRate^N*
        zetaMoebiusLogMajorantMass (1+1/262144) := by
  have ha (n : ℕ) (hn : n ∈ D) :
      ‖(u : ℂ)^(N+1)*(assignedCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖ ≤
        (4*radiusCeiling)*((N : ℝ)+1)*allocationBoxRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    have hc := norm_assigned_interior_le A hL N (hD hn) (hbal n hn)
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 131071/262144) using 1
      norm_num
    have he : Real.exp (-(N : ℝ)/1000) = Real.exp (-(1/1000 : ℝ))^N := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
    calc
      _ = (u^(N+1)*‖assignedCoefficient A L N n‖)*
          ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by ring
      _ ≤ radiusCeiling^(N+1)*
          ((4*((N : ℝ)+1)*Real.exp (-(N : ℝ)/1000))*zetaMoebiusLogMajorant n)*
            ((131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n) := by
        exact mul_le_mul
          (mul_le_mul (pow_le_pow_left₀ hu hU (N+1)) hc (norm_nonneg _)
            (by unfold radiusCeiling; positivity)) hk (norm_nonneg _)
          (mul_nonneg (by unfold radiusCeiling; positivity)
            (mul_nonneg (by positivity) (zetaMoebiusLogMajorant_nonneg n)))
      _ = _ := by rw [he,allocationBoxRate,mul_pow,mul_pow,pow_succ]; ring
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ D, (4*radiusCeiling)*((N : ℝ)+1)*allocationBoxRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) :=
      Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg allocationBoxRate_bounds.1 _))

/-- A lower bound for the entire signed sum: remove the allocated part
only on `D`, and retain its complement INSIDE the same real observation. -/
theorem re_sum_ge_joint_unallocated (A S D : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hDS : D ⊆ S) (hD : D ⊆ literalWindow N)
    (hbal : ∀ n ∈ D, ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ (9/16 : ℝ)*Real.log n)
    (y : ℝ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) :
    ((u : ℂ)^(N+1)*
      ((∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
        ∑ n ∈ S\D, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re-
      (4*radiusCeiling)*((N : ℝ)+1)*allocationBoxRate^N*zetaMoebiusLogMajorantMass (1+1/262144) ≤
    ((u : ℂ)^(N+1)*∑ n ∈ S, residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hb := norm_scaled_assigned_sum_le A D hL N hD hbal y hu hU
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

/-- The same joint inequality applies directly to the existing core.
There is no rectangle split or new definition of the main response. -/
theorem re_core_ge_joint_unallocated (D : Finset ℕ) (N K : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hD : D ⊆ coreBand u N K)
    (hbal : ∀ n ∈ D, ∀ p ∈ n.primeFactors, p ∈ intermediatePrimes u N →
      eligibleCofactor p (n/p) → Real.log p ≤ (9/16 : ℝ)*Real.log n) :
    ((u : ℂ)^(N+1)*
      ((∑ n ∈ D, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
        ∑ n ∈ coreBand u N K\D,
          residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re-
      (4*radiusCeiling)*((N : ℝ)+1)*allocationBoxRate^N*zetaMoebiusLogMajorantMass (1+1/262144) ≤
    ((u : ℂ)^(N+1)*coreResponse u y N K).re := by
  apply re_sum_ge_joint_unallocated _ _ _ (SquarefreeVaughanLogSource.length_pos u N) N hD ?_ hbal y hu hU
  intro n hn
  have hw := (Finset.mem_filter.mp (hD hn)).2
  apply (mem_literalWindow N n).mpr
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) N]

/-- The paid allowance vanishes on the original order scale. Its
constant is finite but is not asserted small at any numerical order. -/
theorem tendsto_allowance :
    Tendsto (fun N : ℕ => (4*radiusCeiling)*((N : ℝ)+1)*allocationBoxRate^N*
      zetaMoebiusLogMajorantMass (1+1/262144)) atTop (𝓝 0) := by
  have hr : 0 < allocationBoxRate := by unfold allocationBoxRate radiusCeiling; positivity
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 hr
    allocationBoxRate_bounds.2).mul_const
      ((4*radiusCeiling)*zetaMoebiusLogMajorantMass (1+1/262144))
  simp only [pow_one,zero_mul] at ht
  exact ht.congr' (Eventually.of_forall fun _ => by ring)

/-! A sharper lower-tail tilt pays removal of the same allocated part
on a larger support. No phase, label or count mask is replaced. -/
namespace Refined

private theorem allocation_log_rate :
    Real.log (49379/50000 : ℝ)+(13/32 : ℝ)*Real.log (100/97 : ℝ) ≤ -(1/8200 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 621/99379)
    (by norm_num : (621/99379 : ℝ) < 1) 1
  norm_num [Finset.sum_range_succ] at hlo
  have he : Real.log (49379/50000 : ℝ) = -Real.log (50000/49379 : ℝ) := by
    rw [show (49379/50000 : ℝ) = (50000/49379 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hhi : Real.log (100/97 : ℝ) ≤ 1523/50000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1523/50000) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  rw [he]
  linarith

/-- The exact summable-envelope rate after removing the original
allocated part up to largest eligible prime share `293/500`. -/
def allocationRate : ℝ := radiusCeiling*(131071/262144 : ℝ)⁻¹*Real.exp (-(1/8200 : ℝ))

/-- An explicit geometric saving at the original source radius. -/
theorem allocationRate_le_exp : allocationRate ≤ Real.exp (-(1/100000 : ℝ)) := by
  rw [allocationRate,Real.exp_neg,mul_inv_le_iff₀ (Real.exp_pos _),← Real.exp_add]
  have h := Real.add_one_le_exp (1/8200-1/100000 : ℝ)
  norm_num [radiusCeiling]
  norm_num at h
  linarith

/-- The concrete rate is nonnegative and strictly less than one. -/
theorem allocationRate_bounds : 0 ≤ allocationRate ∧ allocationRate < 1 := by
  constructor
  · unfold allocationRate radiusCeiling; positivity
  · exact allocationRate_le_exp.trans_lt (Real.exp_lt_one_iff.mpr (by norm_num))

/-- The original unpaid majority orders have exponentially small mass when the cofactor carries at least `207/500` of the product logarithm. -/
theorem unpaid_mass_interior_le (N : ℕ) {x : ℝ} (hx : (207/500:ℝ) ≤ x) (hx1 : x ≤ 1) :
    (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x) ≤
      Real.exp (-(N:ℝ)/8200) := by
  have hx0 : 0 ≤ x := by linarith
  have ht : 0 ≤ Real.log (100/97:ℝ) := Real.log_nonneg (by norm_num)
  have hUS : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+1+1) := by
    intro k hk
    have h := unpaid_orders_submajority N k hk
    simp only [Finset.mem_range]
    omega
  have hh := selected_tilt_bound (N+1) _ hUS hx0 hx1
    (by norm_num : (0:ℝ) ≤ 97/100)
    (Real.exp_pos ((13/32:ℝ)*N*Real.log (100/97:ℝ))).le ?_
  · have hb : ((97/100:ℝ)*x+(1-x))^(N+1) ≤ (49379/50000:ℝ)^(N+1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have he : Real.exp ((13/32:ℝ)*N*Real.log (100/97:ℝ)) * (49379/50000:ℝ)^(N+1) =
        (49379/50000:ℝ)*Real.exp ((N:ℝ)*(Real.log (49379/50000:ℝ)+(13/32:ℝ)*Real.log (100/97:ℝ))) := by
      rw [pow_succ]
      have hp : (49379/50000:ℝ)^N = Real.exp ((N:ℝ)*Real.log (49379/50000:ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<49379/50000)]
      rw [hp]
      rw [show (N:ℝ)*(Real.log (49379/50000:ℝ)+(13/32:ℝ)*Real.log (100/97:ℝ)) =
        (13/32:ℝ)*N*Real.log (100/97:ℝ)+(N:ℝ)*Real.log (49379/50000:ℝ) by ring, Real.exp_add]
      ring
    have hrate : Real.exp ((N:ℝ)*(Real.log (49379/50000:ℝ)+(13/32:ℝ)*Real.log (100/97:ℝ))) ≤
        Real.exp (-(N:ℝ)/8200) := Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_left allocation_log_rate (Nat.cast_nonneg (α:=ℝ) N)])
    have hprod := mul_le_mul_of_nonneg_left hb
      (Real.exp_pos ((13/32:ℝ)*N*Real.log (100/97:ℝ))).le
    rw [he] at hprod
    nlinarith [Real.exp_pos (-(N:ℝ)/8200)]
  · intro k hk
    have hkcut := (ZetaRieszWingHighOrders.unpaidOrders_support hk).2.1
    have hc : (k:ℝ) ≤ (13/32:ℝ)*N := by
      have hn : 32*k ≤ 13*N := by omega
      have hnR : (32:ℝ)*k ≤ 13*N := by exact_mod_cast hn
      linarith
    have he : (97/100:ℝ) = Real.exp (-Real.log (100/97:ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<100/97)]
      norm_num
    rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc ht]

/-- If all eligible selected primes are balanced, the complete assigned fraction has an exponential saving with its exact prime-count factor. -/
theorem share_small_of_selected_primes_interior (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n)
    (hbal : ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ (293/500:ℝ)*Real.log n) :
    allocationShare A N n ≤ (n.primeFactors.card:ℝ)*Real.exp (-(N:ℝ)/8200) := by
  rw [share_eq_binomial_sum A N hn hn1]
  calc
    _ ≤ ∑ _p ∈ n.primeFactors, Real.exp (-(N:ℝ)/8200) := by
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
theorem norm_assigned_interior_le (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (N : ℕ) {n : ℕ} (hnW : n ∈ literalWindow N)
    (hbal : ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ (293/500 : ℝ)*Real.log n) :
    ‖assignedCoefficient A L N n‖ ≤
      (4*((N : ℝ)+1)*Real.exp (-(N : ℝ)/8200))*zetaMoebiusLogMajorant n := by
  by_cases hn : Squarefree n ∧ 1 < n ∧ ¬n.Prime
  · have hs := share_small_of_selected_primes_interior A N hn.1 hn.2.1 hbal
    have hc := card_le_four_order N hn.1 hnW
    have hshare : allocationShare A N n ≤ 4*((N : ℝ)+1)*Real.exp (-(N : ℝ)/8200) := by
      nlinarith [Real.exp_pos (-(N : ℝ)/8200)]
    rw [assignedCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (boundedShare_bounds A N n).1,boundedShare,if_pos hn]
    exact mul_le_mul hshare (SquarefreeVaughanLogSource.norm_coefficient_le hL n)
      (norm_nonneg _) (by positivity)
  · simp only [assignedCoefficient,boundedShare,if_neg hn,Complex.ofReal_zero,zero_mul,norm_zero]
    exact mul_nonneg (by positivity) (zetaMoebiusLogMajorant_nonneg n)

/-- The actual assigned sum has a geometric source-normalized bound,
uniform in height, selection, length and all retained prime counts. -/
theorem norm_scaled_assigned_sum_le (A D : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hD : D ⊆ literalWindow N)
    (hbal : ∀ n ∈ D, ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ (293/500 : ℝ)*Real.log n)
    (y : ℝ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ D, assignedCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (4*radiusCeiling)*((N : ℝ)+1)*allocationRate^N*
        zetaMoebiusLogMajorantMass (1+1/262144) := by
  have ha (n : ℕ) (hn : n ∈ D) :
      ‖(u : ℂ)^(N+1)*(assignedCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖ ≤
        (4*radiusCeiling)*((N : ℝ)+1)*allocationRate^N*
          (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) := by
    have hc := norm_assigned_interior_le A hL N (hD hn) (hbal n hn)
    have hk : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        (131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n := by
      convert norm_zetaPrimeLogKernel_le N (3/2+Complex.I*y) n
        (by norm_num : (0 : ℝ) < 131071/262144) using 1
      norm_num
    have he : Real.exp (-(N : ℝ)/8200) = Real.exp (-(1/8200 : ℝ))^N := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
    calc
      _ = (u^(N+1)*‖assignedCoefficient A L N n‖)*
          ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := by ring
      _ ≤ radiusCeiling^(N+1)*
          ((4*((N : ℝ)+1)*Real.exp (-(N : ℝ)/8200))*zetaMoebiusLogMajorant n)*
            ((131071/262144 : ℝ)⁻¹^N*zetaPrimeExpWeight (1+1/262144) n) := by
        exact mul_le_mul
          (mul_le_mul (pow_le_pow_left₀ hu hU (N+1)) hc (norm_nonneg _)
            (by unfold radiusCeiling; positivity)) hk (norm_nonneg _)
          (mul_nonneg (by unfold radiusCeiling; positivity)
            (mul_nonneg (by positivity) (zetaMoebiusLogMajorant_nonneg n)))
      _ = _ := by rw [he,allocationRate,mul_pow,mul_pow,pow_succ]; ring
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ D, (4*radiusCeiling)*((N : ℝ)+1)*allocationRate^N*
        (zetaMoebiusLogMajorant n*zetaPrimeExpWeight (1+1/262144) n) :=
      Finset.sum_le_sum ha
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg allocationRate_bounds.1 _))

/-- A lower bound for the entire signed sum: remove the allocated part
only on `D`, and retain its complement INSIDE the same real observation. -/
theorem re_sum_ge_joint_unallocated (A S D : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hDS : D ⊆ S) (hD : D ⊆ literalWindow N)
    (hbal : ∀ n ∈ D, ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ (293/500 : ℝ)*Real.log n)
    (y : ℝ) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) :
    ((u : ℂ)^(N+1)*
      ((∑ n ∈ D, SquarefreeVaughanLogSource.coefficient L n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
        ∑ n ∈ S\D, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re-
      (4*radiusCeiling)*((N : ℝ)+1)*allocationRate^N*zetaMoebiusLogMajorantMass (1+1/262144) ≤
    ((u : ℂ)^(N+1)*∑ n ∈ S, residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hb := norm_scaled_assigned_sum_le A D hL N hD hbal y hu hU
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

/-- The same joint inequality applies directly to the existing core.
There is no rectangle split or new definition of the main response. -/
theorem re_core_ge_joint_unallocated (D : Finset ℕ) (N K : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hD : D ⊆ coreBand u N K)
    (hbal : ∀ n ∈ D, ∀ p ∈ n.primeFactors, p ∈ intermediatePrimes u N →
      eligibleCofactor p (n/p) → Real.log p ≤ (293/500 : ℝ)*Real.log n) :
    ((u : ℂ)^(N+1)*
      ((∑ n ∈ D, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
        ∑ n ∈ coreBand u N K\D,
          residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n)).re-
      (4*radiusCeiling)*((N : ℝ)+1)*allocationRate^N*zetaMoebiusLogMajorantMass (1+1/262144) ≤
    ((u : ℂ)^(N+1)*coreResponse u y N K).re := by
  apply re_sum_ge_joint_unallocated _ _ _ (SquarefreeVaughanLogSource.length_pos u N) N hD ?_ hbal y hu hU
  intro n hn
  have hw := (Finset.mem_filter.mp (hD hn)).2
  apply (mem_literalWindow N n).mpr
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) N]

/-- The paid allowance vanishes on the original order scale. Its
constant is finite but is not asserted small at any numerical order. -/
theorem tendsto_allowance :
    Tendsto (fun N : ℕ => (4*radiusCeiling)*((N : ℝ)+1)*allocationRate^N*
      zetaMoebiusLogMajorantMass (1+1/262144)) atTop (𝓝 0) := by
  have hr : 0 < allocationRate := by unfold allocationRate radiusCeiling; positivity
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 hr
    allocationRate_bounds.2).mul_const
      ((4*radiusCeiling)*zetaMoebiusLogMajorantMass (1+1/262144))
  simp only [pow_one,zero_mul] at ht
  exact ht.congr' (Eventually.of_forall fun _ => by ring)

end Refined

end
end RiemannGaussian.ZetaRieszJointAllocationFloor

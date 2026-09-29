/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszBalancedCompanion
import RiemannGaussian.ZetaRieszPrimeEndpoint
import RiemannGaussian.ZetaRieszParityWindow
import RiemannGaussian.ZetaRieszJointFloor

/-!
# A global source-scale payment for every nonowner allocation

Every prime other than the largest is balanced. Its original unpaid-order
allocation therefore has exponential decay, even when the prime selection
depends on the integer label. Summing the literal signed coefficients pays
all nonowner allocations together, uniformly in height and in every bounded
mask, with no fixed prime-count or radial-period restriction. The largest
prime allocation stays inside the signed sum; it is not asserted small.
-/

namespace RiemannGaussian.ZetaRieszNonownerAllocation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency
open ZetaRieszBalancedCompanion ZetaRieszPrimeEndpoint

/-- Every non-largest prime divisor carries at most half the product log.
This arithmetic fact does not require squarefreeness or a count ceiling. -/
theorem nonowner_log_le_half {n q : ℕ} (hq : q ∈ n.primeFactors)
    (hne : q ≠ largestPrime n) : Real.log q ≤ Real.log n / 2 := by
  have hpf : n.primeFactors.Nonempty := ⟨q,hq⟩
  have hp : largestPrime n ∈ n.primeFactors := by
    rw [largestPrime,dif_pos hpf]
    exact Finset.max'_mem _ _
  have hqp : q ≤ largestPrime n := by
    rw [largestPrime,dif_pos hpf]
    exact Finset.le_max' _ _ hq
  have hqP := Nat.prime_of_mem_primeFactors hq
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hcop : q.Coprime (largestPrime n) := hqP.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hne ((Nat.dvd_prime hpP).mp hd |>.resolve_left hqP.ne_one))
  have hdiv : q * largestPrime n ∣ n := hcop.mul_dvd_of_dvd_of_dvd
    (Nat.dvd_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hp)
  have hn0 : 0 < n := Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp hq).2.2
  have hlog := Real.log_le_log
    (show (0 : ℝ) < (q * largestPrime n : ℕ) by
      exact_mod_cast Nat.mul_pos hqP.pos hpP.pos)
    (show ((q * largestPrime n : ℕ) : ℝ) ≤ n by exact_mod_cast Nat.le_of_dvd hn0 hdiv)
  rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hqP.ne_zero)
    (by exact_mod_cast hpP.ne_zero)] at hlog
  have horder := Real.log_le_log (show (0 : ℝ) < q by exact_mod_cast hqP.pos)
    (show (q : ℝ) ≤ largestPrime n by exact_mod_cast hqp)
  linarith

/-- Split the existing assigned fraction into its unique largest-prime
incidence and all other incidences, retaining eligibility and every order. -/
theorem boundedShare_owner_split (A : Finset ℕ) (N n : ℕ) :
    boundedShare A N n = boundedShare (A ∩ {largestPrime n}) N n +
      boundedShare (A.erase (largestPrime n)) N n := by
  unfold boundedShare
  split_ifs with hn
  · unfold allocationShare
    rw [← add_div]
    congr 1
    unfold assignedAmplitude
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hpA : p ∈ A <;> by_cases hp : p = largestPrime n <;>
      by_cases he : eligibleCofactor p (n/p) <;> simp [hpA,hp,he]
  · simp

/-- The exact difference of residual coefficients is the signed nonowner
companion, not a new absolute allowance for the original coefficient. -/
theorem residual_sub_owner (A : Finset ℕ) (L : ℝ) (N n : ℕ) :
    residualCoefficient A L N n -
      residualCoefficient (A ∩ {largestPrime n}) L N n =
        -assignedCoefficient (A.erase (largestPrime n)) L N n := by
  simp only [residualCoefficient,assignedCoefficient]
  rw [boundedShare_owner_split A N n]
  push_cast
  ring

/-- Nonowner coefficients obey the previously proved balanced exponential
bound for every label in the literal window, with no prime-count cutoff. -/
theorem norm_nonowner_le (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ)
    {n : ℕ} (hn : n ∈ literalWindow N) :
    ‖assignedCoefficient (A.erase (largestPrime n)) L N n‖ ≤
      (4*((N : ℝ)+1)*Real.exp (-(N : ℝ)/64))*zetaMoebiusLogMajorant n :=
  norm_assigned_balanced_le _ hL N hn
    (fun _ hq hA _ => nonowner_log_le_half hq (Finset.mem_erase.mp hA).1)

/-- The original balanced allocation saving, retained without weakening its
exponent when passing through the summable full arithmetic moment. -/
def nonownerRate : ℝ := (503/1000 : ℝ)*(2048/1023 : ℝ)*Real.exp (-(1/64 : ℝ))

/-- A uniform rational geometric rate for the ENTIRE nonowner payment. -/
theorem nonownerRate_bounds : 0 ≤ nonownerRate ∧ nonownerRate < 124/125 := by
  constructor
  · unfold nonownerRate; positivity
  · rw [nonownerRate,Real.exp_neg,mul_inv_lt_iff₀ (Real.exp_pos _)]
    have h := Real.add_one_le_exp (1/64 : ℝ)
    linarith

/-- One global bound pays all nonowner incidences at source scale. Prime
selections may depend on the label and every bounded complex mask remains.
The bound is uniform in height; no separate payment per radial period is used. -/
theorem nonowner_sum_bound (A : ℕ → Finset ℕ) (D : Finset ℕ) (w : ℕ → ℂ)
    {L : ℝ} (hL : 0 < L) (N : ℕ) (hD : D ⊆ literalWindow N)
    (hw : ∀ n ∈ D, ‖w n‖ ≤ 1) (y : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (huU : u ≤ Real.exp (-(11/16 : ℝ))) :
    ‖(u : ℂ)^(N+1) * ∑ n ∈ D,
      w n * assignedCoefficient ((A n).erase (largestPrime n)) L N n *
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (4*((N : ℝ)+1)/3) * (nonownerRate^N *
        ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) := by
  let C : ℝ := 4*((N : ℝ)+1)*Real.exp (-(N : ℝ)/64)
  have hC : 0 < C := by dsimp [C]; positivity
  let a : ℕ → ℂ := fun n =>
    w n * assignedCoefficient ((A n).erase (largestPrime n)) L N n / (C : ℂ)
  have ha : ∀ n ∈ D, ‖a n‖ ≤ zetaMoebiusLogMajorant n := by
    intro n hn
    have hb := norm_nonowner_le (A n) hL N (hD hn)
    have hwc : ‖w n * assignedCoefficient ((A n).erase (largestPrime n)) L N n‖ ≤
        ‖assignedCoefficient ((A n).erase (largestPrime n)) L N n‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw n hn)
    rw [show a n = w n * assignedCoefficient ((A n).erase (largestPrime n)) L N n /
      (C : ℂ) from rfl,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hC]
    apply (div_le_iff₀ hC).mpr
    exact (hwc.trans hb).trans_eq (by dsimp [C]; ring)
  have hb := ZetaArithmeticLogWindow.norm_sum_moment_of_log_bound D a ha N 0 y
    (2049/2048) (1023/2048) 0 (by norm_num) (by norm_num) (fun n _ => by norm_num)
  norm_num only [Nat.add_zero,Real.exp_zero,mul_one,pow_zero,inv_div] at hb
  have hbu : ‖(u : ℂ)^(N+1)*∑ n ∈ D, a n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (503/1000 : ℝ)^(N+1)*(2048/1023 : ℝ)^N*zetaMoebiusLogMajorantMass (2049/2048) := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
    exact (mul_le_mul (pow_le_pow_left₀ hu (huU.trans radius_ceiling) _) hb
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hs : (u : ℂ)^(N+1) * (∑ n ∈ D,
      w n * assignedCoefficient ((A n).erase (largestPrime n)) L N n *
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      (C : ℂ)*((u : ℂ)^(N+1)*∑ n ∈ D,
        a n * zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [a]
    have hCc : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
    field_simp
  rw [hs,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hC]
  apply (mul_le_mul_of_nonneg_left hbu hC.le).trans_eq
  have he : Real.exp (-(N : ℝ)/64) = Real.exp (-(1/64 : ℝ))^N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  dsimp only [C,nonownerRate]
  rw [he,mul_pow,mul_pow,pow_succ]
  ring

/-- Replace all allocation incidences by the unique owner inside the exact
signed sum, with a single independent geometric error for both signed sides. -/
theorem residual_sub_owner_bound (A : ℕ → Finset ℕ) (D : Finset ℕ) (w : ℕ → ℂ)
    {L : ℝ} (hL : 0 < L) (N : ℕ) (hD : D ⊆ literalWindow N)
    (hw : ∀ n ∈ D, ‖w n‖ ≤ 1) (y : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (huU : u ≤ Real.exp (-(11/16 : ℝ))) :
    ‖(u : ℂ)^(N+1) * ∑ n ∈ D, w n *
      (residualCoefficient (A n) L N n -
        residualCoefficient (A n ∩ {largestPrime n}) L N n) *
          zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (4*((N : ℝ)+1)/3) * (nonownerRate^N *
        ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) := by
  simp_rw [residual_sub_owner,mul_neg,neg_mul,Finset.sum_neg_distrib,mul_neg,norm_neg]
  exact nonowner_sum_bound A D w hL N hD hw y hu huU

/-- Arbitrary moving masks, counts and heights preserve source-scale
decay of the entire nonowner difference. No signed owner sum is discarded. -/
theorem tendsto_residual_sub_owner (A : ℕ → ℕ → Finset ℕ) (D : ℕ → Finset ℕ)
    (w : ℕ → ℕ → ℂ) (L y : ℕ → ℝ) (hL : ∀ N, 0 < L N)
    (hD : ∀ N, D N ⊆ literalWindow N) (hw : ∀ N n, n ∈ D N → ‖w N n‖ ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) (huU : u ≤ Real.exp (-(11/16 : ℝ))) :
    Tendsto (fun N => (u : ℂ)^(N+1) * ∑ n ∈ D N, w N n *
      (residualCoefficient (A N n) (L N) N n -
        residualCoefficient (A N n ∩ {largestPrime n}) (L N) N n) *
          zetaPrimeLogKernel N (3/2+Complex.I*y N) n) atTop (𝓝 0) := by
  have hr : 0 < nonownerRate := by unfold nonownerRate; positivity
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric
    1 hr (nonownerRate_bounds.2.trans (by norm_num))).mul_const
      ((4/3 : ℝ)*((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))
  simp only [pow_one,zero_mul] at ht
  apply squeeze_zero_norm (a := fun N : ℕ => ((N : ℝ)+1)*nonownerRate^N *
    ((4/3 : ℝ)*((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))) ?_ ht
  intro N
  exact (residual_sub_owner_bound (A N) (D N) (w N) (hL N) N (hD N)
    (hw N) (y N) hu huU).trans_eq (by ring)

/-- The same payment improves BOTH sides of the whole masked signed sum.
No favorable-phase credit is separately counted or added. -/
theorem signed_owner_bounds (A : ℕ → Finset ℕ) (D : Finset ℕ) (w : ℕ → ℂ)
    {L : ℝ} (hL : 0 < L) (N : ℕ) (hD : D ⊆ literalWindow N)
    (hw : ∀ n ∈ D, ‖w n‖ ≤ 1) (y : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (huU : u ≤ Real.exp (-(11/16 : ℝ))) :
    let S := (u : ℂ)^(N+1) * ∑ n ∈ D, w n * residualCoefficient (A n) L N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n
    let O := (u : ℂ)^(N+1) * ∑ n ∈ D,
      w n * residualCoefficient (A n ∩ {largestPrime n}) L N n *
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
    let E := (4*((N : ℝ)+1)/3) * (nonownerRate^N *
      ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))
    O.re-E ≤ S.re ∧ S.re ≤ O.re+E := by
  dsimp only
  have hb := residual_sub_owner_bound A D w hL N hD hw y hu huU
  simp only [mul_sub,sub_mul,Finset.sum_sub_distrib] at hb
  have hr := abs_le.mp ((Complex.abs_re_le_norm _).trans hb)
  simp only [Complex.sub_re] at hr
  exact ⟨by linarith [hr.1],by linarith [hr.2]⟩

/-- Every literal core label lies in the larger already paid window. -/
theorem coreBand_subset_literalWindow (u : ℝ) (N K : ℕ) :
    ZetaRieszParityPacket.coreBand u N K ⊆ literalWindow N := by
  intro n hn
  have hw := (Finset.mem_filter.mp hn).2
  apply (mem_literalWindow N n).mpr
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) N,hw.1,hw.2]

/-- The complete actual core, with all its original masks and moving
height, differs negligibly from the same sum with only its owner allocation. -/
theorem tendsto_core_sub_owner (K : ℕ → ℕ) (y : ℕ → ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u : ℂ)^(N+1) *
      (ZetaRieszParityPacket.coreResponse u (y N) N (K N) -
        ∑ n ∈ ZetaRieszParityPacket.coreBand u N (K N),
          residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩
            {largestPrime n}) (SquarefreeVaughanLogSource.length u N) N n *
              zetaPrimeLogKernel N (3/2+Complex.I*y N) n)) atTop (𝓝 0) := by
  have h := tendsto_residual_sub_owner
    (fun N _ => ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (fun N => ZetaRieszParityPacket.coreBand u N (K N)) (fun _ _ => 1)
    (SquarefreeVaughanLogSource.length u) y (SquarefreeVaughanLogSource.length_pos u)
    (fun N => coreBand_subset_literalWindow u N (K N)) (by intros; simp) hu
    (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)
  simpa only [one_mul,sub_mul,Finset.sum_sub_distrib,ZetaRieszParityPacket.coreResponse]
    using h

/-- The SAME joint floor/ceiling target inherits the global owner
reduction after its already proved window and order-overflow errors.
This does not assert a floor or ceiling for the retained owner sum. -/
theorem tendsto_joint_sub_owner (y : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun j => (u : ℂ)^(dyadicMomentOrder j+1) *
      (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (dyadicMomentOrder j) (dyadicPrimeCount j) -
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
          (dyadicMomentOrder j) (dyadicPrimeCount j) +
        ZetaRieszLeastBoundary.rest u y (dyadicMomentOrder j) (dyadicPrimeCount j) -
        ∑ n ∈ ZetaRieszParityPacket.coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j),
          residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∩
            {largestPrime n}) (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
              (dyadicMomentOrder j) n * zetaPrimeLogKernel (dyadicMomentOrder j)
                (3/2+Complex.I*y) n)) atTop (𝓝 0) := by
  have hcore := (ZetaRieszJointFloor.tendsto_nondominant_sub_core hu hU y).sub
    (ZetaRieszJointFloor.tendsto_nondominant_sub_joint hu hU y)
  have herror (j : ℕ) := residual_sub_owner_bound
    (fun _ => ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
    (ZetaRieszParityPacket.coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j))
    (fun _ => 1) (SquarefreeVaughanLogSource.length_pos u (dyadicMomentOrder j))
    (dyadicMomentOrder j) (coreBand_subset_literalWindow u _ _) (by intros; simp)
    y hu (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)
  have hr : 0 < nonownerRate := by unfold nonownerRate; positivity
  have ht := ((ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric
    1 hr (nonownerRate_bounds.2.trans (by norm_num))).mul_const
      ((4/3 : ℝ)*((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))).comp
        tendsto_dyadicMomentOrder
  simp only [Function.comp_def,pow_one,zero_mul] at ht
  have hpaid := squeeze_zero_norm (fun j => (herror j).trans_eq (by ring)) ht
  have h := hcore.add hpaid
  simp only [sub_zero,add_zero] at h
  apply h.congr'
  filter_upwards [] with j
  simp only [one_mul,sub_mul,Finset.sum_sub_distrib,ZetaRieszParityPacket.coreResponse]
  ring

end
end RiemannGaussian.ZetaRieszNonownerAllocation

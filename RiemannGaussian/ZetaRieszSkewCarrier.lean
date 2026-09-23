/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSkewFactorial

/-!
# Independent decay of the literal quarter-gap skew subfamily

The original unassigned factor kills the proposed rank-two reserve. The
estimate is uniform in height, includes every original mask, and uses no
zero hypothesis or completion of either the composite or prime legs.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszWideOwnerAudit ZetaRieszPrimeEndpoint
open ZetaRieszAnnulusJoint ZetaRieszPrimeCountFrequency ZetaRieszDominantAllocation

/-- The actual old unassigned multiplier and the literal skew order mass
have a joint exponential saving, including their overlap region. -/
theorem literal_missing_skew_bound (t : ℕ) (ht : 32 ≤ t) (u : ℝ) {n q : ℕ}
    (hn : n ∈ tripleBand u (dyadicMomentOrder t) (dyadicPrimeCount t))
    (hq : q ∈ secondIncidences u (dyadicMomentOrder t) n)
    (hz : residualCoefficient (intermediatePrimes u (dyadicMomentOrder t))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder t)) (dyadicMomentOrder t) n ≠ 0) :
    (1 - boundedShare (intermediatePrimes u (dyadicMomentOrder t)) (dyadicMomentOrder t) n) *
      skewMass (dyadicMomentOrder t) (Real.log (n / largestPrime n : ℕ) / Real.log n)
        (Real.log (smallPrime n q) / Real.log (n / largestPrime n : ℕ)) ≤
          3 * Real.exp (-(dyadicMomentOrder t : ℝ) / 8100) := by
  let N := dyadicMomentOrder t
  let A := intermediatePrimes u N
  obtain ⟨_, hs, hc⟩ := Finset.mem_filter.mp hn
  obtain ⟨hln, _, _, hx, hr⟩ := second_log_data hs hc hq
  have hp := largestPrime_mem_of_three hc
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hn1 : 1 < n := hpp.one_lt.trans_le
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) (Nat.dvd_of_mem_primeFactors hp))
  have hnp : ¬n.Prime := by intro h; rw [h.primeFactors, Finset.card_singleton] at hc; omega
  have hb : 0 ≤ 1 - boundedShare A N n := by linarith [(boundedShare_bounds A N n).2]
  have hshare := single_prime_mass_le_share A N hs hn1 hp (owner_mem_intermediate t ht u hn)
    (eligible_of_three_prime_factors hs (by omega) hp)
  have hmiss : 1 - boundedShare A N n ≤
      1 - ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
        mass (N + 1) k (Real.log (n / largestPrime n : ℕ) / Real.log n) := by
    rw [boundedShare, if_pos ⟨hs, hn1, hnp⟩]
    linarith
  have hcap := skewMass_bounds N hx.1 hx.2 hr.1 hr.2
  have hhigh := highMass_bounds N hx.1 hx.2
  have hN : 320 ≤ N := by
    dsimp [N, dyadicMomentOrder]
    nlinarith [four_le_dyadicPrimeCount t]
  calc
    _ ≤ (1 - boundedShare A N n) *
        highMass N (Real.log (n / largestPrime n : ℕ) / Real.log n) :=
      mul_le_mul_of_nonneg_left hcap.2 hb
    _ ≤ (1 - ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
          mass (N + 1) k (Real.log (n / largestPrime n : ℕ) / Real.log n)) *
        highMass N (Real.log (n / largestPrime n : ℕ) / Real.log n) :=
      mul_le_mul_of_nonneg_right hmiss hhigh.1
    _ ≤ _ := missing_mul_highMass N hN (owner_share_lower t ht u hn hz) hx.2

/-- A literal skew atom is independently geometrically small after the
original source normalization, uniformly in the full complex phase. -/
theorem skewAtom_bound (t : ℕ) (ht : 32 ≤ t) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) {n q : ℕ}
    (hn : n ∈ tripleBand u (dyadicMomentOrder t) (dyadicPrimeCount t))
    (hq : q ∈ secondIncidences u (dyadicMomentOrder t) n) :
    ‖(u : ℂ) ^ (dyadicMomentOrder t + 1) * skewAtom u y (dyadicMomentOrder t) n q‖ ≤
      (3 * radiusCeiling) * skewRate ^ dyadicMomentOrder t *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (1 + 1 / 262144) n) := by
  let N := dyadicMomentOrder t
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let w := skewMass N (Real.log (n / largestPrime n : ℕ) / Real.log n)
    (Real.log (smallPrime n q) / Real.log (n / largestPrime n : ℕ))
  have hR : 0 ≤ (3 * radiusCeiling) * skewRate ^ N *
      (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (1 + 1 / 262144) n) :=
    mul_nonneg (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg skewRate_bounds.1 _))
      (mul_nonneg (zetaMoebiusLogMajorant_nonneg _) (Real.exp_pos _).le)
  by_cases hz : residualCoefficient A L N n = 0
  · change ‖(u : ℂ) ^ (N + 1) * ((w : ℂ) *
      (residualCoefficient A L N n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n))‖ ≤ _
    simpa only [hz, zero_mul, mul_zero, norm_zero] using hR
  obtain ⟨_, hs, hc⟩ := Finset.mem_filter.mp hn
  obtain ⟨_, _, _, hx, hr⟩ := second_log_data hs hc hq
  have hw : 0 ≤ w := (skewMass_bounds N hx.1 hx.2 hr.1 hr.2).1
  have hb : 0 ≤ 1 - boundedShare A N n := by linarith [(boundedShare_bounds A N n).2]
  have hjoint := literal_missing_skew_bound t ht u hn hq hz
  have hcbd := SquarefreeVaughanLogSource.norm_coefficient_le
    (SquarefreeVaughanLogSource.length_pos u N) n
  have hk : ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      (131071 / 262144 : ℝ)⁻¹ ^ N * zetaPrimeExpWeight (1 + 1 / 262144) n := by
    convert norm_zetaPrimeLogKernel_le N (3 / 2 + Complex.I * y) n
      (by norm_num : (0 : ℝ) < 131071 / 262144) using 1
    norm_num
  have hpow := pow_le_pow_left₀ hu huU (N + 1)
  have he : Real.exp (-(N : ℝ) / 8100) = Real.exp (-(1 / 8100 : ℝ)) ^ N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  change ‖(u : ℂ) ^ (N + 1) * ((w : ℂ) *
    (residualCoefficient A L N n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n))‖ ≤ _
  rw [residualCoefficient]
  simp only [norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hu, Real.norm_of_nonneg hw, Real.norm_of_nonneg hb]
  calc
    _ = u ^ (N + 1) * ((1 - boundedShare A N n) * w) *
        ‖SquarefreeVaughanLogSource.coefficient L n‖ *
          ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ := by ring
    _ ≤ radiusCeiling ^ (N + 1) * (3 * Real.exp (-(N : ℝ) / 8100)) *
        zetaMoebiusLogMajorant n *
          ((131071 / 262144 : ℝ)⁻¹ ^ N * zetaPrimeExpWeight (1 + 1 / 262144) n) := by
      exact mul_le_mul (mul_le_mul (mul_le_mul hpow hjoint (mul_nonneg hb hw)
        (by unfold radiusCeiling; positivity)) hcbd (norm_nonneg _)
          (by unfold radiusCeiling; positivity)) hk (norm_nonneg _)
            (mul_nonneg (by unfold radiusCeiling; positivity) (zetaMoebiusLogMajorant_nonneg n))
    _ = _ := by rw [he, skewRate, mul_pow, mul_pow, pow_succ]; ring

/-- The complete literal quarter-gap subfamily has a fixed geometric
bound. Every arithmetic mask and its unique second incidence remain. -/
theorem skewResponse_bound (t : ℕ) (ht : 32 ≤ t) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    ‖(u : ℂ) ^ (dyadicMomentOrder t + 1) *
      skewResponse u y (dyadicMomentOrder t) (dyadicPrimeCount t)‖ ≤
        (3 * radiusCeiling) * skewRate ^ dyadicMomentOrder t *
          zetaMoebiusLogMajorantMass (1 + 1 / 262144) := by
  let N := dyadicMomentOrder t
  let K := dyadicPrimeCount t
  rw [skewResponse, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ tripleBand u N K, (3 * radiusCeiling) * skewRate ^ N *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (1 + 1 / 262144) n) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Finset.mul_sum]
      apply (norm_sum_le _ _).trans
      have h := Finset.sum_le_sum (fun q hq => skewAtom_bound t ht y hu huU hn hq)
      simp only [Finset.sum_const, nsmul_eq_mul] at h
      apply h.trans
      apply mul_le_of_le_one_left
      · exact mul_nonneg (mul_nonneg (by unfold radiusCeiling; positivity)
          (pow_nonneg skewRate_bounds.1 _)) (mul_nonneg (zetaMoebiusLogMajorant_nonneg _)
            (Real.exp_pos _).le)
      · exact_mod_cast secondIncidences_card_le_one (Finset.mem_filter.mp hn).2.1
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg skewRate_bounds.1 _))

/-- The proposed literal reserve vanishes for every moving height,
independently of any hypothetical zero or its multiplicity. -/
theorem tendsto_skewResponse (y : ℕ → ℝ) {u : ℝ} (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    Tendsto (fun t => (u : ℂ) ^ (dyadicMomentOrder t + 1) *
      skewResponse u (y t) (dyadicMomentOrder t) (dyadicPrimeCount t)) atTop (𝓝 0) := by
  have h := (((tendsto_pow_atTop_nhds_zero_of_lt_one skewRate_bounds.1 skewRate_bounds.2).const_mul
    (3 * radiusCeiling)).mul_const (zetaMoebiusLogMajorantMass (1 + 1 / 262144))).comp
      tendsto_dyadicMomentOrder
  simp only [mul_zero, zero_mul, Function.comp_def] at h
  apply squeeze_zero_norm' (a := fun t => (3 * radiusCeiling) * skewRate ^ dyadicMomentOrder t *
    zetaMoebiusLogMajorantMass (1 + 1 / 262144)) ?_ h
  filter_upwards [eventually_ge_atTop 32] with t ht
  exact skewResponse_bound t ht (y t) hu huU

/-- In particular the literal box cannot supply any fixed positive
source-scale reserve, however small the requested margin is. -/
theorem not_eventually_positive_skewResponse (y : ℕ → ℝ) {u c : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) (hc : 0 < c) :
    ¬∀ᶠ t : ℕ in atTop, c ≤ ((u : ℂ) ^ (dyadicMomentOrder t + 1) *
      skewResponse u (y t) (dyadicMomentOrder t) (dyadicPrimeCount t)).re := by
  intro h
  have ht := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_skewResponse y hu huU)
  have hh := ge_of_tendsto ht h
  norm_num only [Complex.zero_re] at hh
  linarith

/-- The conclusion is independent of which sign of the correction is
called a reserve: even its norm cannot stay above a positive constant. -/
theorem not_eventually_norm_skewResponse_ge (y : ℕ → ℝ) {u c : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) (hc : 0 < c) :
    ¬∀ᶠ t : ℕ in atTop, c ≤ ‖(u : ℂ) ^ (dyadicMomentOrder t + 1) *
      skewResponse u (y t) (dyadicMomentOrder t) (dyadicPrimeCount t)‖ := by
  intro h
  have ht := (tendsto_skewResponse y hu huU).norm
  have hh := ge_of_tendsto ht h
  simp only [norm_zero] at hh
  linarith

/-- The same finite skew atoms before splitting the old allocation.
This is not a completed prime or cofactor series. -/
def rawSkewAtom (u y : ℝ) (N n q : ℕ) : ℂ :=
  (skewMass N (Real.log (n / largestPrime n : ℕ) / Real.log n)
    (Real.log (smallPrime n q) / Real.log (n / largestPrime n : ℕ)) : ℂ) *
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n)

/-- The weight-one part of the finite skew incidence, with every other
literal mask unchanged. Nonowner completion rows have weight one. -/
def rawSkewResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ tripleBand u N K, ∑ q ∈ secondIncidences u N n, rawSkewAtom u y N n q

/-- The exact old allocated fraction of that same finite skew incidence.
It must be retained if one starts from the weight-one correction row. -/
def allocatedSkewResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ tripleBand u N K, ∑ q ∈ secondIncidences u N n,
    (boundedShare (intermediatePrimes u N) N n : ℂ) * rawSkewAtom u y N n q

/-- Exact allocation bookkeeping: the weight-one correction contains
both the old allocated part and the proposed literal unassigned reserve. -/
theorem rawSkewResponse_eq (u y : ℝ) (N K : ℕ) :
    rawSkewResponse u y N K = allocatedSkewResponse u y N K + skewResponse u y N K := by
  unfold rawSkewResponse allocatedSkewResponse skewResponse
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  unfold rawSkewAtom skewAtom residualCoefficient
  push_cast
  ring

/-- Any source present before the allocation split stays in the allocated
piece to o(1), not in the literal unassigned box. This asserts no bound
for either weight-one or allocated response separately. -/
theorem tendsto_raw_sub_allocated (y : ℕ → ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    Tendsto (fun t => (u : ℂ) ^ (dyadicMomentOrder t + 1) *
      (rawSkewResponse u (y t) (dyadicMomentOrder t) (dyadicPrimeCount t) -
        allocatedSkewResponse u (y t) (dyadicMomentOrder t) (dyadicPrimeCount t)))
      atTop (𝓝 0) := by
  simpa only [rawSkewResponse_eq, add_sub_cancel_left] using tendsto_skewResponse y hu huU

end
end RiemannGaussian.ZetaRieszSkewAllocation

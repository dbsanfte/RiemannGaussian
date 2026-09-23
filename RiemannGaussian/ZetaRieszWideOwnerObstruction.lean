/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWideCompanion
import RiemannGaussian.ZetaRieszWidePhase

/-!
# Go/no-go endpoint for the concrete wide-owner completion

The completion is not independently small: under the same exposed-zero
hypotheses it is bounded away from zero, even after the existing reserve
is returned.  All differences from the actual uniquely owned triple
carrier are retained explicitly.  This is an obstruction to discarding
the complete companion, not a zero exclusion and not an impossibility
theorem for estimating the still-masked signed difference.
-/

namespace RiemannGaussian.ZetaRieszWideOwnerAudit
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimePairConvolution ZetaRieszAnnulusJoint ZetaRieszJointAllocation
open ZetaRieszPrimeEndpoint ZetaRieszPrimeCountFrequency ZetaRieszWingReserve

/-- The literal owned companion, grouped by its unique prime, with the
old allocation multiplier and all original integer masks still present. -/
theorem ownerCompanion_eq_fibres (j : ℕ) (hj : 32 ≤ j) (u y : ℝ) :
    ownerCompanion u y (dyadicMomentOrder j) (dyadicPrimeCount j) =
      (((dyadicMomentOrder j + 1 : ℕ) : ℂ) /
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) : ℂ)) *
      ∑ k ∈ ownerOrders (dyadicMomentOrder j),
        ∑ p ∈ intermediatePrimes u (dyadicMomentOrder j),
          ∑ n ∈ (tripleBand u (dyadicMomentOrder j) (dyadicPrimeCount j)).filter
              (fun n => largestPrime n = p),
            ((1 - boundedShare (intermediatePrimes u (dyadicMomentOrder j))
              (dyadicMomentOrder j) n : ℝ) : ℂ) *
              ZetaRieszJointCofactor.compositeAtom
                (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y k
                (dyadicMomentOrder j + 1 - k) p (n / p) := by
  let N := dyadicMomentOrder j
  let S := tripleBand u N (dyadicPrimeCount j)
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  have hmap : ∀ n ∈ S, largestPrime n ∈ A := fun _ hn => owner_mem_intermediate j hj u hn
  have hf (k : ℕ) :
      (∑ p ∈ A, ∑ n ∈ S.filter (fun n => largestPrime n = p),
        ((1 - boundedShare A N n : ℝ) : ℂ) *
          ZetaRieszJointCofactor.compositeAtom L y k (N + 1 - k) p (n / p)) =
        ∑ n ∈ S, ((1 - boundedShare A N n : ℝ) : ℂ) *
          ZetaRieszJointCofactor.compositeAtom L y k (N + 1 - k) (largestPrime n) (n / largestPrime n) := by
    calc
      _ = ∑ p ∈ A, ∑ n ∈ S.filter (fun n => largestPrime n = p),
          ((1 - boundedShare A N n : ℝ) : ℂ) *
            ZetaRieszJointCofactor.compositeAtom L y k (N + 1 - k) (largestPrime n) (n / largestPrime n) := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro n hn
        rw [(Finset.mem_filter.mp hn).2]
      _ = _ := Finset.sum_fiberwise_of_maps_to hmap _
  change (∑ n ∈ S, ownerAtom A L y N n) =
    (((N + 1 : ℕ) : ℂ) / (L : ℂ)) * ∑ k ∈ ownerOrders N,
      ∑ p ∈ A, ∑ n ∈ S.filter (fun n => largestPrime n = p),
        ((1 - boundedShare A N n : ℝ) : ℂ) *
          ZetaRieszJointCofactor.compositeAtom L y k (N + 1 - k) p (n / p)
  simp_rw [hf]
  rw [Finset.sum_comm]
  simp only [ownerAtom, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The exact difference introduced by completing the unique-owner
fibres. In particular, the old allocation and owner/window masks are not
silently removed or given a vanishing-error label. -/
def ownerCompletionCorrection (u y : ℝ) (N K : ℕ) : ℂ :=
  (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
    ∑ k ∈ ownerOrders N, ∑ p ∈ intermediatePrimes u N,
      ((∑' a, ZetaRieszJointCofactor.compositeAtom
          (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k) p a) -
        ∑ n ∈ (tripleBand u N K).filter (fun n => largestPrime n = p),
          ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) *
            ZetaRieszJointCofactor.compositeAtom
              (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k) p (n / p))

/-- Completing the actual carrier retains the literal signed correction
and the independently decaying unallocated triple mass. -/
theorem triple_completed_decomposition (j : ℕ) (hj : 32 ≤ j) (u y : ℝ) :
    tripleResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j) =
      wideComplete u y (dyadicMomentOrder j) -
        ownerCompletionCorrection u y (dyadicMomentOrder j) (dyadicPrimeCount j) +
        unallocatedTriples u y (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  rw [triple_decomposition, ownerCompanion_eq_fibres j hj u y]
  unfold wideComplete ownerCompletionCorrection
  simp only [Finset.sum_sub_distrib, mul_sub]
  ring

/-- The resulting decomposition of the actual narrowed carrier. The
other prime-count classes are still signed and have not been bounded. -/
theorem narrow_completed_decomposition (j : ℕ) (hj : 32 ≤ j) (u y : ℝ) :
    ZetaRieszTypeII.narrowResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j) =
      (∑ n ∈ ZetaRieszTypeII.narrowBand u (dyadicMomentOrder j) (dyadicPrimeCount j) \
          tripleBand u (dyadicMomentOrder j) (dyadicPrimeCount j),
        residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n *
            zetaPrimeLogKernel (dyadicMomentOrder j) (3 / 2 + Complex.I * y) n) +
        wideComplete u y (dyadicMomentOrder j) -
          ownerCompletionCorrection u y (dyadicMomentOrder j) (dyadicPrimeCount j) +
          unallocatedTriples u y (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  have hs := Finset.sum_sdiff (f := fun n =>
    residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n *
        zetaPrimeLogKernel (dyadicMomentOrder j) (3 / 2 + Complex.I * y) n)
    (show tripleBand u (dyadicMomentOrder j) (dyadicPrimeCount j) ⊆
      ZetaRieszTypeII.narrowBand u (dyadicMomentOrder j) (dyadicPrimeCount j) from Finset.filter_subset _ _)
  have ht := triple_completed_decomposition j hj u y
  dsimp only [ZetaRieszTypeII.narrowResponse, tripleResponse] at *
  linear_combination -hs + ht

private theorem reserve_in_owner {N : ℕ} (hN : 2000 ≤ N) :
    reserveOrders N ⊆ ownerOrders N := by
  intro k hk
  have hki := Finset.mem_Icc.mp hk
  simp only [ownerOrders, Finset.mem_filter, Finset.mem_range]
  omega

/-- The completed band carries at least the already proved reserve. -/
theorem eventually_re_wideWing_ge (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, (15 / 544 : ℝ) * (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 ≤
      ((((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)) *
        wideWing (3 / 2 - rho.1.re) rho.1.im N).re := by
  filter_upwards [eventually_re_wide_atom rho hrho hexposed huU,
    eventually_re_reserve_ge rho hrho hexposed (huU.trans_lt radius_lt_source),
    eventually_ge_atTop 2000] with N hpos hres hN
  apply hres.trans
  simp only [reserve, wideWing, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (reserve_in_owner hN)
  intro k hk _
  exact (by positivity : 0 ≤ (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 /
    (250 * ((N + 1 : ℕ) : ℝ))).trans (hpos k hk)

/-- There is also a nonvanishing block disjoint from the old reserve.
Thus returning that reserve does not make this companion negligible. -/
theorem eventually_wideWing_sub_reserve_ge (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 2500 ≤
      ((((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)) *
        (wideWing (3 / 2 - rho.1.re) rho.1.im N -
          reserve (3 / 2 - rho.1.re) rho.1.im N)).re := by
  filter_upwards [eventually_re_wide_atom rho hrho hexposed huU,
    eventually_ge_atTop 2000] with N hpos hN
  let S := Finset.Icc (N / 2 + 1) (13 * N / 20)
  have hS : S ⊆ ownerOrders N \ reserveOrders N := by
    intro k hk
    have hki := Finset.mem_Icc.mp hk
    simp only [Finset.mem_sdiff, ownerOrders, Finset.mem_filter, Finset.mem_range,
      reserveOrders, Finset.mem_Icc]
    omega
  have hcard : ((N + 1 : ℕ) : ℝ) ≤ 10 * (S.card : ℝ) := by
    have hc : N + 1 ≤ 10 * S.card := by dsimp [S]; rw [Nat.card_Icc]; omega
    exact_mod_cast hc
  have hs := Finset.sum_sdiff (f := fun k => wingAtom (3 / 2 - rho.1.re) rho.1.im N k)
    (reserve_in_owner hN)
  have he : wideWing (3 / 2 - rho.1.re) rho.1.im N - reserve (3 / 2 - rho.1.re) rho.1.im N =
      ∑ k ∈ ownerOrders N \ reserveOrders N, wingAtom (3 / 2 - rho.1.re) rho.1.im N k := by
    dsimp only [wideWing, reserve]
    linear_combination -hs
  rw [he, Finset.mul_sum, Complex.re_sum]
  have hsum := Finset.sum_le_sum (fun k hk => hpos k (Finset.mem_sdiff.mp (hS hk)).1)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hlo : (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 2500 ≤
      (S.card : ℝ) * ((analyticZetaZeroMultiplicity rho : ℝ) ^ 2 /
        (250 * ((N + 1 : ℕ) : ℝ))) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcard (sq_nonneg (analyticZetaZeroMultiplicity rho : ℝ))]
  apply (hlo.trans hsum).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg hS
  intro k hk _
  exact (by positivity : 0 ≤ (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 /
    (250 * ((N + 1 : ℕ) : ℝ))).trans (hpos k (Finset.mem_sdiff.mp hk).1)

/-- No-go for treating the new complete companion as an independent
source-scale error: its real part stays strictly negative. -/
theorem eventually_re_wideComplete_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling) :
    ∀ᶠ N : ℕ in atTop,
      ((((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)) *
        wideComplete (3 / 2 - rho.1.re) rho.1.im N).re ≤
          -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 40 := by
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have ht := (tendsto_wide_completion rho.1.im (nontrivialZetaZero_one_lt_abs_im rho) hu huU).norm
  simp only [norm_zero] at ht
  filter_upwards [eventually_re_wideWing_ge rho hrho hexposed huU,
    ht.eventually (eventually_lt_nhds (show 0 < (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 1000 by positivity))]
    with N hwing herr
  have hre := (Complex.re_le_norm _).trans herr.le
  rw [mul_add, Complex.add_re] at hre
  nlinarith [sq_nonneg (analyticZetaZeroMultiplicity rho : ℝ)]

/-- Even adding back the previously proved reserve leaves a strictly
negative source-scale term.  This is not a fresh arithmetic saving. -/
theorem eventually_re_wideComplete_add_reserve_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling) :
    ∀ᶠ N : ℕ in atTop,
      ((((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)) *
        (wideComplete (3 / 2 - rho.1.re) rho.1.im N +
          reserve (3 / 2 - rho.1.re) rho.1.im N)).re ≤
            -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 5000 := by
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have ht := (tendsto_wide_completion rho.1.im (nontrivialZetaZero_one_lt_abs_im rho) hu huU).norm
  simp only [norm_zero] at ht
  filter_upwards [eventually_wideWing_sub_reserve_ge rho hrho hexposed huU,
    ht.eventually (eventually_lt_nhds (show 0 < (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 5000 by positivity))]
    with N hwing herr
  have hre := (Complex.re_le_norm _).trans herr.le
  rw [mul_add, Complex.add_re] at hre ⊢
  rw [mul_sub, Complex.sub_re] at hwing
  linarith

/-- The obstruction holds on the actual cofinal source schedule, not
just at isolated orders, and survives adding back the old reserve. -/
theorem not_tendsto_wideComplete_add_reserve (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling) :
    ¬Tendsto (fun j => (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (dyadicMomentOrder j + 1)) *
      (wideComplete (3 / 2 - rho.1.re) rho.1.im (dyadicMomentOrder j) +
        reserve (3 / 2 - rho.1.re) rho.1.im (dyadicMomentOrder j))) atTop (𝓝 0) := by
  intro ht
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  have hb := tendsto_dyadicMomentOrder.eventually
    (eventually_re_wideComplete_add_reserve_le rho hrho hexposed huU)
  have h := le_of_tendsto hr hb
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  norm_num only [Complex.zero_re] at h
  nlinarith [sq_pos_of_pos hm]

end
end RiemannGaussian.ZetaRieszWideOwnerAudit

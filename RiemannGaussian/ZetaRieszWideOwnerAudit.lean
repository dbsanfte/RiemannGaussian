/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCompletionRate
import RiemannGaussian.ZetaRieszPairBoundary
import RiemannGaussian.ZetaRieszAllocationConcentration
import RiemannGaussian.ZetaRieszOwnedCells

/-!
# The concrete narrow-radius, wide-owner test

The radius is at most 10001/20000. Completion uses the original exponent
with theta=27/40, ell=11/8, q=27/55 and sigma=1+1/262144.
An owner restriction is not part of that completion theorem and must not
be discarded when passing from a literal owned sum to complete moments.
-/

namespace RiemannGaussian.ZetaRieszWideOwnerAudit
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeCompletionRate ZetaRieszPrimeCompletion ZetaExposedPrimeMoments
open ZetaRieszPrimePairConvolution ZetaRieszAnnulusJoint ZetaRieszJointAllocation

/-- The concrete closed radius ceiling, without widening the requested test. -/
def radiusCeiling : ℝ := 10001 / 20000

theorem radius_lt_source : radiusCeiling < Real.exp (-(11 / 16 : ℝ)) := by
  exact (show radiusCeiling ≤ ZetaRieszTypeII.radiusCeiling by
    norm_num [radiusCeiling, ZetaRieszTypeII.radiusCeiling]).trans_lt
      ZetaRieszTypeII.radiusCeiling_lt_source_ceiling

/-- The proposed ideal tilt has a strictly negative actual completion exponent. -/
theorem completion_rate {u : ℝ} (hu : 1 / 2 ≤ u) (huU : u ≤ radiusCeiling) :
    completionExponent u (27 / 40) (11 / 8) (27 / 55) (1 + 1 / 262144) ≤
      -(1 / 25000) := by
  have hl : Real.log (radiusCeiling / (27 / 55)) ≤ (184492 / 10000000 : ℝ) := by
    apply (Real.log_le_iff_le_exp (by norm_num [radiusCeiling])).mpr
    have h := Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 184492 / 10000000) 4
    norm_num [Finset.sum_range_succ, radiusCeiling] at h ⊢
    linarith
  have hlog : Real.log (u / (27 / 55 : ℝ)) ≤ Real.log (radiusCeiling / (27 / 55)) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right huU (by norm_num))
  unfold completionExponent
  linarith

/-- Both original omitted prime ranges are paid through order 27N/40.
This is the existing general completion theorem at the concrete parameters. -/
theorem eventually_completion {u : ℝ} (hu : 1 / 2 ≤ u) (huU : u ≤ radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 3 * k → 40 * k ≤ 27 * N → ∀ y : ℝ,
      ‖(u : ℂ) ^ k * (finiteMoment (intermediatePrimes u N) k
        (3 / 2 + Complex.I * y) - ordinaryPrimeMoment k (3 / 2 + Complex.I * y))‖ ≤
        Real.exp (-(1 / 25000 : ℝ) * N) *
          ((∑' n, zetaPrimeExpWeight (1025 / 1024) n) +
            ∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n) := by
  have hue := huU.trans_lt radius_lt_source
  have h := eventually_norm_finite_sub_complete_of_rate (show 0 < u by linarith)
    (hue.trans ZetaRieszWingReserve.reserve_radius_lt_annular)
    (show (0 : ℝ) ≤ 11 / 8 by norm_num) (by norm_num; exact hue)
    (show (0 : ℝ) < 27 / 55 by norm_num) (show (27 / 55 : ℝ) ≤ u by linarith)
    (show (1 : ℝ) < 1 + 1 / 262144 by norm_num) (by norm_num)
    (completion_rate hu huU)
  filter_upwards [h] with N hN
  intro k hklo hkhi y
  have hk : (k : ℝ) ≤ (27 / 40 : ℝ) * N := by
    have hkc : 40 * (k : ℝ) ≤ 27 * N := by exact_mod_cast hkhi
    linarith
  have he : Real.exp (-(95 / 3072 : ℝ) * N) ≤ Real.exp (-(1 / 25000 : ℝ) * N) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  apply (hN k hklo hk y).trans
  rw [mul_add]
  exact add_le_add
    (mul_le_mul_of_nonneg_right he (tsum_nonneg (fun _ => (Real.exp_pos _).le))) le_rfl

/-- Exact upper-tail rate at the worst triple cofactor share, two thirds. -/
theorem upper_tail_rate :
    Real.log (40 / 39 : ℝ) - (27 / 40 : ℝ) * Real.log (27 / 26 : ℝ) ≤ -(1 / 6500) := by
  have hlo : (3774 / 100000 : ℝ) ≤ Real.log (27 / 26 : ℝ) := by
    have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 53)
      (by norm_num : (1 / 53 : ℝ) < 1) 2
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hhi : Real.log (40 / 39 : ℝ) ≤ 253179 / 10000000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 253179 / 10000000) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  linarith

/-- The lower middle-order tail also has a strict margin at share 7/20. -/
theorem lower_tail_rate :
    Real.log (193 / 200 : ℝ) + (13 / 40 : ℝ) * Real.log (10 / 9 : ℝ) ≤ -(1 / 6500) := by
  have hhi : Real.log (10 / 9 : ℝ) ≤ 106 / 1000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 106 / 1000) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hlo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 193 / 200)
  linarith

/-- The tail saving survives the original source scaling and a genuinely
summable arithmetic exponent; the positive growth log(2u) is included. -/
theorem normalized_tail_rate :
    radiusCeiling * (131071 / 262144 : ℝ)⁻¹ * Real.exp (-(1 / 6500 : ℝ)) < 1 := by
  rw [Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
  have h := Real.add_one_le_exp (1 / 6500 : ℝ)
  norm_num [radiusCeiling] at h ⊢
  linarith

/-- The concrete middle orders, retaining the total factorial order N+1. -/
def ownerOrders (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 2)).filter (fun k => 13 * N < 40 * k ∧ 40 * k ≤ 27 * N)

theorem ownerOrders_le {N k : ℕ} (hk : k ∈ ownerOrders N) : k ≤ N + 1 := by
  have h := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  omega

/-- Both literal missing binomial tails are exponentially small on the
actual possible largest-prime cofactor-share interval. -/
theorem missing_owner_mass (N : ℕ) {x : ℝ}
    (hx : (7 / 20 : ℝ) ≤ x) (hxhi : x ≤ 2 / 3) :
    1 - (∑ k ∈ ownerOrders N, mass (N + 1) k x) ≤
      2 * Real.exp (-(N : ℝ) / 6500) := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : x ≤ 1 := by linarith
  let Bh := Real.exp (-(27 / 40 : ℝ) * N * Real.log (27 / 26 : ℝ))
  let Bl := Real.exp ((13 / 40 : ℝ) * N * Real.log (10 / 9 : ℝ))
  have ht0 : 0 ≤ Real.log (27 / 26 : ℝ) := Real.log_nonneg (by norm_num)
  have hl0 : 0 ≤ Real.log (10 / 9 : ℝ) := Real.log_nonneg (by norm_num)
  have hm (k : ℕ) : 0 ≤ mass (N + 1) k x := mass_nonneg _ _ hx0 hx1
  have hU : ownerOrders N ⊆ Finset.range (N + 2) := Finset.filter_subset _ _
  have he : 1 - (∑ k ∈ ownerOrders N, mass (N + 1) k x) =
      ∑ k ∈ Finset.range (N + 2) \ ownerOrders N, mass (N + 1) k x := by
    have h := Finset.sum_sdiff (f := fun k => mass (N + 1) k x) hU
    rw [mass_total] at h
    linarith
  have hp (k : ℕ) (hk : k ∈ Finset.range (N + 2) \ ownerOrders N) :
      1 ≤ Bh * (27 / 26 : ℝ) ^ k + Bl * (9 / 10 : ℝ) ^ k := by
    obtain ⟨hkr, hkU⟩ := Finset.mem_sdiff.mp hk
    by_cases hhi : 27 * N < 40 * k
    · have hc : (27 / 40 : ℝ) * N ≤ k := by
        have h : 27 * (N : ℝ) < 40 * k := by exact_mod_cast hhi
        linarith
      have hh : 1 ≤ Bh * (27 / 26 : ℝ) ^ k := by
        dsimp only [Bh]
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 27 / 26),
          ← Real.exp_nat_mul, ← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        simp only [Real.log_exp]
        nlinarith [mul_le_mul_of_nonneg_right hc ht0]
      exact hh.trans (le_add_of_nonneg_right (by dsimp [Bl]; positivity))
    · have hlo : 40 * k ≤ 13 * N := by
        by_contra h
        exact hkU (Finset.mem_filter.mpr ⟨hkr, by omega, by omega⟩)
      have hc : (k : ℝ) ≤ (13 / 40 : ℝ) * N := by
        have h : 40 * (k : ℝ) ≤ 13 * N := by exact_mod_cast hlo
        linarith
      have hh : 1 ≤ Bl * (9 / 10 : ℝ) ^ k := by
        have he : (9 / 10 : ℝ) = Real.exp (-Real.log (10 / 9 : ℝ)) := by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]
          norm_num
        dsimp only [Bl]
        rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        nlinarith [mul_le_mul_of_nonneg_right hc hl0]
      exact hh.trans (le_add_of_nonneg_left (by dsimp [Bh]; positivity))
  have hb : 1 - (∑ k ∈ ownerOrders N, mass (N + 1) k x) ≤
      Bh * (40 / 39 : ℝ) ^ (N + 1) + Bl * (193 / 200 : ℝ) ^ (N + 1) := by
    rw [he]
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 2) \ ownerOrders N,
          (Bh * (27 / 26 : ℝ) ^ k + Bl * (9 / 10 : ℝ) ^ k) * mass (N + 1) k x :=
        Finset.sum_le_sum (fun k hk => by nlinarith [mul_le_mul_of_nonneg_right (hp k hk) (hm k)])
      _ ≤ ∑ k ∈ Finset.range (N + 2),
          (Bh * (27 / 26 : ℝ) ^ k + Bl * (9 / 10 : ℝ) ^ k) * mass (N + 1) k x :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun k _ _ => mul_nonneg (by dsimp [Bh, Bl]; positivity) (hm k))
      _ = Bh * ((27 / 26 : ℝ) * x + (1 - x)) ^ (N + 1) +
          Bl * ((9 / 10 : ℝ) * x + (1 - x)) ^ (N + 1) := by
        simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [mass_tilt, mass_tilt]
      _ ≤ _ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) (by linarith :
              (27 / 26 : ℝ) * x + (1 - x) ≤ 40 / 39) _) (Real.exp_pos _).le
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) (by linarith :
              (9 / 10 : ℝ) * x + (1 - x) ≤ 193 / 200) _) (Real.exp_pos _).le
  have hh : Bh * (40 / 39 : ℝ) ^ (N + 1) ≤
      (40 / 39 : ℝ) * Real.exp (-(N : ℝ) / 6500) := by
    have he : Bh * (40 / 39 : ℝ) ^ (N + 1) = (40 / 39 : ℝ) *
        Real.exp ((N : ℝ) * (Real.log (40 / 39 : ℝ) -
          (27 / 40 : ℝ) * Real.log (27 / 26 : ℝ))) := by
      rw [pow_succ, ← Real.exp_log (by norm_num : (0 : ℝ) < 40 / 39),
        ← Real.exp_nat_mul]
      simp only [Real.log_exp]
      dsimp only [Bh]
      rw [show (N : ℝ) * (Real.log (40 / 39 : ℝ) -
        (27 / 40 : ℝ) * Real.log (27 / 26 : ℝ)) =
          -(27 / 40 : ℝ) * N * Real.log (27 / 26 : ℝ) + N * Real.log (40 / 39 : ℝ) by ring,
        Real.exp_add]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_left upper_tail_rate (Nat.cast_nonneg (α := ℝ) N)]))
        (by norm_num)
  have hl : Bl * (193 / 200 : ℝ) ^ (N + 1) ≤
      (193 / 200 : ℝ) * Real.exp (-(N : ℝ) / 6500) := by
    have he : Bl * (193 / 200 : ℝ) ^ (N + 1) = (193 / 200 : ℝ) *
        Real.exp ((N : ℝ) * (Real.log (193 / 200 : ℝ) +
          (13 / 40 : ℝ) * Real.log (10 / 9 : ℝ))) := by
      rw [pow_succ, ← Real.exp_log (by norm_num : (0 : ℝ) < 193 / 200),
        ← Real.exp_nat_mul]
      simp only [Real.log_exp]
      dsimp only [Bl]
      rw [show (N : ℝ) * (Real.log (193 / 200 : ℝ) +
        (13 / 40 : ℝ) * Real.log (10 / 9 : ℝ)) =
          (13 / 40 : ℝ) * N * Real.log (10 / 9 : ℝ) + N * Real.log (193 / 200 : ℝ) by ring,
        Real.exp_add]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_left lower_tail_rate (Nat.cast_nonneg (α := ℝ) N)]))
        (by norm_num)
  nlinarith [Real.exp_pos (-(N : ℝ) / 6500)]

open ZetaRieszPrimeEndpoint ZetaRieszDominantAllocation ZetaRieszPrimeCountFrequency

/-- Use the existing canonical largest prime, not a new incidence average. -/
def ownerShare (N n : ℕ) : ℝ :=
  ∑ k ∈ ownerOrders N,
    mass (N + 1) k (Real.log (n / largestPrime n : ℕ) / Real.log n)

private theorem owner_log_data {n : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card = 3) :
    0 < Real.log n ∧
      Real.log (n / largestPrime n : ℕ) + Real.log (largestPrime n) = Real.log n ∧
      0 ≤ Real.log (n / largestPrime n : ℕ) / Real.log n ∧
      Real.log (n / largestPrime n : ℕ) / Real.log n ≤ 2 / 3 := by
  have hp := largestPrime_mem_of_three hc
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hn1 : 1 < n := hpp.one_lt.trans_le
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) hpd)
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have he : Real.log (n / largestPrime n : ℕ) = Real.log n - Real.log (largestPrime n) := by
    rw [Nat.cast_div hpd (by exact_mod_cast hpp.ne_zero),
      Real.log_div (by exact_mod_cast hn.ne_zero) (by exact_mod_cast hpp.ne_zero)]
  have hm : Real.log n ≤ 3 * Real.log (largestPrime n) := by
    rw [CoprimeEulerPhase.squarefree_log_eq_prime_sum hn]
    calc
      _ ≤ ∑ _p ∈ n.primeFactors, Real.log (largestPrime n) := by
        apply Finset.sum_le_sum
        intro p hp'
        have hpmax : p ≤ largestPrime n := by
          rw [largestPrime, dif_pos (show n.primeFactors.Nonempty from ⟨p, hp'⟩)]
          exact Finset.le_max' _ _ hp'
        exact Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp').pos)
          (by exact_mod_cast hpmax)
      _ = _ := by rw [Finset.sum_const, hc]; simp [nsmul_eq_mul]
  refine ⟨hln, by linarith, div_nonneg (Real.log_natCast_nonneg _) hln.le, ?_⟩
  apply (div_le_iff₀ hln).mpr
  rw [he]
  linarith

theorem ownerShare_bounds (N : ℕ) {n : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card = 3) : 0 ≤ ownerShare N n ∧ ownerShare N n ≤ 1 := by
  obtain ⟨_, _, hx, hxhi⟩ := owner_log_data hn hc
  have hx1 : Real.log (n / largestPrime n : ℕ) / Real.log n ≤ 1 := by linarith
  have hm := fun k => mass_nonneg (N + 1) k hx hx1
  refine ⟨Finset.sum_nonneg (fun k _ => hm k), ?_⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun k _ _ => hm k)).trans_eq (mass_total _ _)

/-- The literal newly assigned signed atom. The old unassigned fraction,
Riesz coefficient, cofactor coprimality and both factorial orders remain. -/
def ownerAtom (A : Finset ℕ) (L y : ℝ) (N n : ℕ) : ℂ :=
  ((1 - boundedShare A N n : ℝ) : ℂ) * (((N + 1 : ℕ) : ℂ) / (L : ℂ)) *
    ∑ k ∈ ownerOrders N,
      ZetaRieszJointCofactor.compositeAtom L y k (N + 1 - k) (largestPrime n) (n / largestPrime n)

private theorem owner_mass_atom {L : ℝ} (hL : 0 < L) (y : ℝ) (N k : ℕ)
    (hk : k ≤ N + 1) {n : ℕ} (hn : Squarefree n) (hc : n.primeFactors.card = 3) :
    (mass (N + 1) k (Real.log (n / largestPrime n : ℕ) / Real.log n) : ℂ) *
      (SquarefreeVaughanLogSource.coefficient L n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n) =
    (((N + 1 : ℕ) : ℂ) / (L : ℂ)) *
      ZetaRieszJointCofactor.compositeAtom L y k (N + 1 - k) (largestPrime n) (n / largestPrime n) := by
  have hp := largestPrime_mem_of_three hc
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hel := eligible_of_three_prime_factors hn (by omega) hp
  have he : largestPrime n * (n / largestPrime n) = n := Nat.mul_div_cancel' hpd
  obtain ⟨hln, hlogs, _, _⟩ := owner_log_data hn hc
  have hnp : ¬n.Prime := by
    intro h
    rw [h.primeFactors, Finset.card_singleton] at hc
    omega
  have hm := mass_as_factorials (N + 1) k hk
    (Real.log (n / largestPrime n : ℕ)) (Real.log (largestPrime n)) (by rw [hlogs]; exact hln.ne')
  rw [hlogs] at hm
  have hlogc : (Real.log n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hln.ne'
  have hfac : ((N + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hm, originalAtom_eq_phase hL y N hn hnp]
  unfold ZetaRieszJointCofactor.compositeAtom
  dsimp only [eligibleCofactor] at hel
  rw [if_pos hel, he]
  rw [mul_assoc (-(VaughanLogAverage.riesz L n : ℂ)),
    kernel_split_phase hpp (Nat.pos_of_ne_zero hn.ne_zero) hpd]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
  field_simp [hlogc, hfac]

/-- The new signed companion is the exact owned factorial mass, not a
renaming of the old boundedShare or a deletion of its multiplier. -/
theorem ownerAtom_eq_share (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (N : ℕ) {n : ℕ} (hn : Squarefree n) (hc : n.primeFactors.card = 3) :
    ownerAtom A L y N n = (ownerShare N n : ℂ) *
      (residualCoefficient A L N n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n) := by
  unfold ownerAtom ownerShare residualCoefficient
  simp only [Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show ((1 - boundedShare A N n : ℝ) : ℂ) * (((N + 1 : ℕ) : ℂ) / (L : ℂ)) *
      ZetaRieszJointCofactor.compositeAtom L y k (N + 1 - k) (largestPrime n) (n / largestPrime n) =
      ((1 - boundedShare A N n : ℝ) : ℂ) *
        ((((N + 1 : ℕ) : ℂ) / (L : ℂ)) *
          ZetaRieszJointCofactor.compositeAtom L y k (N + 1 - k) (largestPrime n) (n / largestPrime n)) by ring,
    ← owner_mass_atom hL y N k (ownerOrders_le hk) hn hc]
  ring

/-- All surviving squarefree triples, including the exactly-two reflected
large sector; no balanced-three-large triples are silently dropped. -/
def tripleBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (ZetaRieszTypeII.narrowBand u N K).filter (fun n => Squarefree n ∧ n.primeFactors.card = 3)

/-- The original signed residual restricted to the actual triple band. -/
def tripleResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ tripleBand u N K,
    residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
      zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n

/-- The newly assigned unique-owner mass with every original mask retained. -/
def ownerCompanion (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ tripleBand u N K,
    ownerAtom (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) y N n

/-- The remaining signed triple mass after the concrete wider allocation. -/
def unallocatedTriples (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ tripleBand u N K, ((1 - ownerShare N n : ℝ) : ℂ) *
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
      zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n)

/-- Exact decomposition of the literal triple carrier with its phase and
all original masks. Nothing here asserts decay of the assigned companion. -/
theorem triple_decomposition (u y : ℝ) (N K : ℕ) :
    tripleResponse u y N K = ownerCompanion u y N K + unallocatedTriples u y N K := by
  unfold tripleResponse ownerCompanion unallocatedTriples
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨_, hs, hc⟩ := Finset.mem_filter.mp hn
  rw [ownerAtom_eq_share _ (SquarefreeVaughanLogSource.length_pos u N) y N hs hc]
  push_cast
  ring

/-- The two tails' complete-arithmetic geometric ratio. -/
def tailRate : ℝ :=
  radiusCeiling * (131071 / 262144 : ℝ)⁻¹ * Real.exp (-(1 / 6500 : ℝ))

theorem tailRate_bounds : 0 ≤ tailRate ∧ tailRate < 1 :=
  ⟨by unfold tailRate radiusCeiling; positivity, normalized_tail_rate⟩

private theorem normalized_missing_bound (N n : ℕ) (y : ℝ) {u x : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling)
    (hx : (7 / 20 : ℝ) ≤ x) (hxhi : x ≤ 2 / 3) :
    u ^ (N + 1) * (1 - ∑ k ∈ ownerOrders N, mass (N + 1) k x) *
      ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
        (2 * radiusCeiling) * tailRate ^ N * zetaPrimeExpWeight (1 + 1 / 262144) n := by
  have hk : ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ ≤
      (131071 / 262144 : ℝ)⁻¹ ^ N * zetaPrimeExpWeight (1 + 1 / 262144) n := by
    convert norm_zetaPrimeLogKernel_le N (3 / 2 + Complex.I * y) n
      (by norm_num : (0 : ℝ) < 131071 / 262144) using 1
    norm_num
  have hpow := pow_le_pow_left₀ hu huU (N + 1)
  have he : Real.exp (-(N : ℝ) / 6500) = Real.exp (-(1 / 6500 : ℝ)) ^ N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ u ^ (N + 1) * (2 * Real.exp (-(N : ℝ) / 6500)) *
        ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (missing_owner_mass N hx hxhi) (pow_nonneg hu _)) (norm_nonneg _)
    _ ≤ radiusCeiling ^ (N + 1) * (2 * Real.exp (-(N : ℝ) / 6500)) *
        ((131071 / 262144 : ℝ)⁻¹ ^ N * zetaPrimeExpWeight (1 + 1 / 262144) n) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hpow (by positivity)) hk
        (norm_nonneg _) (by unfold radiusCeiling; positivity)
    _ = _ := by rw [he, tailRate, mul_pow, mul_pow, pow_succ]; ring

/-- On the actual nondominant support, the largest-prime owner has the
needed lower share. This uses the proved dominant-sector deletion. -/
theorem owner_share_lower (j : ℕ) (hj : 32 ≤ j) (u : ℝ) {n : ℕ}
    (hn : n ∈ tripleBand u (dyadicMomentOrder j) (dyadicPrimeCount j))
    (hz : residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n ≠ 0) :
    (7 / 20 : ℝ) ≤ Real.log (n / largestPrime n : ℕ) / Real.log n := by
  obtain ⟨hband, hs, hc⟩ := Finset.mem_filter.mp hn
  have hnd : n ∈ nondominantBand u (dyadicMomentOrder j) (dyadicPrimeCount j) :=
    (Finset.mem_filter.mp hband).1
  obtain ⟨hln, he, _, _⟩ := owner_log_data hs hc
  have hp := nondominant_prime_log_lt j hj u hnd hz _ (largestPrime_mem_of_three hc)
  apply (le_div_iff₀ hln).mpr
  linarith

/-- The canonical owner belongs to the literal finite prime family; this
is proved from the existing support, not assumed during completion. -/
theorem owner_mem_intermediate (j : ℕ) (hj : 32 ≤ j) (u : ℝ) {n : ℕ}
    (hn : n ∈ tripleBand u (dyadicMomentOrder j) (dyadicPrimeCount j)) :
    largestPrime n ∈ intermediatePrimes u (dyadicMomentOrder j) := by
  let N := dyadicMomentOrder j
  obtain ⟨hband, hs, hc⟩ := Finset.mem_filter.mp hn
  have hnd : n ∈ nondominantBand u N (dyadicPrimeCount j) := (Finset.mem_filter.mp hband).1
  have hnret := (Finset.mem_sdiff.mp hnd).1
  have hnS := (Finset.mem_sdiff.mp hnret).1
  obtain ⟨hnfew, hw⟩ := Finset.mem_filter.mp hnS
  obtain ⟨hncentral, _, hcK⟩ := Finset.mem_filter.mp hnfew
  have hpX : ∀ p ∈ n.primeFactors,
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hncentral).1).1).2
  have hp := largestPrime_mem_of_three hc
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hpN : N ^ 2 < largestPrime n := by
    by_contra hh
    have hpN' : largestPrime n ≤ N ^ 2 := le_of_not_gt hh
    have hsmall := ZetaRieszMaskSupport.few_smooth_divisor_log_le j hj hs hpd hcK (by
      intro q hq
      have hqp : q = largestPrime n := by simpa only [hpp.primeFactors, Finset.mem_singleton] using hq
      simpa only [hqp] using hpN')
    obtain ⟨hln, he, _, hx⟩ := owner_log_data hs hc
    have hm := (div_le_iff₀ hln).mp hx
    have hlo : (7 / 4 : ℝ) * N < Real.log n := hw.1
    change Real.log (largestPrime n) ≤ (N : ℝ) / 4 at hsmall
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact (mem_intermediatePrimes u N _).mpr ⟨hpp, hpN, hpX _ hp⟩

/-- Independent geometric bound for the entire newly unallocated triple
mass, with every original mask, allocation factor and phase still present. -/
theorem unallocatedTriples_bound (j : ℕ) (hj : 32 ≤ j) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    ‖(u : ℂ) ^ (dyadicMomentOrder j + 1) *
      unallocatedTriples u y (dyadicMomentOrder j) (dyadicPrimeCount j)‖ ≤
        (2 * radiusCeiling) * tailRate ^ dyadicMomentOrder j *
          zetaMoebiusLogMajorantMass (1 + 1 / 262144) := by
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := intermediatePrimes u N
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  have hatom (n : ℕ) (hn : n ∈ tripleBand u N K) :
      ‖(u : ℂ) ^ (N + 1) * (((1 - ownerShare N n : ℝ) : ℂ) *
        (residualCoefficient A L N n * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n))‖ ≤
      (2 * radiusCeiling) * tailRate ^ N *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (1 + 1 / 262144) n) := by
    by_cases hz : residualCoefficient A L N n = 0
    · rw [hz, zero_mul, mul_zero, mul_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (by unfold radiusCeiling; positivity)
        (pow_nonneg tailRate_bounds.1 _)) (mul_nonneg (zetaMoebiusLogMajorant_nonneg _)
          (Real.exp_pos _).le)
    obtain ⟨_, hs, hc⟩ := Finset.mem_filter.mp hn
    obtain ⟨_, _, _, hxhi⟩ := owner_log_data hs hc
    have hx := owner_share_lower j hj u hn hz
    have hb := normalized_missing_bound N n y hu huU hx hxhi
    have hβ : 0 ≤ 1 - ownerShare N n := by linarith [(ownerShare_bounds N hs hc).2]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hu, Complex.norm_real, Real.norm_of_nonneg hβ]
    calc
      _ ≤ u ^ (N + 1) * ((1 - ownerShare N n) *
          (zetaMoebiusLogMajorant n * ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (norm_residualCoefficient_le A hL N n) (norm_nonneg _)) hβ)
            (pow_nonneg hu _)
      _ = zetaMoebiusLogMajorant n * (u ^ (N + 1) *
          (1 - ownerShare N n) * ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n‖) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hb (zetaMoebiusLogMajorant_nonneg n)).trans_eq (by ring)
  change ‖(u : ℂ) ^ (N + 1) * unallocatedTriples u y N K‖ ≤ _
  rw [unallocatedTriples, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ tripleBand u N K, (2 * radiusCeiling) * tailRate ^ N *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (1 + 1 / 262144) n) :=
      Finset.sum_le_sum hatom
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (zetaMoebiusLogMajorant_nonneg n)
          (Real.exp_pos _).le) (summable_zetaMoebiusLogMajorant (by norm_num)))
        (mul_nonneg (by unfold radiusCeiling; positivity) (pow_nonneg tailRate_bounds.1 _))

/-- The allocation error vanishes uniformly for arbitrary moving heights.
This does not assert that the assigned companion itself vanishes. -/
theorem tendsto_unallocatedTriples (y : ℕ → ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    Tendsto (fun j => (u : ℂ) ^ (dyadicMomentOrder j + 1) *
      unallocatedTriples u (y j) (dyadicMomentOrder j) (dyadicPrimeCount j)) atTop (𝓝 0) := by
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one tailRate_bounds.1 tailRate_bounds.2).const_mul
    (2 * radiusCeiling)).mul_const (zetaMoebiusLogMajorantMass (1 + 1 / 262144))).comp
      tendsto_dyadicMomentOrder
  simp only [mul_zero, zero_mul, Function.comp_def] at ht
  apply squeeze_zero_norm' (a := fun j => (2 * radiusCeiling) * tailRate ^ dyadicMomentOrder j *
    zetaMoebiusLogMajorantMass (1 + 1 / 262144)) ?_ ht
  filter_upwards [eventually_ge_atTop 32] with j hj
  exact unallocatedTriples_bound j hj (y j) hu huU

end
end RiemannGaussian.ZetaRieszWideOwnerAudit

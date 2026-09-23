/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordMomentSequence

/-!
# Ford's published rank and maximal depth

This is the rank `floor(k - Delta/k + 1)` used in Ford's Lemma 3.6,
with the largest depth permitted by (3.8). The local depth is the paper's
`j - 1`. Every scalar admissibility condition is proved in the range
`k ≤ Delta ≤ k(k-1)/2`; no choice of ranks or depths is assumed.

Source: Kevin Ford, *Vinogradov's integral and bounds for the Riemann
zeta function*, Lemmas 3.5--3.6, arXiv:1910.08209v1.
-/

namespace RiemannGaussian.VinogradovFordRank
noncomputable section
open VinogradovFordScales VinogradovFordSchedule VinogradovFordGlobalStep

/-- The integer rank prescribed in the proof of Ford's Lemma 3.6. -/
def rank (k : ℕ) (delta : ℝ) : ℕ := ⌊(k : ℝ) - delta / k + 1⌋₊

/-- The exact two restrictions (3.8), with local depth `n = j - 1`. -/
def depths (k r : ℕ) (delta : ℝ) : Finset ℕ :=
  (Finset.range (k + 1)).filter fun n =>
    10 * (n + 1) ≤ 9 * r ∧ (n : ℝ) * ((n : ℝ) - 1) ≤ depthReserve k r delta

/-- The largest permitted depth, with zero as the default outside the
admissible parameter range. -/
def maximalDepth (k r : ℕ) (delta : ℝ) : ℕ := (depths k r delta).sup id

/-- The published rounding has no unproved integer-range conditions. -/
theorem rank_bounds {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    4 ≤ rank k delta ∧ rank k delta ≤ k ∧
      (k : ℝ) - delta / k < rank k delta ∧
        (rank k delta : ℝ) ≤ (k : ℝ) - delta / k + 1 := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hlo : 1 ≤ delta / k := (le_div_iff₀ hkpos).mpr (by simpa using hlower)
  have hhi : delta / k ≤ ((k : ℝ) - 1) / 2 :=
    (div_le_iff₀ hkpos).mpr (by nlinarith)
  have hx : 0 ≤ (k : ℝ) - delta / k + 1 := by linarith
  have hfloor := Nat.floor_le hx
  have hceil := Nat.lt_floor_add_one ((k : ℝ) - delta / k + 1)
  change (rank k delta : ℝ) ≤ (k : ℝ) - delta / k + 1 at hfloor
  change (k : ℝ) - delta / k + 1 < (rank k delta : ℝ) + 1 at hceil
  refine ⟨?_, ?_, by linarith, hfloor⟩
  · have hh : (4 : ℝ) ≤ rank k delta := by linarith
    exact_mod_cast hh
  · have hh : (rank k delta : ℝ) ≤ k := by linarith
    exact_mod_cast hh

/-- The selected rank exceeds half the degree; this pays the depth cap. -/
theorem half_degree_lt_rank {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    ((k : ℝ) + 1) / 2 < rank k delta := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hhi : delta / k ≤ ((k : ℝ) - 1) / 2 :=
    (div_le_iff₀ hkpos).mpr (by nlinarith)
  have hh := (rank_bounds hk hlower hupper).2.2.1
  linarith

/-- Ford's two sharp reserve bounds, including the rounding error. -/
theorem reserve_bounds {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    delta / k * (2 * k - delta / k - 1) ≤ depthReserve k (rank k delta) delta ∧
      depthReserve k (rank k delta) delta ≤ delta / k * (2 * k - delta / k + 1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ha : 1 ≤ delta / k := (le_div_iff₀ hkpos).mpr (by simpa using hlower)
  obtain ⟨_, hr, hrlo, hrhi⟩ := rank_bounds hk hlower hupper
  have hrR : (rank k delta : ℝ) ≤ k := by exact_mod_cast hr
  have he : delta / k * k = delta := div_mul_cancel₀ _ hkpos.ne'
  have hprodlo := mul_le_mul (show delta / k - 1 ≤ (k : ℝ) - rank k delta by linarith)
    (show delta / k ≤ (k : ℝ) - rank k delta + 1 by linarith)
    (by linarith : 0 ≤ delta / k) (by linarith : 0 ≤ (k : ℝ) - rank k delta)
  have hprodhi := mul_le_mul (show (k : ℝ) - rank k delta ≤ delta / k by linarith)
    (show (k : ℝ) - rank k delta + 1 ≤ delta / k + 1 by linarith)
    (by linarith : 0 ≤ (k : ℝ) - rank k delta + 1) (by linarith : 0 ≤ delta / k)
  unfold depthReserve
  constructor <;> nlinarith

/-- The entire active range has the reserve needed for a long maximal
iteration, not just a single differencing step. -/
theorem reserve_ge {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    2 * (k : ℝ) - 2 ≤ depthReserve k (rank k delta) delta := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have ha : 1 ≤ delta / k := (le_div_iff₀ hkpos).mpr (by simpa using hlower)
  have hb : delta / k ≤ ((k : ℝ) - 1) / 2 :=
    (div_le_iff₀ hkpos).mpr (by nlinarith)
  have hh := (reserve_bounds hk hlower hupper).1
  have hp := mul_nonneg (by linarith : 0 ≤ delta / k - 1)
    (by linarith : 0 ≤ 2 * (k : ℝ) - delta / k - 2)
  nlinarith

/-- The paper's stationary root-scale condition follows from its rounded
rank. It is no longer an extra hypothesis. -/
theorem root_scale {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    1 / ((k : ℝ) + 1) ≤ stationaryScale k (rank k delta) delta := by
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : 0 < k := by omega
  obtain ⟨hr4, hr, _, hrhi⟩ := rank_bounds hk hlower hupper
  have hrR : (rank k delta : ℝ) ≤ k := by exact_mod_cast hr
  have hy : 0 ≤ depthReserve k (rank k delta) delta := by
    have hh := reserve_ge hk hlower hupper
    linarith
  have hd := stationary_denominator_pos hkpos (by omega) hy
  have hrh := mul_le_mul_of_nonneg_right hrhi (show (0 : ℝ) ≤ k by positivity)
  have he : delta / k * k = delta := div_mul_cancel₀ _ (by positivity)
  have hprod : 0 ≤ ((k : ℝ) - rank k delta) * ((k : ℝ) - rank k delta + 1) :=
    mul_nonneg (by linarith) (by linarith)
  unfold stationaryScale
  apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < k + 1) hd).mpr
  unfold depthReserve
  nlinarith

/-- Every admissible candidate is at most the chosen maximal depth. -/
theorem le_maximalDepth {k r n : ℕ} {delta : ℝ} (hnk : n ≤ k)
    (hcap : 10 * (n + 1) ≤ 9 * r)
    (hdepth : (n : ℝ) * ((n : ℝ) - 1) ≤ depthReserve k r delta) :
    n ≤ maximalDepth k r delta := by
  apply Finset.le_sup (f := id)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcap, hdepth⟩

/-- The exact maximum itself satisfies both original depth restrictions. -/
theorem maximalDepth_spec {k r : ℕ} {delta : ℝ} (hk : 1 ≤ k) (hr : 4 ≤ r)
    (hy : 0 ≤ depthReserve k r delta) :
    1 ≤ maximalDepth k r delta ∧ maximalDepth k r delta ≤ k ∧
      10 * (maximalDepth k r delta + 1) ≤ 9 * r ∧
        (maximalDepth k r delta : ℝ) * ((maximalDepth k r delta : ℝ) - 1) ≤
          depthReserve k r delta := by
  have hmem : 1 ∈ depths k r delta := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), by omega, by simpa using hy⟩
  have hs := Finset.sup_mem_of_nonempty (f := id) ⟨1, hmem⟩
  have hm : maximalDepth k r delta ∈ depths k r delta := by simpa [maximalDepth] using hs
  obtain ⟨hin, hcap, hdepth⟩ := Finset.mem_filter.mp hm
  exact ⟨Finset.le_sup (f := id) hmem, by have := Finset.mem_range.mp hin; omega,
    hcap, hdepth⟩

/-- Ford's concrete rank and maximal depth discharge every scalar
restriction used by the actual all-endpoint moment step. -/
theorem admissible {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    4 ≤ rank k delta ∧ rank k delta ≤ k ∧
      1 ≤ maximalDepth k (rank k delta) delta ∧
      10 * (maximalDepth k (rank k delta) delta + 1) ≤ 9 * rank k delta ∧
      (maximalDepth k (rank k delta) delta : ℝ) *
        ((maximalDepth k (rank k delta) delta : ℝ) - 1) ≤
          depthReserve k (rank k delta) delta ∧
      1 / ((k : ℝ) + 1) ≤ stationaryScale k (rank k delta) delta := by
  obtain ⟨hr4, hr, _, _⟩ := rank_bounds hk hlower hupper
  have hy : 0 ≤ depthReserve k (rank k delta) delta := by
    have hh := reserve_ge hk hlower hupper
    have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  obtain ⟨hn1, _, hcap, hdepth⟩ := maximalDepth_spec (by omega) hr4 hy
  exact ⟨hr4, hr, hn1, hcap, hdepth, root_scale hk hlower hupper⟩

/-- Below the degree, the same published rounding selects the degree itself. -/
theorem rank_eq_degree {k : ℕ} {delta : ℝ} (hk : 0 < k)
    (hd0 : 0 < delta) (hd : delta ≤ k) : rank k delta = k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hq0 : 0 < delta / k := div_pos hd0 hkR
  have hq1 : delta / k ≤ 1 := (div_le_one hkR).mpr hd
  apply le_antisymm
  · have hf := Nat.floor_le (show 0 ≤ (k : ℝ) - delta / k + 1 by linarith)
    have hh : (rank k delta : ℝ) < (k : ℝ) + 1 := by change (rank k delta : ℝ) ≤ _ at hf; linarith
    have hn : rank k delta < k + 1 := by exact_mod_cast hh
    omega
  · exact Nat.le_floor (by linarith)

/-- The stationary root condition also holds in the last, rank-k step. -/
theorem root_scale_of_small {k : ℕ} {delta : ℝ} (hk : 0 < k)
    (hd0 : 0 < delta) (hd : delta ≤ k) :
    1 / ((k : ℝ) + 1) ≤ stationaryScale k (rank k delta) delta := by
  rw [rank_eq_degree hk hd0 hd]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold stationaryScale depthReserve
  simp only [sub_self, zero_mul, sub_zero]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < k + 1) (by positivity)).mpr
  nlinarith

/-- Scalar admissibility through the extra boundary step needed at the
top of Ford's published order range. -/
theorem admissible_to_boundary {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) - 1 ≤ delta) (hupper : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    4 ≤ rank k delta ∧ rank k delta ≤ k ∧
      1 ≤ maximalDepth k (rank k delta) delta ∧
      10 * (maximalDepth k (rank k delta) delta + 1) ≤ 9 * rank k delta ∧
      (maximalDepth k (rank k delta) delta : ℝ) *
        ((maximalDepth k (rank k delta) delta : ℝ) - 1) ≤
          depthReserve k (rank k delta) delta ∧
      1 / ((k : ℝ) + 1) ≤ stationaryScale k (rank k delta) delta := by
  by_cases hd : (k : ℝ) ≤ delta
  · exact admissible hk hd hupper
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hd0 : 0 < delta := by linarith
  have hr := rank_eq_degree (by omega : 0 < k) hd0 (by linarith)
  have hy : 0 ≤ depthReserve k (rank k delta) delta := by
    simp only [hr, depthReserve, sub_self, zero_mul, sub_zero]
    positivity
  obtain ⟨hn1, _, hcap, hdepth⟩ := maximalDepth_spec (by omega : 1 ≤ k) (by omega : 4 ≤ rank k delta) hy
  exact ⟨by omega, by omega, hn1, hcap, hdepth, root_scale_of_small (by omega) hd0 (by linarith)⟩

end
end RiemannGaussian.VinogradovFordRank

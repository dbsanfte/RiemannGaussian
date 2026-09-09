/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiBalancedCells

/-!
# Signed bounds between balanced arithmetic cutoffs

Retain every prime-power atom of a complete block and its common starting
mass. The exact potential increment is its centered logarithmic moment
minus one full block entropy cost. Balance at the two endpoints bounds the
increment in both directions by the corresponding relative entropies.

The resulting quadratic bound controls short balanced blocks without an
arithmetic cancellation hypothesis. It does not assert that such blocks
cover all large cutoffs, or bound the accumulated drops over long blocks.
-/

namespace RiemannGaussian
noncomputable section
open Filter
open scoped Topology

/-- The whole new prime-power block, centered at the unchanged starting
mass. The signed logarithmic locations are retained before summation. -/
def suzukiMassBlockCenteredWork (start count : ℕ) : ℝ :=
  ∑ j ∈ Finset.range count, suzukiPrimeWeight (start + j + 1) *
    (suzukiPrimeLocation (start + j + 1) - suzukiLegendreMassCenter start)

private theorem mass_block (start count : ℕ) :
    suzukiOldPrimeMass (start + count) - suzukiOldPrimeMass start =
      ∑ j ∈ Finset.range count, suzukiPrimeWeight (start + j + 1) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Nat.add_succ, suzukiOldPrimeMass_succ, Finset.sum_range_succ, ← ih]
    ring

private theorem moment_block (start count : ℕ) :
    screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight (start + count + 1) -
      screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight (start + 1) =
        ∑ j ∈ Finset.range count,
          suzukiPrimeWeight (start + j + 1) * suzukiPrimeLocation (start + j + 1) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [show start + (count + 1) + 1 = (start + count + 1) + 1 by omega,
      screwPrefixMoment_succ, Finset.sum_range_succ, ← ih]
    ring

/-- Exact block accounting. The entropy term uses the complete block mass,
so interactions between different new atoms have not been reset or lost. -/
theorem suzukiMassLegendrePotential_block_eq_centeredWork_sub_entropy (start count : ℕ) :
    suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start =
      suzukiMassBlockCenteredWork start count -
        2 * ((suzukiOldPrimeMass (start + count) - suzukiArchimedeanSlopeConstant) *
          Real.log ((suzukiOldPrimeMass (start + count) - suzukiArchimedeanSlopeConstant) /
            (suzukiOldPrimeMass start - suzukiArchimedeanSlopeConstant)) -
          (suzukiOldPrimeMass (start + count) - suzukiOldPrimeMass start)) := by
  have hm := suzukiFirstTailCorrectedMass_pos start
  have hn := suzukiFirstTailCorrectedMass_pos (start + count)
  have hlog :
      Real.log ((suzukiOldPrimeMass (start + count) - suzukiArchimedeanSlopeConstant) / 2) =
        Real.log ((suzukiOldPrimeMass start - suzukiArchimedeanSlopeConstant) / 2) +
          Real.log ((suzukiOldPrimeMass (start + count) - suzukiArchimedeanSlopeConstant) /
            (suzukiOldPrimeMass start - suzukiArchimedeanSlopeConstant)) := by
    rw [Real.log_div hn.ne' (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div hm.ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_div hn.ne' hm.ne']
    ring
  unfold suzukiMassBlockCenteredWork
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← mass_block, ← moment_block]
  unfold suzukiMassLegendrePotential suzukiLegendreMassCenter
  rw [hlog]
  ring

private theorem balanced_center_bounds {count : ℕ} (hc : SuzukiMassBalancedCell count) :
    Real.log ((count + 2 : ℕ) : ℝ) ≤ suzukiLegendreMassCenter count ∧
      suzukiLegendreMassCenter count ≤ Real.log ((count + 3 : ℕ) : ℝ) := by
  have hm := suzukiFirstTailCorrectedMass_pos count
  have hl := Real.log_le_log
    (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < ((count + 2 : ℕ) : ℝ)))
    (show Real.sqrt ((count + 2 : ℕ) : ℝ) ≤
      (suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) / 2 by linarith [hc.1])
  have hu := Real.log_le_log (div_pos hm (by norm_num : (0 : ℝ) < 2))
    (show (suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) / 2 ≤
      Real.sqrt ((count + 3 : ℕ) : ℝ) by linarith [hc.2])
  rw [Real.log_sqrt (by positivity)] at hl hu
  unfold suzukiLegendreMassCenter
  constructor <;> linarith

/-- With both endpoint cells balanced, every intervening logarithmic prime
location lies between their mass centers. This bounds the complete centered
block while preserving its full mass. -/
theorem suzukiMassBlockCenteredWork_balanced_bounds {start count : ℕ}
    (hs : SuzukiMassBalancedCell start) (ht : SuzukiMassBalancedCell (start + count)) :
    0 ≤ suzukiMassBlockCenteredWork start count ∧
      suzukiMassBlockCenteredWork start count ≤
        (suzukiOldPrimeMass (start + count) - suzukiOldPrimeMass start) *
          (suzukiLegendreMassCenter (start + count) - suzukiLegendreMassCenter start) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range count) :
      suzukiLegendreMassCenter start ≤ suzukiPrimeLocation (start + j + 1) ∧
        suzukiPrimeLocation (start + j + 1) ≤ suzukiLegendreMassCenter (start + count) := by
    have hjc := Finset.mem_range.mp hj
    unfold suzukiPrimeLocation
    constructor
    · exact (balanced_center_bounds hs).2.trans
        (Real.log_le_log (by positivity) (by norm_cast; omega))
    · exact (Real.log_le_log (by positivity) (by norm_cast; omega)).trans
        (balanced_center_bounds ht).1
  constructor
  · exact Finset.sum_nonneg (fun j hj =>
      mul_nonneg (suzukiPrimeWeight_nonnegative _) (sub_nonneg.mpr (hterm j hj).1))
  · rw [mass_block, Finset.sum_mul]
    exact Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (sub_le_sub_right (hterm j hj).2 _)
        (suzukiPrimeWeight_nonnegative _))

/-- The signed potential increment lies between two explicit block
entropies. This is an independent bound for the actual prime-power block,
not a lower-bound premise or a comparison with isolated block optima. -/
theorem suzuki_balanced_potential_block_entropy_bounds {start count : ℕ}
    (hs : SuzukiMassBalancedCell start) (ht : SuzukiMassBalancedCell (start + count)) :
    let m := suzukiOldPrimeMass start - suzukiArchimedeanSlopeConstant;
    let a := suzukiOldPrimeMass (start + count) - suzukiOldPrimeMass start;
    -(2 * ((m + a) * Real.log ((m + a) / m) - a)) ≤
        suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start ∧
      suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start ≤
        2 * (a - m * Real.log ((m + a) / m)) := by
  dsimp only
  have he := suzukiMassLegendrePotential_block_eq_centeredWork_sub_entropy start count
  obtain ⟨hl, hu⟩ := suzukiMassBlockCenteredWork_balanced_bounds hs ht
  have hm := suzukiFirstTailCorrectedMass_pos start
  have hn := suzukiFirstTailCorrectedMass_pos (start + count)
  have hcent : suzukiLegendreMassCenter (start + count) - suzukiLegendreMassCenter start =
      2 * Real.log ((suzukiOldPrimeMass (start + count) - suzukiArchimedeanSlopeConstant) /
        (suzukiOldPrimeMass start - suzukiArchimedeanSlopeConstant)) := by
    unfold suzukiLegendreMassCenter
    rw [Real.log_div hn.ne' (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div hm.ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_div hn.ne' hm.ne']
    ring
  rw [hcent] at hu
  rw [show suzukiOldPrimeMass start - suzukiArchimedeanSlopeConstant +
      (suzukiOldPrimeMass (start + count) - suzukiOldPrimeMass start) =
        suzukiOldPrimeMass (start + count) - suzukiArchimedeanSlopeConstant by ring]
  constructor <;> nlinarith

private theorem entropy_costs_le {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) :
    2 * ((m + a) * Real.log ((m + a) / m) - a) ≤ 2 * a ^ 2 / m ∧
      2 * (a - m * Real.log ((m + a) / m)) ≤ 2 * a ^ 2 / m := by
  have hma : 0 < m + a := by positivity
  have hu := Real.log_le_sub_one_of_pos (div_pos hma hm)
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hma hm)
  have hq : (m + a) / m - 1 = a / m := by field_simp; ring
  have hi : 1 - ((m + a) / m)⁻¹ = a / (m + a) := by field_simp; ring
  rw [hq] at hu
  rw [hi] at hl
  constructor
  · have h := mul_le_mul_of_nonneg_left hu hma.le
    apply (le_div_iff₀ hm).mpr
    have he : (m + a) * (a / m) * m = (m + a) * a := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h hm.le]
  · have h := mul_le_mul_of_nonneg_left hl hm.le
    have he : m * (a / (m + a)) * (m + a) = m * a := by field_simp
    have hbound : 2 * (a - m * Real.log ((m + a) / m)) ≤ 2 * a ^ 2 / (m + a) := by
      apply (le_div_iff₀ hma).mpr
      nlinarith [mul_le_mul_of_nonneg_right h hma.le]
    exact hbound.trans (div_le_div_of_nonneg_left (by positivity) hm (by linarith))

/-- The entire signed change between balanced cells is quadratically small
in their actual intervening mass, including every cross interaction. -/
theorem abs_suzuki_balanced_potential_block_le_mass_square {start count : ℕ}
    (hs : SuzukiMassBalancedCell start) (ht : SuzukiMassBalancedCell (start + count)) :
    |suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start| ≤
      2 * (suzukiOldPrimeMass (start + count) - suzukiOldPrimeMass start) ^ 2 /
        (suzukiOldPrimeMass start - suzukiArchimedeanSlopeConstant) := by
  have h := suzuki_balanced_potential_block_entropy_bounds hs ht
  dsimp only at h
  have hc := entropy_costs_le (suzukiFirstTailCorrectedMass_pos start)
    (sub_nonneg.mpr (monotone_suzukiOldPrimeMass (Nat.le_add_right start count)))
  rw [abs_le]
  constructor <;> linarith [hc.1, hc.2, h.1, h.2]

/-- In physical cutoff coordinates `N = start + 2`, a balanced block of
length `count` changes the actual potential by at most
`(count + 1)^2 / (N * sqrt N)`. The rounding unit comes from the right
endpoint of the final balanced cell. No prime-distribution error is assumed. -/
theorem abs_suzuki_balanced_potential_block_le_cutoff_square {start count : ℕ}
    (hs : SuzukiMassBalancedCell start) (ht : SuzukiMassBalancedCell (start + count)) :
    |suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start| ≤
      (count + 1 : ℝ) ^ 2 /
        (((start + 2 : ℕ) : ℝ) * Real.sqrt ((start + 2 : ℕ) : ℝ)) := by
  let N : ℝ := ((start + 2 : ℕ) : ℝ)
  let R : ℝ := ((start + count + 3 : ℕ) : ℝ)
  let m := suzukiOldPrimeMass start - suzukiArchimedeanSlopeConstant
  let a := suzukiOldPrimeMass (start + count) - suzukiOldPrimeMass start
  have hN : 0 < N := by dsimp [N]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hx : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hm : 0 < m := suzukiFirstTailCorrectedMass_pos start
  have ha : 0 ≤ a := sub_nonneg.mpr
    (monotone_suzukiOldPrimeMass (Nat.le_add_right start count))
  have hml : 2 * Real.sqrt N ≤ m := hs.1
  have hmu : m + a ≤ 2 * Real.sqrt R := by
    dsimp [m, a, R]
    linarith [ht.2]
  have hRN : R - N = count + 1 := by dsimp [R, N]; push_cast; ring
  have hax : a * Real.sqrt N ≤ count + 1 := by
    have h := mul_le_mul_of_nonneg_right
      (show a ≤ 2 * (Real.sqrt R - Real.sqrt N) by linarith) hx.le
    nlinarith [Real.sq_sqrt hN.le, Real.sq_sqrt hR.le,
      sq_nonneg (Real.sqrt R - Real.sqrt N)]
  have haq : a ^ 2 * N ≤ (count + 1 : ℝ) ^ 2 := by
    have h := mul_self_le_mul_self (mul_nonneg ha hx.le) hax
    nlinarith [Real.sq_sqrt hN.le]
  refine (abs_suzuki_balanced_potential_block_le_mass_square hs ht).trans ?_
  change 2 * a ^ 2 / m ≤ (count + 1 : ℝ) ^ 2 / (N * Real.sqrt N)
  apply (div_le_div_iff₀ hm (mul_pos hN hx)).mpr
  calc
    2 * a ^ 2 * (N * Real.sqrt N) = (a ^ 2 * N) * (2 * Real.sqrt N) := by ring
    _ ≤ (count + 1 : ℝ) ^ 2 * (2 * Real.sqrt N) :=
      mul_le_mul_of_nonneg_right haq (by positivity)
    _ ≤ (count + 1 : ℝ) ^ 2 * m := mul_le_mul_of_nonneg_left hml (sq_nonneg _)

/-- Every balanced block of length at most a fixed multiple of `sqrt N`
has an explicit inverse-square-root bound for its full signed increment. -/
theorem abs_suzuki_balanced_potential_short_block_le {start count : ℕ} {K : ℝ}
    (hs : SuzukiMassBalancedCell start) (ht : SuzukiMassBalancedCell (start + count))
    (hlen : (count + 1 : ℝ) ≤ K * Real.sqrt ((start + 2 : ℕ) : ℝ)) :
    |suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start| ≤
      K ^ 2 / Real.sqrt ((start + 2 : ℕ) : ℝ) := by
  have hN : (0 : ℝ) < ((start + 2 : ℕ) : ℝ) := by positivity
  have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ count + 1) hlen
  have hbound : (count + 1 : ℝ) ^ 2 ≤ K ^ 2 * ((start + 2 : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt hN.le]
  refine (abs_suzuki_balanced_potential_block_le_cutoff_square hs ht).trans ?_
  calc
    _ ≤ (K ^ 2 * ((start + 2 : ℕ) : ℝ)) /
        (((start + 2 : ℕ) : ℝ) * Real.sqrt ((start + 2 : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by field_simp

/-- Short-block decay is uniform over all balanced endpoints and all block
lengths meeting the displayed scale. This neither selects a weight family
nor asserts the existence of enough balanced endpoints to cover the tail. -/
theorem suzuki_balanced_potential_short_blocks_uniformly_small {K ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ start : ℕ in atTop, ∀ count : ℕ,
      SuzukiMassBalancedCell start → SuzukiMassBalancedCell (start + count) →
      (count + 1 : ℝ) ≤ K * Real.sqrt ((start + 2 : ℕ) : ℝ) →
      |suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start| < ε := by
  have hN : Tendsto (fun start : ℕ => ((start + 2 : ℕ) : ℝ)) atTop atTop := by
    simp only [Nat.cast_add, Nat.cast_ofNat]
    exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun start : ℕ => K ^ 2 / Real.sqrt ((start + 2 : ℕ) : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hN)
  filter_upwards [hb.eventually (gt_mem_nhds hε)] with start hstart
  intro count hs ht hlen
  exact (abs_suzuki_balanced_potential_short_block_le hs ht hlen).trans_lt hstart

/-- The cutoff estimate retains the complete scale exponent. A block of
length at most `K*N^alpha` costs at most `K^2*N^(2*alpha-3/2)`, uniformly
over the actual balanced cells. -/
theorem abs_suzuki_balanced_potential_power_block_le {start count : ℕ} {K alpha : ℝ}
    (hs : SuzukiMassBalancedCell start) (ht : SuzukiMassBalancedCell (start + count))
    (hlen : (count + 1 : ℝ) ≤ K * ((start + 2 : ℕ) : ℝ) ^ alpha) :
    |suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start| ≤
      K ^ 2 * ((start + 2 : ℕ) : ℝ) ^ (2 * alpha - 3 / 2) := by
  let N : ℝ := ((start + 2 : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ count + 1) hlen
  have hbound : (count + 1 : ℝ) ^ 2 ≤ K ^ 2 * (N ^ alpha) ^ 2 := by nlinarith
  have he : (N ^ alpha) ^ 2 / (N * Real.sqrt N) = N ^ (2 * alpha - 3 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (N ^ alpha) 2,
      ← Real.rpow_mul hN.le, Real.rpow_sub hN]
    rw [show alpha * (2 : ℕ) = 2 * alpha by push_cast; ring]
    congr 1
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hN, Real.rpow_one]
  refine (abs_suzuki_balanced_potential_block_le_cutoff_square hs ht).trans ?_
  change (count + 1 : ℝ) ^ 2 / (N * Real.sqrt N) ≤ _
  calc
    _ ≤ K ^ 2 * (N ^ alpha) ^ 2 / (N * Real.sqrt N) :=
      div_le_div_of_nonneg_right hbound (by positivity)
    _ = K ^ 2 * N ^ (2 * alpha - 3 / 2) := by rw [mul_div_assoc, he]

/-- Every fixed power scale strictly below `N^(3/4)` has uniformly vanishing
signed variation between its balanced endpoints. Long blocks and their
accumulated contribution are not covered by this local estimate. -/
theorem suzuki_balanced_potential_power_blocks_uniformly_small {K alpha ε : ℝ}
    (halpha : alpha < 3 / 4) (hε : 0 < ε) :
    ∀ᶠ start : ℕ in atTop, ∀ count : ℕ,
      SuzukiMassBalancedCell start → SuzukiMassBalancedCell (start + count) →
      (count + 1 : ℝ) ≤ K * ((start + 2 : ℕ) : ℝ) ^ alpha →
      |suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start| < ε := by
  have hN : Tendsto (fun start : ℕ => ((start + 2 : ℕ) : ℝ)) atTop atTop := by
    simp only [Nat.cast_add, Nat.cast_ofNat]
    exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_neg_atTop (by linarith : 0 < 3 / 2 - 2 * alpha)).comp hN
  have hb : Tendsto (fun start : ℕ => K ^ 2 * ((start + 2 : ℕ) : ℝ) ^ (2 * alpha - 3 / 2))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub, mul_zero] using hp.const_mul (K ^ 2)
  filter_upwards [hb.eventually (gt_mem_nhds hε)] with start hstart
  intro count hs ht hlen
  exact (abs_suzuki_balanced_potential_power_block_le hs ht hlen).trans_lt hstart

/-- The same independent local bound reaches the original canonical gaps,
with only their already controlled inverse-five-halves comparison allowance. -/
theorem abs_suzuki_balanced_canonical_gap_block_le {start count : ℕ}
    (hs : SuzukiMassBalancedCell start) (ht : SuzukiMassBalancedCell (start + count)) :
    |suzukiFirstTailCanonicalGap (start + count) - suzukiFirstTailCanonicalGap start| ≤
      (count + 1 : ℝ) ^ 2 /
        (((start + 2 : ℕ) : ℝ) * Real.sqrt ((start + 2 : ℕ) : ℝ)) +
      (16 / 75 : ℝ) * Real.exp 5 / (start + 2 : ℝ) ^ (5 / 2 : ℝ) := by
  have hb := abs_suzuki_balanced_potential_block_le_cutoff_square hs ht
  have he := suzukiCanonicalGap_block_massLegendre_error_le start count
  have ha := abs_add_le
    ((suzukiFirstTailCanonicalGap (start + count) - suzukiFirstTailCanonicalGap start) -
      (suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start))
    (suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start)
  rw [sub_add_cancel] at ha
  linarith

/-- Uniform decay on balanced blocks below the three-quarter power scale
holds for the actual canonical gap as well as for its exact ideal potential. -/
theorem suzuki_balanced_canonical_gap_power_blocks_uniformly_small {K alpha ε : ℝ}
    (halpha : alpha < 3 / 4) (hε : 0 < ε) :
    ∀ᶠ start : ℕ in atTop, ∀ count : ℕ,
      SuzukiMassBalancedCell start → SuzukiMassBalancedCell (start + count) →
      (count + 1 : ℝ) ≤ K * ((start + 2 : ℕ) : ℝ) ^ alpha →
      |suzukiFirstTailCanonicalGap (start + count) - suzukiFirstTailCanonicalGap start| < ε := by
  filter_upwards [suzuki_balanced_potential_power_blocks_uniformly_small (K := K)
    halpha (half_pos hε), sum_suzuki_signed_cost_uniformly_small (half_pos hε)] with start hb he
  intro count hs ht hlen
  have hbound := hb count hs ht hlen
  have herr := he count
  rw [sum_suzuki_signed_cost_eq_gap_sub_massLegendre] at herr
  have ha := abs_add_le
    ((suzukiFirstTailCanonicalGap (start + count) - suzukiFirstTailCanonicalGap start) -
      (suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start))
    (suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start)
  rw [sub_add_cancel] at ha
  linarith

end
end RiemannGaussian

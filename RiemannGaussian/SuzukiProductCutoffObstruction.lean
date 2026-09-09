/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiArithmeticCancellation

/-!
# The large-product part of the original Suzuki prime interaction

A product cutoff in a Selberg convolution is not the cutoff in the actual
triangular Suzuki work. All pairs from the top dyadic band lie beyond that
product cutoff. Their retained positive interaction has square-root size,
as follows from the proved arithmetic mass asymptotic. Thus they cannot be
discarded as a logarithmic error in a proposed work bound.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The portion of the original triangular interaction whose arithmetic products
lie below the original prefix endpoint. The initial atom at `2` is included. -/
def suzukiProductCutoffInteraction (count : ℕ) : ℝ :=
  ∑ j ∈ Finset.range count,
    suzukiPrimeWeight (j + 1) / Real.sqrt (j + 3 : ℕ) *
      ∑ d ∈ Finset.range (j + 1),
        if (d + 2) * (j + 3) ≤ count + 2 then suzukiPrimeWeight d else 0

/-- The complete complementary interaction beyond that product cutoff,
with the original triangular support and later-event denominator retained. -/
def suzukiProductCutoffRemainder (count : ℕ) : ℝ :=
  ∑ j ∈ Finset.range count,
    suzukiPrimeWeight (j + 1) / Real.sqrt (j + 3 : ℕ) *
      ∑ d ∈ Finset.range (j + 1),
        if (d + 2) * (j + 3) ≤ count + 2 then 0 else suzukiPrimeWeight d

/-- Exact partition of the literal old-mass interaction at the product cutoff. -/
theorem suzukiPrimeInteraction_eq_productCutoff_add_remainder (count : ℕ) :
    (∑ j ∈ Finset.range count, suzukiPrimeWeight (j + 1) /
      Real.sqrt (j + 3 : ℕ) * suzukiOldPrimeMass j) =
    suzukiProductCutoffInteraction count + suzukiProductCutoffRemainder count := by
  unfold suzukiProductCutoffInteraction suzukiProductCutoffRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  unfold suzukiOldPrimeMass screwPrefixMass
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

/-- Both product regions occur with a negative sign in the exact bilinear work.
Dropping the complementary interaction would raise the proposed lower bound. -/
theorem suzukiBilinearWork_sum_eq_productCutoff_with_remainder (count : ℕ) :
    (∑ j ∈ Finset.range count, suzukiFirstTailBilinearWork j) =
      2 * (∑ j ∈ Finset.range count, suzukiPrimeWeight (j + 1)) +
      suzukiArchimedeanSlopeConstant *
        (∑ j ∈ Finset.range count, suzukiPrimeWeight (j + 1) / Real.sqrt (j + 3 : ℕ)) -
      (suzukiProductCutoffInteraction count + suzukiProductCutoffRemainder count) := by
  rw [← suzukiPrimeInteraction_eq_productCutoff_add_remainder]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold suzukiFirstTailBilinearWork suzukiOldPrimeMass
  ring

/-- The original signed work retains both product regions and the entire
positive convexity reserve; no cancellation between them is presumed. -/
theorem suzukiSignedWork_sum_eq_productCutoff_with_remainder_and_reserve (count : ℕ) :
    (∑ j ∈ Finset.range count, suzukiFirstTailTransportLinearWork j) =
      2 * (∑ j ∈ Finset.range count, suzukiPrimeWeight (j + 1)) +
      suzukiArchimedeanSlopeConstant *
        (∑ j ∈ Finset.range count, suzukiPrimeWeight (j + 1) / Real.sqrt (j + 3 : ℕ)) -
      (suzukiProductCutoffInteraction count + suzukiProductCutoffRemainder count) +
      ∑ j ∈ Finset.range count, suzukiFirstTailWorkConvexReserve j := by
  have h := suzuki_signed_work_block_eq_bilinear_add_reserve 0 count
  simp only [zero_add] at h
  rw [h, suzukiBilinearWork_sum_eq_productCutoff_with_remainder]

/-- The full new-atom mass in the upper dyadic band of the original event sequence. -/
def suzukiTopBandMass (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K, suzukiPrimeWeight (K + j + 1)

/-- The positive internal triangular interaction in that same band, retaining the later event's original denominator. -/
def suzukiTopBandInteraction (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K,
    suzukiPrimeWeight (K + j + 1) / Real.sqrt (K + j + 3 : ℕ) *
      ∑ i ∈ Finset.range j, suzukiPrimeWeight (K + i + 1)

private theorem mass_increment (start count : ℕ) :
    suzukiOldPrimeMass (start + count) = suzukiOldPrimeMass start +
      ∑ j ∈ Finset.range count, suzukiPrimeWeight (start + j + 1) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Nat.add_succ, suzukiOldPrimeMass_succ, ih, Finset.sum_range_succ]
    ring

/-- The upper-band mass is the difference of the two original complete prefix masses. -/
theorem suzukiTopBandMass_eq_mass_sub (K : ℕ) :
    suzukiTopBandMass K = suzukiOldPrimeMass (2 * K) - suzukiOldPrimeMass K := by
  have h := mass_increment K K
  rw [← two_mul K] at h
  unfold suzukiTopBandMass
  linarith

/-- Every product from the upper band exceeds the full prefix's arithmetic endpoint, including both rounding offsets. -/
theorem suzukiTopBand_product_gt_cutoff (K i j : ℕ) :
    2 * K + 2 < (K + i + 3) * (K + j + 3) := by
  nlinarith

/-- The entire upper-band interaction is contained in the actual product
complement. Earlier pairs, including pairs crossing the band boundary, stay
in the remainder with their nonnegative weights. -/
theorem suzukiTopBandInteraction_le_productCutoffRemainder (K : ℕ) :
    suzukiTopBandInteraction K ≤ suzukiProductCutoffRemainder (2 * K) := by
  have hnonneg (j d : ℕ) :
      0 ≤ if (d + 2) * (j + 3) ≤ 2 * K + 2 then 0 else suzukiPrimeWeight d := by
    split_ifs <;> first | exact le_rfl | exact suzukiPrimeWeight_nonnegative _
  have hcell (j : ℕ) :
      (∑ i ∈ Finset.range j, suzukiPrimeWeight (K + i + 1)) ≤
      ∑ d ∈ Finset.range (K + j + 1),
        if (d + 2) * (K + j + 3) ≤ 2 * K + 2 then 0 else suzukiPrimeWeight d := by
    rw [show K + j + 1 = (K + 1) + j by omega, Finset.sum_range_add]
    have he : (∑ i ∈ Finset.range j,
        if (K + 1 + i + 2) * (K + j + 3) ≤ 2 * K + 2 then 0 else
          suzukiPrimeWeight (K + 1 + i)) =
        ∑ i ∈ Finset.range j, suzukiPrimeWeight (K + i + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [if_neg (not_le.mpr (by
        simpa only [show K + 1 + i + 2 = K + i + 3 by omega] using
          suzukiTopBand_product_gt_cutoff K i j))]
      congr 1
      omega
    rw [he]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun d _ ↦ hnonneg (K + j) d))
  unfold suzukiProductCutoffRemainder
  rw [show Finset.range (2 * K) = Finset.range (K + K) by congr 1; omega,
    Finset.sum_range_add]
  apply le_trans _ (le_add_of_nonneg_left (Finset.sum_nonneg (fun j _ ↦
    mul_nonneg (div_nonneg (suzukiPrimeWeight_nonnegative _) (Real.sqrt_nonneg _))
      (Finset.sum_nonneg (fun d _ ↦ hnonneg j d)))))
  exact Finset.sum_le_sum (fun j _ ↦ mul_le_mul_of_nonneg_left (hcell j)
    (div_nonneg (suzukiPrimeWeight_nonnegative _) (Real.sqrt_nonneg _)))

/-- The top-band term is part of the literal old-mass interaction; the old mass at the band boundary remains as a separate exact cross term. -/
theorem suzukiTopBandInteraction_eq_original_sub_boundary (K : ℕ) :
    (∑ j ∈ Finset.range K, suzukiPrimeWeight (K + j + 1) /
      Real.sqrt (K + j + 3 : ℕ) * suzukiOldPrimeMass (K + j)) =
    suzukiOldPrimeMass K *
      (∑ j ∈ Finset.range K, suzukiPrimeWeight (K + j + 1) / Real.sqrt (K + j + 3 : ℕ)) +
      suzukiTopBandInteraction K := by
  unfold suzukiTopBandInteraction
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [mass_increment]
  ring

private theorem half_pair_square (a : ℕ → ℝ) (K : ℕ) :
    2 * (∑ j ∈ Finset.range K, a j * ∑ i ∈ Finset.range j, a i) =
      (∑ j ∈ Finset.range K, a j) ^ 2 - ∑ j ∈ Finset.range K, (a j) ^ 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    simp only [Finset.sum_range_succ]
    nlinarith

/-- The full upper-band interaction dominates its retained mass square after subtracting the actual diagonal. -/
theorem suzukiTopBandInteraction_mass_lower (K : ℕ) :
    (suzukiTopBandMass K ^ 2 - 2 * suzukiTopBandMass K) /
      (2 * Real.sqrt (2 * K + 2 : ℕ)) ≤ suzukiTopBandInteraction K := by
  have hs : 0 < Real.sqrt (2 * K + 2 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hdiag : (∑ j ∈ Finset.range K, suzukiPrimeWeight (K + j + 1) ^ 2) ≤
      2 * suzukiTopBandMass K := by
    rw [suzukiTopBandMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    nlinarith [suzukiPrimeWeight_nonnegative (K + j + 1), suzukiPrimeWeight_le_two (K + j + 1)]
  have hsq := half_pair_square (fun j ↦ suzukiPrimeWeight (K + j + 1)) K
  have hterm (j : ℕ) (hj : j ∈ Finset.range K) :
      (suzukiPrimeWeight (K + j + 1) * ∑ i ∈ Finset.range j, suzukiPrimeWeight (K + i + 1)) /
        Real.sqrt (2 * K + 2 : ℕ) ≤
      suzukiPrimeWeight (K + j + 1) / Real.sqrt (K + j + 3 : ℕ) *
        ∑ i ∈ Finset.range j, suzukiPrimeWeight (K + i + 1) := by
    have hjK := Finset.mem_range.mp hj
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_left
    · exact mul_nonneg (suzukiPrimeWeight_nonnegative _)
        (Finset.sum_nonneg (fun _ _ ↦ suzukiPrimeWeight_nonnegative _))
    · exact Real.sqrt_pos.mpr (by positivity)
    · exact Real.sqrt_le_sqrt (by exact_mod_cast (show K + j + 3 ≤ 2 * K + 2 by omega))
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_div] at hsum
  apply le_trans _ hsum
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt (2 * K + 2 : ℕ)) hs).mpr
  change (suzukiTopBandMass K ^ 2 - 2 * suzukiTopBandMass K) * _ ≤ _
  have hh : suzukiTopBandMass K ^ 2 - 2 * suzukiTopBandMass K ≤
      2 * (∑ j ∈ Finset.range K, suzukiPrimeWeight (K + j + 1) *
        ∑ i ∈ Finset.range j, suzukiPrimeWeight (K + i + 1)) := by
    change _ = suzukiTopBandMass K ^ 2 - _ at hsq
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hh hs.le]

private theorem mass_ratio (a : ℕ) (ha : 0 < a) :
    Tendsto (fun K : ℕ ↦ suzukiOldPrimeMass (a * K) / Real.sqrt K)
      atTop (𝓝 (2 * Real.sqrt a)) := by
  have hK : Tendsto (fun K : ℕ ↦ ((a * K + 2 : ℕ) : ℝ)) atTop atTop := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    exact tendsto_atTop_add_const_right atTop (2 : ℝ)
      (tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < a by exact_mod_cast ha))
  have hM := suzukiWeightedMass_div_sqrt_tendsto_two.comp hK
  have hi : Tendsto (fun K : ℕ ↦ (2 : ℝ) / K) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun K : ℕ ↦ ((a * K + 2 : ℕ) : ℝ) / K) atTop (𝓝 (a : ℝ)) := by
    have h := (tendsto_const_nhds (x := (a : ℝ)) (f := atTop)).add hi
    norm_num only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with K hK
    have hp : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    push_cast
    field_simp
  have h := hM.mul hr.sqrt
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with K hKpos
  have hs : 0 < Real.sqrt ((a * K + 2 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  rw [suzukiOldPrimeMass, screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass,
    Real.sqrt_div (by positivity)]
  dsimp only [Function.comp_def]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  field_simp

/-- Actual arithmetic cancellation fixes the upper-band mass at a positive square-root proportion. -/
theorem suzukiTopBandMass_div_sqrt_tendsto :
    Tendsto (fun K : ℕ ↦ suzukiTopBandMass K / Real.sqrt K) atTop
      (𝓝 (2 * Real.sqrt 2 - 2)) := by
  have h := (mass_ratio 2 (by decide)).sub (mass_ratio 1 (by decide))
  norm_num only [one_mul, Real.sqrt_one, mul_one] at h
  apply h.congr'
  exact Eventually.of_forall fun K ↦ by
    dsimp only
    rw [suzukiTopBandMass_eq_mass_sub, sub_div]

/-- The interaction omitted by the smaller product cutoff is at least a fixed positive square-root amount at all sufficiently large cutoffs. -/
theorem eventually_sqrt_le_suzukiTopBandInteraction :
    ∀ᶠ K : ℕ in atTop, Real.sqrt K / 32 ≤ suzukiTopBandInteraction K := by
  have hc : (1 / 2 : ℝ) < 2 * Real.sqrt 2 - 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hl := suzukiTopBandMass_div_sqrt_tendsto.eventually (lt_mem_nhds hc)
  filter_upwards [hl, eventually_ge_atTop (64 : ℕ)] with K hmass hK
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK64 : (64 : ℝ) ≤ K := by exact_mod_cast hK
  have hs := Real.sqrt_pos.mpr hKpos
  have hm : Real.sqrt K / 2 ≤ suzukiTopBandMass K := by
    have h := (lt_div_iff₀ hs).mp hmass
    linarith
  have hs8 : (8 : ℝ) ≤ Real.sqrt K := by
    apply (Real.le_sqrt (by norm_num) hKpos.le).mpr
    exact_mod_cast hK
  have hbig : Real.sqrt (2 * K + 2 : ℕ) ≤ 2 * Real.sqrt K := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hKpos.le]
      push_cast
      nlinarith
  have hsq : suzukiTopBandMass K ^ 2 - 2 * suzukiTopBandMass K ≥ (K : ℝ) / 8 := by
    have hroot := Real.sq_sqrt hKpos.le
    nlinarith [sq_nonneg (suzukiTopBandMass K - Real.sqrt K / 2)]
  apply le_trans _ (suzukiTopBandInteraction_mass_lower K)
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt (2 * K + 2 : ℕ))).mpr
  have h := mul_le_mul_of_nonneg_left hbig (div_nonneg hs.le (by norm_num : (0 : ℝ) ≤ 16))
  have hroot := Real.sq_sqrt hKpos.le
  nlinarith

/-- The complete product-cutoff remainder is at least square-root size
eventually, so the exact decomposition cannot discard it as a small error. -/
theorem eventually_sqrt_le_suzukiProductCutoffRemainder :
    ∀ᶠ K : ℕ in atTop, Real.sqrt K / 32 ≤ suzukiProductCutoffRemainder (2 * K) :=
  eventually_sqrt_le_suzukiTopBandInteraction.mono (fun K h ↦
    h.trans (suzukiTopBandInteraction_le_productCutoffRemainder K))

/-- No fixed logarithmic allowance can absorb the omitted product region.
This obstructs discarding the region, not a signed estimate retaining it. -/
theorem eventually_log_lt_suzukiProductCutoffRemainder (B D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ K : ℕ in atTop,
      B + D * Real.log (2 * K + 2 : ℕ) < suzukiProductCutoffRemainder (2 * K) := by
  have hA : Tendsto (fun K : ℕ ↦ (B + D * Real.log 4) / Real.sqrt K) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog : Tendsto (fun K : ℕ ↦ Real.log K / Real.sqrt K) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := (hA.add (hlog.const_mul D)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) + D * 0 < 1 / 32))
  filter_upwards [hsmall, eventually_sqrt_le_suzukiProductCutoffRemainder,
    eventually_ge_atTop (1 : ℕ)] with K hsmall hlower hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by positivity
  have hs := Real.sqrt_pos.mpr hKpos
  have hlogbound : Real.log (2 * K + 2 : ℕ) ≤ Real.log 4 + Real.log K := by
    rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hKpos.ne']
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have hsmall' : B + D * Real.log 4 + D * Real.log K < Real.sqrt K / 32 := by
    have hh : (B + D * Real.log 4 + D * Real.log K) / Real.sqrt K < 1 / 32 := by
      simpa only [add_div, mul_div_assoc] using hsmall
    have hh' := (div_lt_iff₀ hs).mp hh
    linarith
  exact (show B + D * Real.log (2 * K + 2 : ℕ) ≤
    B + D * Real.log 4 + D * Real.log K by
      nlinarith [mul_le_mul_of_nonneg_left hlogbound hD]).trans_lt (hsmall'.trans_le hlower)

end

end RiemannGaussian

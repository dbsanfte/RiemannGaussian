/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiBoundedWork
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# A bilinear lower bound for the actual signed Suzuki work

The slope-matching equation and the tangent inequality for the exponential
give an unconditional lower bound for each unchanged signed work cell. The
bound is a finite triangular von-Mangoldt sum; its definition contains no
implicit canonical center. The exact difference is retained as a nonnegative
exponential convexity remainder plus the positive Archimedean slope tail.

The coefficient of the linear harmonic prime sum is the exact digamma
constant. Changing it incurs the corresponding cumulative harmonic mass,
which cannot be treated as a fixed numerical error.

This is a lower estimate, not a proof that its cumulative sum has a finite
floor. Such an independent arithmetic floor remains open. The new positive
reserve is retained exactly; its summability is not asserted. It is distinct
from the already summable transport cell cost.
-/

namespace RiemannGaussian
noncomputable section
open Filter
open scoped BigOperators Topology

/-- The exact constant in the Archimedean slope after its leading exponential
and positive Lerch tail have been separated. -/
def suzukiArchimedeanSlopeConstant : ℝ :=
  ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2

/-- The coefficient is fixed by the actual zeta function at the central real
point. Nonvanishing there follows from the existing eta theorem. -/
theorem suzukiArchimedeanSlopeConstant_eq_neg_logDeriv_zeta_half :
    suzukiArchimedeanSlopeConstant = -(logDeriv riemannZeta (1 / 2 : ℂ)).re := by
  have hxi : riemannXi (1 / 2 : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      riemannXi_ofReal_ne_zero (1 / 2)
  have hzeta : riemannZeta (1 / 2 : ℂ) ≠ 0 := by
    intro hz
    have he := riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos
      (s := (1 / 2 : ℂ)) (by norm_num) (by norm_num)
    rw [hz, mul_zero] at he
    exact hxi he
  have hd : deriv riemannXi (1 / 2 : ℂ) = 0 := by
    have he := deriv_riemannXi_one_sub (1 / 2)
    norm_num at he
    linear_combination (1 / 2 : ℂ) * he
  have hl : logDeriv riemannXi (1 / 2 : ℂ) = 0 := by
    rw [logDeriv_apply, hd, zero_div]
  have he := logDeriv_riemannXi_of_re_pos_of_riemannZeta_ne_zero
    (s := (1 / 2 : ℂ)) (by norm_num) (by norm_num) hzeta
  rw [hl] at he
  have hre := congrArg Complex.re he
  norm_num [Complex.log_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.div_re] at hre
  unfold suzukiArchimedeanSlopeConstant
  linarith

/-- The positive Lerch slope tail, with the cancelling zeroth term removed. -/
def suzukiArchimedeanPositiveSlopeTail (r : ℝ) : ℝ :=
  ∑' n : ℕ, suzukiPointwiseLerchGapSlopeSummand r (n + 1) / 4

/-- The retained tail is a genuinely convergent series at positive time. -/
theorem summable_suzukiArchimedeanPositiveSlopeTail {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℕ => suzukiPointwiseLerchGapSlopeSummand r (n + 1) / 4) :=
  ((summable_nat_add_iff 1).2 (summable_suzukiPointwiseLerchGapSlopeSummand hr)).div_const 4

/-- Every term of the retained slope tail is nonnegative. -/
theorem suzukiArchimedeanPositiveSlopeTail_nonneg (r : ℝ) :
    0 ≤ suzukiArchimedeanPositiveSlopeTail r := by
  apply tsum_nonneg
  intro n
  unfold suzukiPointwiseLerchGapSlopeSummand
  positivity

/-- Exact cancellation of the zeroth Lerch slope term against the decaying
exponential, before any estimate is taken. -/
theorem suzukiPointwiseArchimedeanSlope_eq_exp_add_constant_add_positiveTail
    {r : ℝ} (hr : 0 < r) :
    suzukiPointwiseArchimedeanSlope r =
      2 * Real.exp (r / 2) + suzukiArchimedeanSlopeConstant +
        suzukiArchimedeanPositiveSlopeTail r := by
  have hs := (summable_suzukiPointwiseLerchGapSlopeSummand hr).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hs
  rw [suzukiPointwiseLerchGapSlopeSummand] at hs
  norm_num at hs
  rw [show -(1 / 2 * r) = -r / 2 by ring] at hs
  unfold suzukiPointwiseArchimedeanSlope suzukiPointwiseLerchGapSlope
    suzukiArchimedeanSlopeConstant suzukiArchimedeanPositiveSlopeTail
  rw [tsum_div_const]
  linarith

/-- A finite bilinear prime expression below the actual work of the next atom.
The old prefix ends at `count + 2`; the new atom is at `count + 3`. -/
def suzukiFirstTailBilinearWork (count : ℕ) : ℝ :=
  suzukiPrimeWeight (count + 1) *
    (2 - (screwPrefixMass suzukiPrimeWeight (count + 1) -
      suzukiArchimedeanSlopeConstant) / Real.sqrt ((count + 3 : ℕ) : ℝ))

/-- The exact positive remainder between the original work and its bilinear
lower bound. It retains both the center displacement and the Lerch tail. -/
def suzukiFirstTailWorkConvexReserve (count : ℕ) : ℝ :=
  suzukiPrimeWeight (count + 1) *
    (2 * (Real.exp ((suzukiFirstTailChebyshevCenter count -
        Real.log ((count + 3 : ℕ) : ℝ)) / 2) - 1 -
      (suzukiFirstTailChebyshevCenter count - Real.log ((count + 3 : ℕ) : ℝ)) / 2) +
      suzukiArchimedeanPositiveSlopeTail (suzukiFirstTailChebyshevCenter count) /
        Real.sqrt ((count + 3 : ℕ) : ℝ))

/-- The difference retained in the exact work identity has a proved sign. -/
theorem suzukiFirstTailWorkConvexReserve_nonneg (count : ℕ) :
    0 ≤ suzukiFirstTailWorkConvexReserve count := by
  have he := Real.add_one_le_exp ((suzukiFirstTailChebyshevCenter count -
    Real.log ((count + 3 : ℕ) : ℝ)) / 2)
  have ht := suzukiArchimedeanPositiveSlopeTail_nonneg (suzukiFirstTailChebyshevCenter count)
  unfold suzukiFirstTailWorkConvexReserve
  exact mul_nonneg (suzukiPrimeWeight_nonnegative _) (add_nonneg (by linarith) (by positivity))

/-- Exact cellwise passage from the original signed work to a finite bilinear
prime sum, with the positive remainder kept rather than discarded. -/
theorem suzukiFirstTailTransportLinearWork_eq_bilinear_add_reserve (count : ℕ) :
    suzukiFirstTailTransportLinearWork count =
      suzukiFirstTailBilinearWork count + suzukiFirstTailWorkConvexReserve count := by
  let r := suzukiFirstTailChebyshevCenter count
  let b : ℝ := ((count + 3 : ℕ) : ℝ)
  have hb : 0 < b := by dsimp [b]; positivity
  have hr : 0 < r := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
    (log_two_le_suzukiFirstTailChebyshevCenter count)
  have hm : suzukiPointwiseArchimedeanSlope r =
      screwPrefixMass suzukiPrimeWeight (count + 1) := by
    rw [screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass]
    simpa only [Nat.add_assoc] using
      suzukiPointwiseArchimedeanSlope_firstTailChebyshevCenter_eq_mass count
  rw [suzukiPointwiseArchimedeanSlope_eq_exp_add_constant_add_positiveTail hr] at hm
  have hscale : Real.sqrt b * Real.exp ((r - Real.log b) / 2) = Real.exp (r / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hb, ← Real.exp_add]
    congr 1
    ring
  have he : Real.exp ((r - Real.log b) / 2) = Real.exp (r / 2) / Real.sqrt b :=
    (eq_div_iff (Real.sqrt_pos.mpr hb).ne').2 (by simpa only [mul_comm] using hscale)
  have hl : suzukiPrimeLocation (count + 1) = Real.log b := by
    simp only [suzukiPrimeLocation, b, Nat.add_assoc]
  unfold suzukiFirstTailTransportLinearWork suzukiFirstTailBilinearWork
    suzukiFirstTailWorkConvexReserve
  change suzukiPrimeWeight (count + 1) * (suzukiPrimeLocation (count + 1) - r) =
    suzukiPrimeWeight (count + 1) *
      (2 - (screwPrefixMass suzukiPrimeWeight (count + 1) -
        suzukiArchimedeanSlopeConstant) / Real.sqrt b) +
    suzukiPrimeWeight (count + 1) *
      (2 * (Real.exp ((r - Real.log b) / 2) - 1 - (r - Real.log b) / 2) +
        suzukiArchimedeanPositiveSlopeTail r / Real.sqrt b)
  rw [hl, ← hm, he]
  ring

/-- An unconditional lower bound for every actual signed work cell. -/
theorem suzukiFirstTailBilinearWork_le_linearWork (count : ℕ) :
    suzukiFirstTailBilinearWork count ≤ suzukiFirstTailTransportLinearWork count := by
  rw [suzukiFirstTailTransportLinearWork_eq_bilinear_add_reserve]
  linarith [suzukiFirstTailWorkConvexReserve_nonneg count]

/-- Every finite band preserves the exact accumulated convexity and tail reserve. -/
theorem suzuki_signed_work_block_eq_bilinear_add_reserve (start count : ℕ) :
    (∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork (start + n)) =
      (∑ n ∈ Finset.range count, suzukiFirstTailBilinearWork (start + n)) +
        ∑ n ∈ Finset.range count, suzukiFirstTailWorkConvexReserve (start + n) := by
  simp_rw [suzukiFirstTailTransportLinearWork_eq_bilinear_add_reserve]
  exact Finset.sum_add_distrib

/-- The unchanged cumulative signed work dominates its finite bilinear prime sum. -/
theorem suzuki_bilinear_work_block_le_signed_work (start count : ℕ) :
    (∑ n ∈ Finset.range count, suzukiFirstTailBilinearWork (start + n)) ≤
      ∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork (start + n) :=
  Finset.sum_le_sum (fun _ _ => suzukiFirstTailBilinearWork_le_linearWork _)

/-- The lower bound is literally triangular in the von-Mangoldt weights.
Every old prime power and the new atom occur with their original weights. -/
theorem suzukiFirstTailBilinearWork_eq_prime_sum (count : ℕ) :
    suzukiFirstTailBilinearWork count =
      2 * ArithmeticFunction.vonMangoldt (count + 3) / Real.sqrt ((count + 3 : ℕ) : ℝ) +
        suzukiArchimedeanSlopeConstant * ArithmeticFunction.vonMangoldt (count + 3) /
          ((count + 3 : ℕ) : ℝ) -
        ArithmeticFunction.vonMangoldt (count + 3) / ((count + 3 : ℕ) : ℝ) *
          ∑ d ∈ Finset.range (count + 1),
            ArithmeticFunction.vonMangoldt (d + 2) / Real.sqrt ((d + 2 : ℕ) : ℝ) := by
  have hb : 0 < ((count + 3 : ℕ) : ℝ) := by positivity
  unfold suzukiFirstTailBilinearWork screwPrefixMass suzukiPrimeWeight
  simp only [Nat.add_assoc, Nat.reduceAdd]
  field_simp [(Real.sqrt_pos.mpr hb).ne', hb.ne']
  ring_nf at hb ⊢
  rw [Real.sq_sqrt hb.le]
  ring

/-- Exact cumulative arithmetic expression, retaining every triangular cross
term rather than taking absolute values term by term. -/
theorem suzuki_bilinear_work_sum_eq_triangular_prime_sum (count : ℕ) :
    (∑ n ∈ Finset.range count, suzukiFirstTailBilinearWork n) =
      2 * (∑ n ∈ Finset.range count,
        ArithmeticFunction.vonMangoldt (n + 3) / Real.sqrt ((n + 3 : ℕ) : ℝ)) +
      suzukiArchimedeanSlopeConstant *
        (∑ n ∈ Finset.range count,
          ArithmeticFunction.vonMangoldt (n + 3) / ((n + 3 : ℕ) : ℝ)) -
      ∑ n ∈ Finset.range count,
        ArithmeticFunction.vonMangoldt (n + 3) / ((n + 3 : ℕ) : ℝ) *
          ∑ d ∈ Finset.range (n + 1),
            ArithmeticFunction.vonMangoldt (d + 2) / Real.sqrt ((d + 2 : ℕ) : ℝ) := by
  simp_rw [suzukiFirstTailBilinearWork_eq_prime_sum, mul_div_assoc, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Exact coefficient sensitivity. A fixed error in the Archimedean constant
is multiplied by the cumulative harmonic prime mass, not by a bounded local cost. -/
theorem suzuki_bilinear_work_sum_coefficient_shift (c : ℝ) (count : ℕ) :
    (∑ n ∈ Finset.range count, suzukiPrimeWeight (n + 1) *
      (2 - (screwPrefixMass suzukiPrimeWeight (n + 1) - c) /
        Real.sqrt ((n + 3 : ℕ) : ℝ))) =
      (∑ n ∈ Finset.range count, suzukiFirstTailBilinearWork n) +
        (c - suzukiArchimedeanSlopeConstant) *
          ∑ n ∈ Finset.range count,
            ArithmeticFunction.vonMangoldt (n + 3) / ((n + 3 : ℕ) : ℝ) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hb : 0 < ((n + 3 : ℕ) : ℝ) := by positivity
  unfold suzukiFirstTailBilinearWork suzukiPrimeWeight
  simp only [Nat.add_assoc, Nat.reduceAdd]
  field_simp [(Real.sqrt_pos.mpr hb).ne', hb.ne']
  ring_nf at hb ⊢
  rw [Real.sq_sqrt hb.le]
  ring

/-- The multiplier of a fixed coefficient error is unbounded. This uses the
unconditional divergence of prime reciprocals, not an RH estimate. -/
theorem tendsto_suzuki_harmonic_prime_mass_atTop :
    Tendsto (fun count : ℕ => ∑ n ∈ Finset.range count,
      ArithmeticFunction.vonMangoldt (n + 3) / ((n + 3 : ℕ) : ℝ)) atTop atTop := by
  have hnot : ¬ Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
    intro hs
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    apply Nat.Primes.not_summable_one_div
    apply ((hs.subtype Nat.Prime).div_const (Real.log 2)).of_nonneg_of_le
      (fun _ => by positivity)
    intro p
    have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
    change 1 / (p : ℝ) ≤ (ArithmeticFunction.vonMangoldt (p : ℕ) / (p : ℝ)) / Real.log 2
    rw [ArithmeticFunction.vonMangoldt_apply_prime p.prop]
    apply (le_div_iff₀ hl).2
    calc
      (1 / (p : ℝ)) * Real.log 2 = Real.log 2 / (p : ℝ) := by ring
      _ ≤ Real.log (p : ℝ) / (p : ℝ) :=
        div_le_div_of_nonneg_right
          (Real.log_le_log (by norm_num) (by exact_mod_cast p.prop.two_le)) hp.le
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun _ => by positivity)).mp
  intro hs
  exact hnot ((summable_nat_add_iff 3).mp hs)

/-- Any fixed downward change of the exact coefficient causes an unbounded
negative discrepancy from the original bilinear sum, however small the change. -/
theorem suzuki_bilinear_work_lower_coefficient_error_tendsto_atBot
    {c : ℝ} (hc : c < suzukiArchimedeanSlopeConstant) :
    Tendsto (fun count : ℕ =>
      (∑ n ∈ Finset.range count, suzukiPrimeWeight (n + 1) *
        (2 - (screwPrefixMass suzukiPrimeWeight (n + 1) - c) /
          Real.sqrt ((n + 3 : ℕ) : ℝ))) -
      ∑ n ∈ Finset.range count, suzukiFirstTailBilinearWork n) atTop atBot := by
  simpa only [suzuki_bilinear_work_sum_coefficient_shift, add_sub_cancel_left] using
    tendsto_suzuki_harmonic_prime_mass_atTop.const_mul_atTop_of_neg (sub_neg.mpr hc)

/-- Exact finite-band accounting in the canonical gap: the bilinear prime work
and its positive reserve are kept separate from the summable transport costs. -/
theorem suzukiFirstTailCanonicalGap_add_eq_bilinear_add_reserve_sub_cost
    (start count : ℕ) :
    suzukiFirstTailCanonicalGap (start + count) = suzukiFirstTailCanonicalGap start +
      (∑ n ∈ Finset.range count, suzukiFirstTailBilinearWork (start + n)) +
      (∑ n ∈ Finset.range count, suzukiFirstTailWorkConvexReserve (start + n)) -
      ∑ n ∈ Finset.range count, suzukiFirstTailTransportCellCost (start + n) := by
  rw [suzukiFirstTailCanonicalGap_add_eq_signed_work_sub_cost,
    suzuki_signed_work_block_eq_bilinear_add_reserve]
  ring

/-- An eventual floor for this explicit finite bilinear prime sum is sufficient
for the existing signed-work contradiction. The floor itself is still open. -/
theorem riemannHypothesis_of_suzuki_bilinear_work_eventually_bounded_below
    (B : ℝ)
    (hwork : ∀ᶠ count : ℕ in atTop, -B ≤
      ∑ n ∈ Finset.range count, suzukiFirstTailBilinearWork n) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_signed_work_eventually_bounded_below B
  filter_upwards [hwork] with count hc
  exact hc.trans (by simpa only [Nat.zero_add] using
    suzuki_bilinear_work_block_le_signed_work 0 count)

end
end RiemannGaussian

import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevQuadratic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# A literal counterexample to the uniform Suzuki quadratic mass condition

At the prime prefix ending at five, the quadratic mass cost exceeds the
source-exact allowance by at least `1/4000`. The stronger sufficient
condition therefore cannot hold at every cutoff. The existing implication
from that condition remains correct; the exact entropy criterion and any
eventual quadratic condition are not refuted by this finite obstruction.

All constants are bounded in Lean using finite rational arithmetic,
logarithm bounds, and summable digamma/Lerch tail comparisons. The canonical
center retains its original definition and exact slope-matching law.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate Interval

namespace RiemannGaussian

noncomputable section

private theorem eulerMascheroni_lower : (5767 / 10000 : ℝ) < Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 1000
  rw [Real.eulerMascheroniSeq] at h
  have hlog : Real.log (1001 : ℝ) ≤
      3 * (Real.log 2 + Real.log 5) + 1 / 1000 := by
    have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1001 / 1000 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num)] at hl
    have he : Real.log (1000 : ℝ) = 3 * (Real.log 2 + Real.log 5) := by
      rw [show (1000 : ℝ) = (2 * 5) ^ 3 by norm_num, Real.log_pow,
        Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [he] at hl
    linarith
  have hh : (harmonic 1000 : ℝ) > 748547 / 100000 := by
    set_option maxRecDepth 20000 in norm_num
  have ht := Real.log_two_lt_d9
  have hf := Real.log_five_lt_d9
  norm_num only [Nat.cast_ofNat] at h
  linarith

private theorem log_pi_lower : (114472 / 100000 : ℝ) < Real.log Real.pi := by
  have h := Real.le_log_one_add_of_nonneg
    (show (0 : ℝ) ≤ (3141592 / 1000000) / 3 - 1 by norm_num)
  have he : Real.log (3141592 / 1000000 : ℝ) =
      Real.log 3 + Real.log (1 + ((3141592 / 1000000 : ℝ) / 3 - 1)) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    norm_num
  have hpi : Real.log (3141592 / 1000000 : ℝ) < Real.log Real.pi :=
    Real.log_lt_log (by norm_num) (by convert Real.pi_gt_d6 using 1; norm_num)
  rw [he] at hpi
  have hthree := Real.log_three_gt_d9
  norm_num at h
  linarith

private theorem hasSum_reciprocal_difference {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    HasSum (fun k : ℕ ↦ c * (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + a + 1))) (c / a) := by
  have hn (k : ℕ) : 0 ≤ c * (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + a + 1)) := by
    apply mul_nonneg hc
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))
  apply (hasSum_iff_tendsto_nat_of_nonneg hn (c / a)).2
  have he (N : ℕ) :
      (∑ k ∈ Finset.range N, c * (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + a + 1))) =
        c * (1 / a - 1 / ((N : ℝ) + a)) := by
    rw [← Finset.mul_sum]
    have hfun : (fun k : ℕ ↦ 1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + a + 1)) =
        fun k : ℕ ↦ 1 / ((k : ℝ) + a) - 1 / (((k + 1 : ℕ) : ℝ) + a) := by
      ext k
      push_cast
      ring
    rw [hfun, Finset.sum_range_sub']
    simp
  have hx : Tendsto (fun N : ℕ ↦ (N : ℝ) + a) atTop atTop :=
    tendsto_atTop_add_const_right atTop a tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun N : ℕ ↦ 1 / ((N : ℝ) + a)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hx
  have ht := ((tendsto_const_nhds (x := 1 / a)).sub hi).const_mul c
  simpa only [he, sub_zero, mul_one_div] using ht

private theorem archimedean_linear_upper :
    ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 < (-26857 / 10000 : ℝ) := by
  let f : ℕ → ℝ := fun n ↦ (suzukiWeilDigammaDifferenceSummand (1 / 2) (1 / 4) n).re
  have hs : HasSum f ((Complex.digamma (1 / 2) - Complex.digamma (1 / 4)).re) :=
    Complex.hasSum_re (hasSum_suzukiWeilDigammaDifferenceSummand
      (a := (1 / 2 : ℂ)) (b := (1 / 4 : ℂ)) (by norm_num) (by norm_num))
  have hf (n : ℕ) : f n = 1 / ((n : ℝ) + 1 / 4) - 1 / ((n : ℝ) + 1 / 2) := by
    unfold f suzukiWeilDigammaDifferenceSummand
    norm_num [Complex.inv_re, Complex.normSq_apply]
  have ht := hasSum_reciprocal_difference
    (a := (65 / 2 : ℝ)) (c := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  have htail (k : ℕ) : (1 / 4 : ℝ) *
      (1 / ((k : ℝ) + 65 / 2) - 1 / ((k : ℝ) + 65 / 2 + 1)) ≤ f (k + 32) := by
    rw [hf]
    push_cast
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have he1 : (1 / 4 : ℝ) *
        (1 / ((k : ℝ) + 65 / 2) - 1 / ((k : ℝ) + 65 / 2 + 1)) =
          (1 / 4 : ℝ) / (((k : ℝ) + 65 / 2) * ((k : ℝ) + 65 / 2 + 1)) := by
      field_simp
      ring
    have he2 : 1 / ((k : ℝ) + 32 + 1 / 4) - 1 / ((k : ℝ) + 32 + 1 / 2) =
        (1 / 4 : ℝ) / (((k : ℝ) + 32 + 1 / 4) * ((k : ℝ) + 32 + 1 / 2)) := by
      field_simp
      ring
    rw [he1, he2]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have hsplit := hs.summable.sum_add_tsum_nat_add 32
  have htailBound := ht.summable.tsum_le_tsum htail ((summable_nat_add_iff 32).2 hs.summable)
  rw [ht.tsum_eq] at htailBound
  have hfinite : (226379 / 100000 : ℝ) <
      (∑ n ∈ Finset.range 32, f n) + (1 / 4 : ℝ) / (65 / 2) := by
    simp only [hf]
    norm_num [Finset.sum_range_succ]
  rw [hs.tsum_eq, Complex.sub_re, Complex.digamma_one_half] at hsplit
  norm_num [Complex.log_re] at hsplit
  have hl2 := Real.log_two_gt_d9
  have hg := eulerMascheroni_lower
  have hp := log_pi_lower
  linarith

private theorem lerch_constant_upper :
    suzukiHurwitzLerchTwo 1 / 4 - 8 ≤ (-370054 / 100000 : ℝ) := by
  let f : ℕ → ℝ := suzukiHurwitzLerchTwoSummand 1
  have hs := summable_suzukiHurwitzLerchTwoSummand (q := (1 : ℝ)) zero_le_one le_rfl
  have hf (n : ℕ) : f n = 1 / ((n : ℝ) + 1 / 4) ^ 2 := by
    simp [f, suzukiHurwitzLerchTwoSummand]
  have ht := hasSum_reciprocal_difference
    (a := (125 / 4 : ℝ)) (c := (1 : ℝ)) (by norm_num) (by norm_num)
  have htail (k : ℕ) : f (k + 32) ≤
      (1 : ℝ) * (1 / ((k : ℝ) + 125 / 4) - 1 / ((k : ℝ) + 125 / 4 + 1)) := by
    rw [hf]
    push_cast
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have he : (1 : ℝ) * (1 / ((k : ℝ) + 125 / 4) - 1 / ((k : ℝ) + 125 / 4 + 1)) =
        1 / (((k : ℝ) + 125 / 4) * ((k : ℝ) + 125 / 4 + 1)) := by
      field_simp
      ring
    rw [he]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have htailBound := ((summable_nat_add_iff 32).2 hs).tsum_le_tsum htail ht.summable
  rw [ht.tsum_eq] at htailBound
  have hsplit := hs.sum_add_tsum_nat_add 32
  change (∑ n ∈ Finset.range 32, f n) + (∑' k : ℕ, f (k + 32)) = suzukiHurwitzLerchTwo 1 at hsplit
  have hfinite : ((∑ n ∈ Finset.range 32, f n) + 1 / (125 / 4 : ℝ)) / 4 - 8 ≤
      (-370054 / 100000 : ℝ) := by
    simp only [hf]
    norm_num [Finset.sum_range_succ]
  linarith

/-- The literal Archimedean term stays below the exponential main term on
nonnegative time. Keeping the first moving Lerch summand cancels the reflected
exponential exactly; the remaining constant and linear coefficients are negative. -/
theorem suzukiPointwiseArchimedean_lt_four_mul_exp_half
    {t : ℝ} (ht : 0 ≤ t) :
    suzukiPointwiseArchimedean t < 4 * Real.exp (t / 2) := by
  have hq0 := (Real.exp_pos (-2 * t)).le
  have hq1 : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hfirst := (summable_suzukiHurwitzLerchTwoSummand hq0 hq1).sum_le_tsum
    (Finset.range 1) (fun n _ => by
      unfold suzukiHurwitzLerchTwoSummand
      positivity)
  have hlerch : 16 ≤ suzukiHurwitzLerchTwo (Real.exp (-2 * t)) := by
    norm_num [suzukiHurwitzLerchTwo, suzukiHurwitzLerchTwoSummand] at hfirst ⊢
    exact hfirst
  have hmoving := mul_le_mul_of_nonneg_left hlerch (Real.exp_pos (-t / 2)).le
  have hlinear : t * (((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht (by linarith [archimedean_linear_upper])
  unfold suzukiPointwiseArchimedean
  nlinarith [lerch_constant_upper]

private theorem prime_mass_five : suzukiChebyshevWeightedMass 5 =
    Real.log 2 / Real.sqrt 2 + Real.log 3 / Real.sqrt 3 + Real.log 2 / 2 +
      Real.log 5 / Real.sqrt 5 := by
  have h := screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass 4
  have h4 : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  norm_num [screwPrefixMass, suzukiPrimeWeight, Finset.sum_range_succ, h4,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5)] at h
  linarith

private theorem prime_moment_five : suzukiChebyshevWeightedLogMoment 5 =
    Real.log 2 ^ 2 / Real.sqrt 2 + Real.log 3 ^ 2 / Real.sqrt 3 + Real.log 2 ^ 2 +
      Real.log 5 ^ 2 / Real.sqrt 5 := by
  have h := screwPrefixMoment_suzukiPrime_eq_chebyshevWeightedLogMoment 4
  have h4 : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  norm_num [screwPrefixMoment, suzukiPrimeWeight, suzukiPrimeLocation, Finset.sum_range_succ, h4, hl4,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5)] at h
  rw [← h]
  ring

private theorem prime_data_five_bounds :
    (2190749 / 1000000 : ℝ) ≤ suzukiChebyshevWeightedMass 5 ∧
      suzukiChebyshevWeightedLogMoment 5 ≤ (2675431 / 1000000 : ℝ) := by
  have h2 : (1414213562 / 1000000000 : ℝ) ≤ Real.sqrt 2 ∧
      Real.sqrt 2 ≤ (1414213563 / 1000000000 : ℝ) := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    constructor <;> nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have h3 : (1732050807 / 1000000000 : ℝ) ≤ Real.sqrt 3 ∧
      Real.sqrt 3 ≤ (1732050808 / 1000000000 : ℝ) := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    constructor <;> nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have h5 : (2236067977 / 1000000000 : ℝ) ≤ Real.sqrt 5 ∧
      Real.sqrt 5 ≤ (2236067978 / 1000000000 : ℝ) := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    constructor <;> nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have hl2 := Real.log_two_gt_d9.le
  have hl3 := Real.log_three_gt_d9.le
  have hl5 := Real.log_five_gt_d9.le
  have hu2 := Real.log_two_lt_d9.le
  have hu3 := Real.log_three_lt_d9.le
  have hu5 := Real.log_five_lt_d9.le
  constructor
  · rw [prime_mass_five]
    have hm2 := div_le_div₀ (by linarith) hl2 (by positivity : (0 : ℝ) < Real.sqrt 2) h2.2
    have hm3 := div_le_div₀ (by linarith) hl3 (by positivity : (0 : ℝ) < Real.sqrt 3) h3.2
    have hm5 := div_le_div₀ (by linarith) hl5 (by positivity : (0 : ℝ) < Real.sqrt 5) h5.2
    norm_num at hm2 hm3 hm5
    linarith
  · rw [prime_moment_five]
    have hp2 : Real.log 2 ^ 2 ≤ (0.6931471808 : ℝ) ^ 2 := by
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hp3 : Real.log 3 ^ 2 ≤ (1.0986122888 : ℝ) ^ 2 := by
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
    have hp5 : Real.log 5 ^ 2 ≤ (1.6094379127 : ℝ) ^ 2 := by
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 5)]
    have hm2 := div_le_div₀ (by positivity) hp2 (by norm_num) h2.1
    have hm3 := div_le_div₀ (by positivity) hp3 (by norm_num) h3.1
    have hm5 := div_le_div₀ (by positivity) hp5 (by norm_num) h5.1
    norm_num at hm2 hm3 hm5
    linarith

private def slopeTail (r : ℝ) : ℝ :=
  ∑' n : ℕ, suzukiPointwiseLerchGapSlopeSummand r (n + 1) / 4

private theorem slopeTail_nonneg (r : ℝ) : 0 ≤ slopeTail r := by
  apply tsum_nonneg
  intro n
  unfold suzukiPointwiseLerchGapSlopeSummand
  positivity

private theorem archimedeanSlope_eq_main_add_tail {r : ℝ} (hr : 0 < r) :
    suzukiPointwiseArchimedeanSlope r =
      2 * Real.exp (r / 2) + ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 +
        slopeTail r := by
  have hs := (summable_suzukiPointwiseLerchGapSlopeSummand hr).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hs
  rw [suzukiPointwiseLerchGapSlopeSummand] at hs
  norm_num at hs
  rw [show -(1 / 2 * r) = -r / 2 by ring] at hs
  unfold suzukiPointwiseArchimedeanSlope suzukiPointwiseLerchGapSlope slopeTail
  rw [tsum_div_const]
  linarith

private theorem slopeTail_mul_fifth_sub_le {r : ℝ} (hr : 0 < r) :
    slopeTail r * (Real.exp (r / 2) ^ 5 - Real.exp (r / 2)) ≤ 2 / 5 := by
  let q := Real.exp (-2 * r)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs : Summable (fun n : ℕ ↦ suzukiPointwiseLerchGapSlopeSummand r (n + 1) / 4) :=
    ((summable_nat_add_iff 1).2 (summable_suzukiPointwiseLerchGapSlopeSummand hr)).div_const 4
  have hterm (n : ℕ) : suzukiPointwiseLerchGapSlopeSummand r (n + 1) / 4 ≤
      (2 / 5 : ℝ) * Real.exp (-5 * r / 2) * q ^ n := by
    have he : Real.exp (-2 * (((n + 1 : ℕ) : ℝ) + 1 / 4) * r) =
        Real.exp (-5 * r / 2) * q ^ n := by
      dsimp only [q]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    unfold suzukiPointwiseLerchGapSlopeSummand
    rw [he]
    have hd : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 / 4 := by positivity
    have hepos : 0 ≤ Real.exp (-5 * r / 2) * q ^ n := by positivity
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    apply (div_le_iff₀ hd).2
    have hn := Nat.cast_nonneg (α := ℝ) n
    push_cast
    nlinarith
  have hb := hs.tsum_le_tsum hterm
    ((summable_geometric_of_lt_one hq0 hq1).mul_left ((2 / 5 : ℝ) * Real.exp (-5 * r / 2)))
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1] at hb
  have hb' : slopeTail r * (1 - q) ≤ (2 / 5 : ℝ) * Real.exp (-5 * r / 2) := by
    exact (le_div_iff₀ (sub_pos.mpr hq1)).mp (by simpa only [slopeTail, div_eq_mul_inv] using hb)
  have hx := Real.exp_pos (r / 2)
  have hex5 : Real.exp (-5 * r / 2) * Real.exp (r / 2) ^ 5 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hex4 : q * Real.exp (r / 2) ^ 5 = Real.exp (r / 2) := by
    dsimp only [q]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_right hb' (pow_nonneg hx.le 5)
  simpa only [mul_assoc, sub_mul, one_mul, hex5, hex4, mul_one] using h

private theorem fifth_sub_mono {a x : ℝ} (ha : 1 ≤ a) (hax : a ≤ x) :
    a ^ 5 - a ≤ x ^ 5 - x := by
  have ha0 : 0 ≤ a := by linarith
  have hx0 : 0 ≤ x := by linarith
  have h4 : a ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ ha0 hax 4
  have h41 : 1 ≤ a ^ 4 := one_le_pow₀ ha
  have h := mul_le_mul hax (sub_le_sub_right h4 1) (sub_nonneg.mpr h41) hx0
  nlinarith only [h]

private theorem canonical_five_bounds :
    (12 / 5 : ℝ) ≤ Real.exp (suzukiFirstTailChebyshevCenter 3 / 2) ∧
      Real.log 5 ≤ suzukiFirstTailChebyshevCenter 3 ∧
      0 ≤ slopeTail (suzukiFirstTailChebyshevCenter 3) ∧
      slopeTail (suzukiFirstTailChebyshevCenter 3) ≤ (13 / 2500 : ℝ) := by
  let r := suzukiFirstTailChebyshevCenter 3
  let X := Real.exp (r / 2)
  let T := slopeTail r
  let D := X ^ 5 - X
  have hr2 : Real.log 2 ≤ r := log_two_le_suzukiFirstTailChebyshevCenter 3
  have hr : 0 < r := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hr2
  have hXone : 1 ≤ X := Real.one_le_exp (by linarith : 0 ≤ r / 2)
  have hXs : X ^ 2 = Real.exp r := by
    dsimp [X]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hXsq : 2 ≤ X ^ 2 := by
    rw [hXs]
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hr2
  have hD : 3 ≤ D := by
    have h : 0 ≤ X * (X ^ 2 - 2) * (X ^ 2 + 2) := by positivity
    dsimp [D]
    nlinarith
  have hT : 0 ≤ T := slopeTail_nonneg r
  have hb : T * D ≤ 2 / 5 := slopeTail_mul_fifth_sub_le hr
  have hTfirst : T ≤ 2 / 15 := by nlinarith
  have hm := suzukiPointwiseArchimedeanSlope_firstTailChebyshevCenter_eq_mass 3
  have he := archimedeanSlope_eq_main_add_tail hr
  have hM := prime_data_five_bounds.1
  have hc := archimedean_linear_upper
  change suzukiPointwiseArchimedeanSlope r = suzukiChebyshevWeightedMass 5 at hm
  change suzukiPointwiseArchimedeanSlope r = 2 * X +
    ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + T at he
  have hX225 : (9 / 4 : ℝ) ≤ X := by linarith
  have hD225 := fifth_sub_mono (by norm_num : (1 : ℝ) ≤ 9 / 4) hX225
  change (9 / 4 : ℝ) ^ 5 - 9 / 4 ≤ D at hD225
  norm_num at hD225
  have hTsecond : T ≤ 1 / 100 := by nlinarith
  have hX24 : (12 / 5 : ℝ) ≤ X := by linarith
  have hD24 := fifth_sub_mono (by norm_num : (1 : ℝ) ≤ 12 / 5) hX24
  change (12 / 5 : ℝ) ^ 5 - 12 / 5 ≤ D at hD24
  norm_num at hD24
  have hTlast : T ≤ 13 / 2500 := by nlinarith
  have hlog5 : Real.log 5 ≤ r := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 5), ← hXs]
    nlinarith
  exact ⟨hX24, hlog5, hT, hTlast⟩

private theorem slope_lower_order_eq {r : ℝ} (hr : 0 < r) :
    suzukiChebyshevArchimedeanSlopeLowerOrder r =
      ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1 + slopeTail r := by
  have h := archimedeanSlope_eq_main_add_tail hr
  unfold suzukiPointwiseArchimedeanSlope at h
  unfold suzukiChebyshevArchimedeanSlopeLowerOrder
  linarith

private theorem archimedean_lower_order_upper {r : ℝ} (hr : 0 < r) :
    suzukiChebyshevArchimedeanLowerOrder r ≤ suzukiHurwitzLerchTwo 1 / 4 - 4 +
      r * (((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1) := by
  have hq0 := (Real.exp_pos (-2 * r)).le
  have hq1 : Real.exp (-2 * r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hfirst := (summable_suzukiHurwitzLerchTwoSummand hq0 hq1).sum_le_tsum (Finset.range 1)
    (fun n _ ↦ by unfold suzukiHurwitzLerchTwoSummand; positivity)
  norm_num [suzukiHurwitzLerchTwoSummand] at hfirst
  rw [show -(2 * r) = -2 * r by ring] at hfirst
  change 16 ≤ suzukiHurwitzLerchTwo (Real.exp (-2 * r)) at hfirst
  have h := mul_le_mul_of_nonneg_left hfirst (Real.exp_pos (-r / 2)).le
  unfold suzukiChebyshevArchimedeanLowerOrder
  nlinarith

private theorem legendre_five_upper :
    suzukiChebyshevLegendreLowerOrder (suzukiFirstTailChebyshevCenter 3)
      (suzukiChebyshevCorrectedMassRatio (suzukiFirstTailChebyshevCenter 3) 5) ≤
      suzukiHurwitzLerchTwo 1 / 4 - 4 +
        (((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1) * Real.log 5 := by
  let r := suzukiFirstTailChebyshevCenter 3
  have hr5 : Real.log 5 ≤ r := canonical_five_bounds.2.1
  have hr : 0 < r := (Real.log_pos (by norm_num : (1 : ℝ) < 5)).trans_le hr5
  have hlog : 2 * Real.log (suzukiChebyshevCorrectedMassRatio r 5) = r - Real.log 5 := by
    have h := suzukiChebyshevCorrectedMassRatio_firstTail_eq_exp_displacement 3
    change suzukiChebyshevCorrectedMassRatio r 5 = Real.exp ((r - Real.log 5) / 2) at h
    rw [h, Real.log_exp]
    ring
  have hmain := archimedean_lower_order_upper hr
  have htail := mul_nonneg (sub_nonneg.mpr hr5) (slopeTail_nonneg r)
  change suzukiChebyshevLegendreLowerOrder r (suzukiChebyshevCorrectedMassRatio r 5) ≤ _
  rw [suzukiChebyshevLegendreLowerOrder, hlog, slope_lower_order_eq hr]
  nlinarith

private theorem exact_right_side_five_upper :
    suzukiChebyshevEndpointCenteredError 5 +
      suzukiChebyshevLegendreLowerOrder (suzukiFirstTailChebyshevCenter 3)
        (suzukiChebyshevCorrectedMassRatio (suzukiFirstTailChebyshevCenter 3) 5) ≤
      (7083 / 100000 : ℝ) := by
  have hleg := legendre_five_upper
  have he : suzukiChebyshevEndpointCenteredError 5 =
      suzukiChebyshevWeightedLogMoment 5 - Real.log 5 * suzukiChebyshevWeightedMass 5 +
        4 * Real.sqrt 5 - Real.log 5 - 4 := by
    unfold suzukiChebyshevEndpointCenteredError suzukiChebyshevWeightedLogMomentError
      suzukiChebyshevWeightedMassError suzukiChebyshevContinuousMass suzukiChebyshevContinuousLogMoment
    rw [← Real.sqrt_eq_rpow]
    ring
  have hM := prime_data_five_bounds.1
  have hL := prime_data_five_bounds.2
  have hc := archimedean_linear_upper
  have hC := lerch_constant_upper
  have hl : (1609437912 / 1000000000 : ℝ) ≤ Real.log 5 := by
    linarith [Real.log_five_gt_d9]
  have hroot : Real.sqrt 5 ≤ (2236068 / 1000000 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg (5 : ℝ)]
  have hprod := mul_le_mul hl
    (show (2190749 / 1000000 : ℝ) + 26857 / 10000 ≤
        suzukiChebyshevWeightedMass 5 - ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 by linarith)
    (by norm_num) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5))
  rw [he]
  nlinarith

private theorem quadratic_cost_five_lower :
    (712 / 10000 : ℝ) ≤
      suzukiChebyshevQuadraticMassCost (suzukiFirstTailChebyshevCenter 3) 5 := by
  let r := suzukiFirstTailChebyshevCenter 3
  let d := suzukiChebyshevWeightedMass 5 - 2 * Real.sqrt 5 -
    ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 - slopeTail r
  have hr : 0 < r := (Real.log_pos (by norm_num : (1 : ℝ) < 5)).trans_le
    canonical_five_bounds.2.1
  have hM := prime_data_five_bounds.1
  have hc := archimedean_linear_upper
  have hT : slopeTail r ≤ (13 / 2500 : ℝ) := canonical_five_bounds.2.2.2
  have hroot : Real.sqrt 5 ≤ (2236068 / 1000000 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg (5 : ℝ)]
  have hd : (399111 / 1000000 : ℝ) ≤ d := by dsimp [d]; linarith
  have hsq : (399111 / 1000000 : ℝ) ^ 2 ≤ d ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hd 2
  have he : suzukiChebyshevQuadraticMassCost r 5 = d ^ 2 / Real.sqrt 5 := by
    unfold suzukiChebyshevQuadraticMassCost suzukiChebyshevWeightedMassError suzukiChebyshevContinuousMass
    rw [slope_lower_order_eq hr, ← Real.sqrt_eq_rpow]
    dsimp [d]
    ring
  change (712 / 10000 : ℝ) ≤ suzukiChebyshevQuadraticMassCost r 5
  rw [he]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5))).2
  nlinarith

/-- At the literal prefix ending at five, the quadratic mass cost exceeds
its exact arithmetic allowance by a certified positive rational margin. -/
theorem suzukiChebyshevQuadraticMassCost_five_exceeds_allowance :
    suzukiChebyshevEndpointCenteredError 5 +
      suzukiChebyshevLegendreLowerOrder (suzukiFirstTailChebyshevCenter 3)
        (suzukiChebyshevCorrectedMassRatio (suzukiFirstTailChebyshevCenter 3) 5) + 1 / 4000 ≤
      suzukiChebyshevQuadraticMassCost (suzukiFirstTailChebyshevCenter 3) 5 := by
  linarith [exact_right_side_five_upper, quadratic_cost_five_lower]


/-- The stronger quadratic sufficient inequality is false at the canonical
center of the actual prime prefix ending at five. -/
theorem suzukiChebyshevQuadraticMassCost_five_not_le_allowance :
    ¬ suzukiChebyshevQuadraticMassCost (suzukiFirstTailChebyshevCenter 3) 5 ≤
      suzukiChebyshevEndpointCenteredError 5 +
        suzukiChebyshevLegendreLowerOrder (suzukiFirstTailChebyshevCenter 3)
          (suzukiChebyshevCorrectedMassRatio (suzukiFirstTailChebyshevCenter 3) 5) := by
  intro h
  linarith [suzukiChebyshevQuadraticMassCost_five_exceeds_allowance]

/-- The all-cutoff hypothesis of the existing quadratic mass--moment
criterion cannot be established. This says nothing against an eventual
bound or the weaker exact entropy criterion. -/
theorem not_forall_suzukiChebyshevQuadraticMassCost_le_allowance :
    ¬ ∀ count : ℕ, 1 ≤ count →
      suzukiChebyshevQuadraticMassCost (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) ≤
        suzukiChebyshevEndpointCenteredError (((count + 2 : ℕ) : ℝ)) +
          suzukiChebyshevLegendreLowerOrder (suzukiFirstTailChebyshevCenter count)
            (suzukiChebyshevCorrectedMassRatio (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ))) := by
  intro h
  exact suzukiChebyshevQuadraticMassCost_five_not_le_allowance (h 3 (by norm_num))

end

end RiemannGaussian

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSignedFiveHeight

/-!
# An infinite family of coupled prime phases

Multiplying the fourth-power phase kernel by the Poisson kernel with radius
`1/8` gives an everywhere nonnegative cosine series with infinitely many
strictly positive coefficients. Its tail is geometric. The phase series,
the prime-power series, and their interchange are justified by summable
majorants before estimating any logarithmic derivative.

This is the classical positive-trigonometric-kernel method. Infinite support
does not itself supply an arbitrary exclusion margin or the open signed
Suzuki arithmetic bound.
-/

open Complex
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

private theorem infinitePhase_geometric_hasSum :
    HasSum (fun n : ℕ ↦ (1 / 8 : ℝ) ^ n) (8 / 7) := by
  convert hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num : (1 / 8 : ℝ) < 1) using 1
  norm_num

private theorem infinitePhase_cos_summable (k : ℕ) (t : ℝ) :
    Summable (fun n : ℕ ↦ (1 / 8 : ℝ) ^ n * Real.cos (((n + k : ℕ) : ℝ) * t)) := by
  apply infinitePhase_geometric_hasSum.summable.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ n)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

private theorem infinitePhase_cos_shift (k : ℕ) (t : ℝ) :
    (∑' n : ℕ, (1 / 8 : ℝ) ^ n * Real.cos (((n + k : ℕ) : ℝ) * t)) =
      Real.cos ((k : ℝ) * t) + (1 / 8 : ℝ) *
        ∑' n : ℕ, (1 / 8 : ℝ) ^ n * Real.cos (((n + (k + 1) : ℕ) : ℝ) * t) := by
  rw [(infinitePhase_cos_summable k t).tsum_eq_zero_add]
  simp only [zero_add, pow_zero, one_mul, ← tsum_mul_left, pow_succ']
  congr 1
  apply tsum_congr
  intro n
  rw [show n + 1 + k = n + (k + 1) by omega]
  ring

/-- The complete geometric tail of the infinite cosine kernel, including
its first frequency four. -/
def zetaInfinitePhaseTail (t : ℝ) : ℝ :=
  ∑' n : ℕ, (1 / 8 : ℝ) ^ n * Real.cos (((n + 4 : ℕ) : ℝ) * t)

/-- The retained infinite tail satisfies the exact Poisson denominator
identity; all infinitely many terms participate in this equality. -/
theorem zetaInfinitePhaseTail_denominator_identity (t : ℝ) :
    (65 - 16 * Real.cos t) * zetaInfinitePhaseTail t =
      64 * Real.cos (4 * t) - 8 * Real.cos (3 * t) := by
  let T (k : ℕ) := ∑' n : ℕ, (1 / 8 : ℝ) ^ n *
    Real.cos (((n + k : ℕ) : ℝ) * t)
  have h3 := infinitePhase_cos_shift 3 t
  have h4 := infinitePhase_cos_shift 4 t
  have hrec : T 5 + T 3 = 2 * Real.cos t * T 4 := by
    dsimp only [T]
    rw [← (infinitePhase_cos_summable 5 t).tsum_add (infinitePhase_cos_summable 3 t),
      ← tsum_mul_left]
    apply tsum_congr
    intro n
    have hc := Real.cos_add_cos (((n + 5 : ℕ) : ℝ) * t) (((n + 3 : ℕ) : ℝ) * t)
    have he1 : ((((n + 5 : ℕ) : ℝ) * t + ((n + 3 : ℕ) : ℝ) * t) / 2) =
        ((n + 4 : ℕ) : ℝ) * t := by push_cast; ring
    have he2 : ((((n + 5 : ℕ) : ℝ) * t - ((n + 3 : ℕ) : ℝ) * t) / 2) = t := by
      push_cast
      ring
    rw [he1, he2] at hc
    nlinarith [congrArg (fun z : ℝ ↦ (1 / 8 : ℝ) ^ n * z) hc]
  change T 3 = Real.cos ((3 : ℕ) * t) + (1 / 8 : ℝ) * T 4 at h3
  change T 4 = Real.cos ((4 : ℕ) * t) + (1 / 8 : ℝ) * T 5 at h4
  change (65 - 16 * Real.cos t) * T 4 = _
  norm_num only [Nat.cast_ofNat] at h3 h4
  nlinarith

/-- The cosine coefficients of the fourth-power kernel multiplied by the
Poisson kernel of radius `1/8`, scaled by `2^24` to keep them integral. -/
def zetaInfinitePhaseKernel (t : ℝ) : ℝ :=
  712249344 + 1162805760 * Real.cos t + 624545856 * Real.cos (2 * t) +
    212253192 * Real.cos (3 * t) + 43046721 * zetaInfinitePhaseTail t

/-- The infinite phase kernel is exactly a positive Poisson factor times
the previously retained fourth power. -/
theorem zetaInfinitePhaseKernel_denominator_identity (t : ℝ) :
    (65 - 16 * Real.cos t) * zetaInfinitePhaseKernel t =
      8455716864 * (1 + Real.cos t) ^ 4 := by
  have ht := zetaInfinitePhaseTail_denominator_identity t
  rw [show 4 * t = 2 * (2 * t) by ring] at ht
  simp only [Real.cos_two_mul, Real.cos_three_mul] at ht
  unfold zetaInfinitePhaseKernel
  simp only [Real.cos_two_mul, Real.cos_three_mul]
  nlinarith only [ht]

/-- Positivity is proved for the full infinite phase kernel before any
prime or zero sum is bounded. -/
theorem zetaInfinitePhaseKernel_nonneg (t : ℝ) : 0 ≤ zetaInfinitePhaseKernel t := by
  have hd : 0 < 65 - 16 * Real.cos t := by linarith [Real.cos_le_one t]
  have h := zetaInfinitePhaseKernel_denominator_identity t
  have hp : 0 ≤ (1 + Real.cos t) ^ 4 := by positivity
  nlinarith

/-- The signed combination at every nonnegative integer multiple of the
ordinate. Frequencies four and above have strictly positive geometric weights. -/
def zetaInfiniteHeightCombination (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  712249344 * f 0 + 1162805760 * f y + 624545856 * f (2 * y) +
    212253192 * f (3 * y) +
      43046721 * ∑' n : ℕ, (1 / 8 : ℝ) ^ n * f (((n + 4 : ℕ) : ℝ) * y)

private theorem infinitePhase_prime_hasSum {a : ℝ} (ha : 1 < a) (t : ℝ) :
    HasSum (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * Real.exp (-a * Real.log n) *
      Real.cos (t * Real.log n)) (-logDeriv riemannZeta ((a : ℂ) + I * t)).re := by
  have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (a : ℂ) + I * t) (by simpa using ha)
  rw [neg_logDeriv_riemannZeta_eq_vonMangoldt (by simpa using ha), Complex.re_tsum hs]
  have hsre : Summable (fun n ↦ (LSeries.term (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ))
    ((a : ℂ) + I * t) n).re) := Complex.reCLM.summable hs
  simpa only [vonMangoldt_LSeries_term_re] using hsre.hasSum

private theorem infinitePhase_amplitude_hasSum {a : ℝ} (ha : 1 < a) :
    HasSum (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * Real.exp (-a * Real.log n))
      (-logDeriv riemannZeta (a : ℂ)).re := by
  simpa only [Complex.ofReal_zero, mul_zero, add_zero, zero_mul, Real.cos_zero, mul_one]
    using infinitePhase_prime_hasSum ha 0

/-- Absolute convergence of the actual prime-power series supplies a
uniform bound in the ordinate, used only to justify the infinite phase sum. -/
theorem norm_neg_logDeriv_riemannZeta_re_le_real_axis {a : ℝ} (ha : 1 < a) (t : ℝ) :
    ‖(-logDeriv riemannZeta ((a : ℂ) + I * t)).re‖ ≤
      (-logDeriv riemannZeta (a : ℂ)).re := by
  rw [← (infinitePhase_prime_hasSum ha t).tsum_eq]
  apply tsum_of_norm_bounded (infinitePhase_amplitude_hasSum ha)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

/-- The infinite family of actual logarithmic derivatives is absolutely
summable on `re s > 1`. -/
theorem summable_infinitePhase_logDeriv {a : ℝ} (ha : 1 < a) (y : ℝ) :
    Summable (fun n : ℕ ↦ (1 / 8 : ℝ) ^ n *
      (-logDeriv riemannZeta ((a : ℂ) + I * ((((n + 4 : ℕ) : ℝ) * y : ℝ) : ℂ))).re) := by
  apply (infinitePhase_geometric_hasSum.summable.mul_right
    (-logDeriv riemannZeta (a : ℂ)).re).of_norm_bounded
  intro n
  rw [norm_mul, Real.norm_eq_abs ( (1 / 8 : ℝ) ^ n),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ n)]
  exact mul_le_mul_of_nonneg_left (norm_neg_logDeriv_riemannZeta_re_le_real_axis ha _)
    (by positivity)

/-- The entire infinite phase family gives a signed inequality for the
literal zeta logarithmic derivative, with no convergence or arithmetic premise
beyond the half-plane of absolute convergence. -/
theorem neg_logDeriv_riemannZeta_infinite_height_nonneg {a : ℝ} (ha : 1 < a) (y : ℝ) :
    0 ≤ zetaInfiniteHeightCombination
      (fun t ↦ (-logDeriv riemannZeta ((a : ℂ) + I * t)).re) y := by
  let w (n : ℕ) := ArithmeticFunction.vonMangoldt n * Real.exp (-a * Real.log n)
  have hw (n : ℕ) : 0 ≤ w n :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
  have hwS : Summable w := (infinitePhase_amplitude_hasSum ha).summable
  let f (j n : ℕ) := (1 / 8 : ℝ) ^ n * w j *
    Real.cos ((((n + 4 : ℕ) : ℝ) * y) * Real.log j)
  have hmajor := hwS.mul_of_nonneg infinitePhase_geometric_hasSum.summable hw
    (fun _ ↦ by positivity)
  have hdouble : Summable (Function.uncurry f) := by
    apply hmajor.of_norm_bounded
    intro p
    dsimp [f, Function.uncurry]
    rw [abs_mul, abs_of_nonneg (mul_nonneg (by positivity) (hw p.1))]
    calc
      _ ≤ (1 / 8 : ℝ) ^ p.2 * w p.1 :=
        mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
      _ = _ := mul_comm _ _
  have htail : HasSum (fun j ↦ ∑' n, f j n)
      (∑' n : ℕ, (1 / 8 : ℝ) ^ n *
        (-logDeriv riemannZeta ((a : ℂ) + I * ((((n + 4 : ℕ) : ℝ) * y : ℝ) : ℂ))).re) := by
    have he : (∑' j, ∑' n, f j n) =
        ∑' n : ℕ, (1 / 8 : ℝ) ^ n *
          (-logDeriv riemannZeta ((a : ℂ) + I * ((((n + 4 : ℕ) : ℝ) * y : ℝ) : ℂ))).re := by
      rw [← hdouble.tsum_comm]
      apply tsum_congr
      intro n
      dsimp only [f]
      rw [← (infinitePhase_prime_hasSum ha (((n + 4 : ℕ) : ℝ) * y)).tsum_eq,
        ← tsum_mul_left]
      apply tsum_congr
      intro j
      dsimp [w]
      ring
    rw [← he]
    exact hdouble.prod.hasSum
  have hsum := ((((infinitePhase_prime_hasSum ha 0).mul_left 712249344).add
    ((infinitePhase_prime_hasSum ha y).mul_left 1162805760)).add
    ((infinitePhase_prime_hasSum ha (2 * y)).mul_left 624545856)).add
    ((infinitePhase_prime_hasSum ha (3 * y)).mul_left 212253192) |>.add
    (htail.mul_left 43046721)
  unfold zetaInfiniteHeightCombination
  rw [← hsum.tsum_eq]
  apply tsum_nonneg
  intro j
  have he : (∑' n, f j n) = w j * zetaInfinitePhaseTail (y * Real.log j) := by
    unfold zetaInfinitePhaseTail
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [f]
    simp only [mul_assoc]
    ring
  rw [he]
  have hp := mul_nonneg (hw j) (zetaInfinitePhaseKernel_nonneg (y * Real.log j))
  dsimp only [zetaInfinitePhaseKernel, w] at hp ⊢
  simp only [zero_mul, Real.cos_zero, mul_one, mul_assoc] at hp ⊢
  nlinarith only [hp]

private theorem infinitePhase_linear_hasSum (A B : ℝ) :
    HasSum (fun n : ℕ ↦ (1 / 8 : ℝ) ^ n * ((n : ℝ) * A + B))
      ((8 / 49 : ℝ) * A + (8 / 7 : ℝ) * B) := by
  have hc := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 8 : ℝ))
    (by norm_num)
  norm_num at hc
  convert! (hc.mul_right A).add (infinitePhase_geometric_hasSum.mul_right B) using 1
  ext n
  ring

private theorem infinitePhase_logHeight_le {k : ℝ} (hk : 1 ≤ k) (y : ℝ) :
    localZetaLogHeight (k * y) ≤ ((k + 1) / 2) * localZetaLogHeight y := by
  have h := localZetaLogHeight_mul_le_add_log hk y
  have hl := Real.log_le_sub_one_of_pos (show 0 < k by linarith)
  have hp := mul_nonneg (show 0 ≤ k - 1 by linarith)
    (show 0 ≤ localZetaLogHeight y - 2 by linarith [two_lt_localZetaLogHeight y])
  nlinarith

private theorem infinitePhase_pole_le_real_axis {x : ℝ} (hx : 0 < x) (t : ℝ) :
    x / (x ^ 2 + t ^ 2) ≤ 1 / x := by
  calc
    x / (x ^ 2 + t ^ 2) ≤ x / x ^ 2 :=
      div_le_div_of_nonneg_left hx.le (sq_pos_of_pos hx) (by nlinarith [sq_nonneg t])
    _ = 1 / x := by field_simp

/-- The full local pole sums are summable across the infinite phase
family. This justifies retaining them together before selecting a zero. -/
theorem summable_infinitePhase_localZetaPoleSum {x : ℝ} (hx : 0 < x)
    (hxsmall : x ≤ 1 / 4) (y : ℝ) :
    Summable (fun n : ℕ ↦ (1 / 8 : ℝ) ^ n *
      (localZetaPoleSum (((n + 4 : ℕ) : ℝ) * y) ((x - 1 / 2 : ℝ) : ℂ)).re) := by
  let L := localZetaLogHeight y
  let D := (-logDeriv riemannZeta ((1 + x : ℝ) : ℂ)).re
  have hbound (n : ℕ) :
      (localZetaPoleSum (((n + 4 : ℕ) : ℝ) * y) ((x - 1 / 2 : ℝ) : ℂ)).re ≤
        (n : ℝ) * (224 * L) + (1 / x + D + 1120 * L) := by
    have h := neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum
      (((n + 4 : ℕ) : ℝ) * y) hx hxsmall
    have hp := infinitePhase_pole_le_real_axis hx (((n + 4 : ℕ) : ℝ) * y)
    have hnorm := norm_neg_logDeriv_riemannZeta_re_le_real_axis
      (by linarith : 1 < 1 + x) (((n + 4 : ℕ) : ℝ) * y)
    have hL := infinitePhase_logHeight_le (k := ((n + 4 : ℕ) : ℝ))
      (by exact_mod_cast (show 1 ≤ n + 4 by omega)) y
    have hneg := neg_le_abs (-logDeriv riemannZeta
      (((1 + x : ℝ) : ℂ) + I * ((((n + 4 : ℕ) : ℝ) * y : ℝ) : ℂ))).re
    rw [Real.norm_eq_abs] at hnorm
    simp only [Nat.cast_add, Nat.cast_ofNat] at h hp hnorm hneg hL ⊢
    dsimp only [L, D]
    linarith
  apply (infinitePhase_linear_hasSum (224 * L) (1 / x + D + 1120 * L)).summable.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (by positivity) (localZetaPoleSum_re_nonneg _ hx))]
  exact mul_le_mul_of_nonneg_left (hbound n) (by positivity)

private theorem infinitePhase_nonzero_pole_le {k y x : ℝ} (hk : 1 ≤ k) (hy : y ≠ 0)
    (hx : 0 < x) : x / (x ^ 2 + (k * y) ^ 2) ≤ x / y ^ 2 := by
  apply div_le_div_of_nonneg_left hx.le (sq_pos_of_ne_zero hy)
  have h := mul_nonneg (show 0 ≤ k ^ 2 - 1 by nlinarith) (sq_nonneg y)
  nlinarith [sq_nonneg x]

/-- The independent infinite prime inequality controls the complete
infinite family of local zero sums. The full height cost and the pole at one
are included in the explicit bound. -/
theorem infinite_height_localZetaPoleSum_re_le {y x : ℝ} (hy : y ≠ 0)
    (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    zetaInfiniteHeightCombination
      (fun t ↦ (localZetaPoleSum t ((x - 1 / 2 : ℝ) : ℂ)).re) y ≤
        712249344 / x + 1507000000000 * localZetaLogHeight y +
          2050000000 * x / y ^ 2 := by
  let L := localZetaLogHeight y
  let D (t : ℝ) := (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * t)).re
  let P (t : ℝ) := (localZetaPoleSum t ((x - 1 / 2 : ℝ) : ℂ)).re
  have hpoint {k : ℝ} (hk : 1 ≤ k) :
      D (k * y) + P (k * y) ≤ x / y ^ 2 + 224 * (k + 1) * L := by
    have h := neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum (k * y) hx hxsmall
    have hp := infinitePhase_nonzero_pole_le hk hy hx
    have hL := infinitePhase_logHeight_le hk y
    dsimp only [D, P, L]
    linarith
  have hD := summable_infinitePhase_logDeriv (by linarith : 1 < 1 + x) y
  have hP := summable_infinitePhase_localZetaPoleSum hx hxsmall y
  have htail :
      (∑' n : ℕ, (1 / 8 : ℝ) ^ n * D (((n + 4 : ℕ) : ℝ) * y)) +
        (∑' n : ℕ, (1 / 8 : ℝ) ^ n * P (((n + 4 : ℕ) : ℝ) * y)) ≤
          (8 / 7 : ℝ) * (x / y ^ 2) + (9216 / 7 : ℝ) * L := by
    rw [← hD.tsum_add hP]
    have hu := infinitePhase_linear_hasSum (224 * L) (x / y ^ 2 + 1120 * L)
    have hle := (hD.add hP).tsum_le_tsum (fun n ↦ show
        (1 / 8 : ℝ) ^ n * D (((n + 4 : ℕ) : ℝ) * y) +
          (1 / 8 : ℝ) ^ n * P (((n + 4 : ℕ) : ℝ) * y) ≤
        (1 / 8 : ℝ) ^ n * ((n : ℝ) * (224 * L) + (x / y ^ 2 + 1120 * L)) from by
      have h := hpoint (k := ((n + 4 : ℕ) : ℝ))
        (by exact_mod_cast (show 1 ≤ n + 4 by omega))
      simp only [Nat.cast_add, Nat.cast_ofNat] at h ⊢
      have hm := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ n)
      nlinarith only [hm]) hu.summable
    rw [hu.tsum_eq] at hle
    linarith
  have h0 := neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum 0 hx hxsmall
  have he0 : x / (x ^ 2 + (0 : ℝ) ^ 2) = 1 / x := by field_simp; ring
  rw [he0] at h0
  have hL0 := localZetaLogHeight_zero_le y
  have h1 := hpoint (k := 1) (by norm_num)
  have h2 := hpoint (k := 2) (by norm_num)
  have h3 := hpoint (k := 3) (by norm_num)
  have hprime := neg_logDeriv_riemannZeta_infinite_height_nonneg
    (by linarith : 1 < 1 + x) y
  change 0 ≤ zetaInfiniteHeightCombination D y at hprime
  change zetaInfiniteHeightCombination P y ≤ _
  unfold zetaInfiniteHeightCombination at hprime ⊢
  change D 0 ≤ 1 / x + 448 * localZetaLogHeight 0 - P 0 at h0
  simp only [one_mul] at h1
  change _ ≤ 712249344 / x + 1507000000000 * L + 2050000000 * x / y ^ 2
  have hLpos : 0 < L := by dsimp [L]; linarith [two_lt_localZetaLogHeight y]
  have hxdiv : 0 ≤ x / y ^ 2 := div_nonneg hx.le (sq_nonneg y)
  change localZetaLogHeight 0 ≤ L at hL0
  rw [show (712249344 : ℝ) / x = 712249344 * (1 / x) by ring]
  rw [mul_div_assoc]
  nlinarith only [hprime, h0, h1, h2, h3, htail, hL0, hLpos, hxdiv]

/-- Selecting one actual zero from the infinite coupled inequality keeps
its full multiplicity; every remaining local pole contribution is nonnegative. -/
theorem infiniteHeight_multiplicity_div_gap_le (rho : NontrivialZetaZero)
    (hrho : 3 / 4 ≤ rho.1.re) {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    1162805760 * (analyticZetaZeroMultiplicity rho : ℝ) / (x + 1 - rho.1.re) ≤
      712249344 / x + 1507000000000 * localZetaLogHeight rho.1.im +
        2050000000 * x / rho.1.im ^ 2 := by
  have h := infinite_height_localZetaPoleSum_re_le
    (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) hx hxsmall
  have hs := multiplicity_div_gap_le_localZetaPoleSum_re rho hrho hx
  have h0 := localZetaPoleSum_re_nonneg 0 hx
  have h2 := localZetaPoleSum_re_nonneg (2 * rho.1.im) hx
  have h3 := localZetaPoleSum_re_nonneg (3 * rho.1.im) hx
  have ht : 0 ≤ ∑' n : ℕ, (1 / 8 : ℝ) ^ n *
      (localZetaPoleSum (((n + 4 : ℕ) : ℝ) * rho.1.im) ((x - 1 / 2 : ℝ) : ℂ)).re :=
    tsum_nonneg (fun _ ↦ mul_nonneg (by positivity) (localZetaPoleSum_re_nonneg _ hx))
  unfold zetaInfiniteHeightCombination at h
  rw [mul_div_assoc]
  linarith

/-- Evaluating at `18/5` times the actual edge distance produces the
explicit quadratic zero constraint for the infinite family. -/
theorem multiplicity_le_infiniteHeight_signed_zero_gap (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    20930503680 * (analyticZetaZeroMultiplicity rho : ℝ) - 16381734912 ≤
      124779600000000 * localZetaLogHeight rho.1.im * (1 - rho.1.re) +
        611064000000 * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  let d := 1 - rho.1.re
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have h := infiniteHeight_multiplicity_div_gap_le rho
    (by linarith : 3 / 4 ≤ rho.1.re) (by positivity : 0 < (18 / 5 : ℝ) * d)
    (by dsimp [d]; linarith : (18 / 5 : ℝ) * d ≤ 1 / 4)
  rw [show (18 / 5 : ℝ) * d + 1 - rho.1.re = (23 / 5 : ℝ) * d by dsimp [d]; ring] at h
  have hmul := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (414 / 5 : ℝ) * d by positivity)
  have he : (414 / 5 : ℝ) * d *
      (1162805760 * (analyticZetaZeroMultiplicity rho : ℝ) / ((23 / 5 : ℝ) * d)) =
        20930503680 * (analyticZetaZeroMultiplicity rho : ℝ) := by field_simp; ring
  have he' : (414 / 5 : ℝ) * d *
      (712249344 / ((18 / 5 : ℝ) * d) + 1507000000000 * localZetaLogHeight rho.1.im +
        2050000000 * ((18 / 5 : ℝ) * d) / rho.1.im ^ 2) =
      16381734912 + 124779600000000 * localZetaLogHeight rho.1.im * d +
        611064000000 * d ^ 2 / rho.1.im ^ 2 := by field_simp; ring
  rw [he, he'] at hmul
  dsimp only [d] at hmul
  linarith

private theorem infiniteHeight_margin_small (y : ℝ) :
    1 / (27500 * localZetaLogHeight y) < (1 / 16 : ℝ) := by
  have hL := two_lt_localZetaLogHeight y
  exact one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 16) (by linarith)

/-- The full infinite phase family proves a strict right-edge margin for
every actual nontrivial zero above absolute height one. -/
theorem infiniteHeight_margin_lt_one_sub_re (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) :
    1 / (27500 * localZetaLogHeight rho.1.im) < 1 - rho.1.re := by
  by_cases hrho : 15 / 16 ≤ rho.1.re
  · let d := 1 - rho.1.re
    let L := localZetaLogHeight rho.1.im
    have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
    have hdsmall : d ≤ 1 / 16 := by dsimp [d]; linarith
    have hL : 2 < L := two_lt_localZetaLogHeight rho.1.im
    have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
      exact_mod_cast analyticZetaZeroMultiplicity_positive rho
    have hgap := multiplicity_le_infiniteHeight_signed_zero_gap rho hrho
    change 20930503680 * (analyticZetaZeroMultiplicity rho : ℝ) - 16381734912 ≤
      124779600000000 * L * d + 611064000000 * d ^ 2 / rho.1.im ^ 2 at hgap
    have hy2 : 1 ≤ rho.1.im ^ 2 := by nlinarith [sq_abs rho.1.im]
    have hquad : d ^ 2 / rho.1.im ^ 2 ≤ L * d / 32 := by
      have hdiv : d ^ 2 / rho.1.im ^ 2 ≤ d ^ 2 := div_le_self (sq_nonneg d) hy2
      nlinarith [mul_nonneg hd.le (show 0 ≤ L - 2 by linarith)]
    by_contra hn
    have hdm : d ≤ 1 / (27500 * L) := le_of_not_gt hn
    have hprod := (le_div_iff₀ (show 0 < 27500 * L by positivity)).mp hdm
    have hquad' := mul_le_mul_of_nonneg_left hquad (by norm_num : (0 : ℝ) ≤ 611064000000)
    rw [mul_div_assoc] at hgap
    nlinarith only [hgap, hm, hquad', hprod]
  · exact (infiniteHeight_margin_small rho.1.im).trans_le (by linarith)

/-- Completion reflection gives the matching strict left-edge margin. -/
theorem infiniteHeight_margin_lt_re (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) :
    1 / (27500 * localZetaLogHeight rho.1.im) < rho.1.re := by
  have h := infiniteHeight_margin_lt_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
    (by simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_im,
      Complex.one_im, Complex.conj_im, sub_neg_eq_add, zero_add] using hy)
  simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re,
    Complex.conj_re, Complex.sub_im, Complex.one_im, Complex.conj_im,
    sub_neg_eq_add, zero_add, sub_sub_cancel] using h

/-- Every actual nontrivial zero at absolute height at least one lies
strictly inside the strip obtained from the complete infinite phase family. -/
theorem nontrivialZetaZero_mem_infiniteHeight_reciprocal_log_strip (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) :
    rho.1.re ∈ Set.Ioo (1 / (27500 * localZetaLogHeight rho.1.im))
      (1 - 1 / (27500 * localZetaLogHeight rho.1.im)) := by
  exact ⟨infiniteHeight_margin_lt_re rho hy,
    by linarith [infiniteHeight_margin_lt_one_sub_re rho hy]⟩

/-- The literal zeta function is nonzero throughout the closed right-edge
region furnished by the infinite phase family. -/
theorem riemannZeta_ne_zero_of_infiniteHeight_margin {s : ℂ} (hy : 1 ≤ |s.im|)
    (hs : 1 - 1 / (27500 * localZetaLogHeight s.im) ≤ s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith [infiniteHeight_margin_small s.im]
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hy
  have hpole : riemannZeta₁ s = 0 := by
    rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have hgap := infiniteHeight_margin_lt_one_sub_re rho hy
  change 1 / (27500 * localZetaLogHeight s.im) < 1 - s.re at hgap
  linarith

/-- The new infinite-family margin is strictly larger than the previous
five-height margin. This comparison includes the complete tail error budget. -/
theorem fiveHeight_margin_lt_infiniteHeight (y : ℝ) :
    1 / (28000 * localZetaLogHeight y) < 1 / (27500 * localZetaLogHeight y) := by
  have hL : 0 < localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)

end

end RiemannGaussian

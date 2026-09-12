/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaAngularPhaseAllowance
import RiemannGaussian.PhasePoleMargin

/-!
# The actual signed angular source bound for general phase families

An arbitrary nonnegative summable phase family with finite logarithmic
frequency cost has a complete actual zeta budget. The selected frequency
one retains its full zero multiplicity and radial correction. The real
pole and every other frequency allowance stay explicit, with infinite
support permitted and the prime inequality discharged by the full kernel.
-/

namespace RiemannGaussian.ZetaAngularPhaseFamily
noncomputable section
open Complex Filter ZetaNearOneLocalDisc ZetaNearOneJensen ZetaNearOneLogProfile
open ZetaNearOneBudgetLimit DerivativeOrderComparison ZetaAngularPhaseAllowance
open scoped Topology

/-- The actual real-axis allowance and complete oscillatory budget,
with the logarithmic frequency cost kept inside the true height sum. -/
def budget (k : ℕ) (x t : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  448 * a 0 * localZetaLogHeight 0 +
    2 * totalAllowance k x t a ω / (Real.pi * delta k)

/-- The complete normalized analytic budget and selected radial
correction at an arbitrary positive center-to-margin ratio. -/
def cost (k : ℕ) (r u t : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  u * budget k (r * u) t a ω + a 1 * (r + 1) * (u / delta k) ^ 2

/-- Every eligible finite or infinite phase family controls the actual
selected zero source. The nonnegative kernel is the original prime-power
kernel, and all analytic and convergence inputs are proved for zeta. -/
theorem source_le_budget {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 2 ≤ k) (ρ : NontrivialZetaZero) {x : ℝ}
    (ht : 2 ≤ |ρ.1.im|) (hscale : 1 ≤ scale ρ.1.im)
    (hx : 0 < x) (hx' : x ≤ delta k / 4) (hnear : x + 1 - ρ.1.re < delta k) :
    a 1 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (delta k) ^ 2) ≤
      a 0 / x + budget k x ρ.1.im a ω := by
  let D (n : ℕ) := (-logDeriv riemannZeta (center x (ω n * ρ.1.im))).re
  let S := (analyticZetaZeroMultiplicity ρ : ℝ) *
    (1 / (x + 1 - ρ.1.re) - (x + 1 - ρ.1.re) / (delta k) ^ 2)
  have hσ : 1 < 1 + x := by linarith
  have hD : Summable (fun n ↦ a n * D n) :=
    summable_zetaPhase_logDeriv (ω := ω) ha hs hσ ρ.1.im
  have hprime : 0 ≤ ∑' n, a n * D n :=
    zetaPhase_logDeriv_nonneg (ω := ω) ha hs hp hσ ρ.1.im
  have hE := summable_allowance ha hs hω hlog k hx hscale
  have hU := (hE.mul_left 2).div_const (Real.pi * delta k)
  have hsingle := (hasSum_ite_eq (1 : ℕ) (a 1 * S)).summable
  have hrealSingle :=
    (hasSum_ite_eq (0 : ℕ) (a 0 * (1 / x + 448 * localZetaLogHeight 0))).summable
  have hpoint (n : ℕ) : a n * D n + (if n = 1 then a 1 * S else 0) ≤
      (if n = 0 then a 0 * (1 / x + 448 * localZetaLogHeight 0) else 0) +
        2 * (tail a n * allowance k x (ω n * ρ.1.im)) / (Real.pi * delta k) := by
    by_cases hn0 : n = 0
    · subst n
      have hxsmall : x ≤ 1 / 4 := by
        have hd := ZetaNearOneFullDisc.delta_le_two_sevenths hk
        linarith
      have hreal := mul_le_mul_of_nonneg_left
        (neg_logDeriv_riemannZeta_real_le_local hx hxsmall) (ha 0)
      simpa [D, center, hω0, tail] using hreal
    · by_cases hn1 : n = 1
      · subst n
        have hz := mul_le_mul_of_nonneg_left
          (ZetaNearOneAngularBound.neg_logDeriv_re_le_sub_zero k hk ρ ht hx hx' hnear) (ha 1)
        simp only [D, S, hω1, one_mul, tail, if_true, if_false,
          show (1 : ℕ) ≠ 0 by norm_num, zero_add] at hz ⊢
        simp only [div_eq_mul_inv] at hz ⊢
        nlinarith only [hz]
      · have hw := hω n hn0
        have hfreq : 2 ≤ |ω n * ρ.1.im| := by
          rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ ω n)]
          nlinarith
        have hz := mul_le_mul_of_nonneg_left
          (ZetaNearOneAngularBound.neg_logDeriv_re_le k hk hfreq hx hx') (ha n)
        simp only [D, tail, hn0, hn1, if_false, add_zero, zero_add]
        simp only [div_eq_mul_inv] at hz ⊢
        nlinarith only [hz]
  have hb := (hD.add hsingle).tsum_le_tsum hpoint (hrealSingle.add hU)
  rw [hD.tsum_add hsingle, hrealSingle.tsum_add hU] at hb
  simp only [tsum_ite_eq, tsum_div_const, tsum_mul_left] at hb
  change (∑' n, a n * D n) + a 1 * S ≤
    a 0 * (1 / x + 448 * localZetaLogHeight 0) +
      2 * totalAllowance k x ρ.1.im a ω / (Real.pi * delta k) at hb
  dsimp only [S] at hb
  unfold budget
  simp only [div_eq_mul_inv] at hb ⊢
  nlinarith only [hb, hprime]

/-- An actual zero in the proposed margin forces the complete cost
to dominate the exact source-minus-pole margin for every positive
center shift and every eligible finite or infinite phase family. -/
theorem margin_le_cost_of_zero_near {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 2 ≤ k) (ρ : NontrivialZetaZero) {r u : ℝ}
    (ht : 2 ≤ |ρ.1.im|) (hscale : 1 ≤ scale ρ.1.im) (hr : 0 < r) (hu : 0 < u)
    (hsmall : 4 * (r + 1) * u < delta k) (hnear : 1 - ρ.1.re ≤ u) :
    PhasePoleMargin.margin (a 0) (a 1) r ≤ cost k r u ρ.1.im a ω := by
  let d := r * u + 1 - ρ.1.re
  have hδ := delta_pos k
  have hx : 0 < r * u := mul_pos hr hu
  have hd : 0 < d := by dsimp [d]; linarith [NontrivialZetaZero.re_lt_one ρ]
  have hdu : d ≤ (r + 1) * u := by dsimp [d]; nlinarith only [hnear]
  have hx' : r * u ≤ delta k / 4 := by nlinarith
  have hdδ : d < delta k := by nlinarith
  have hb := source_le_budget ha hs hp hω0 hω1 hω hlog k hk ρ ht hscale hx hx' hdδ
  change a 1 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / d - d / (delta k) ^ 2) ≤ a 0 / (r * u) + budget k (r * u) ρ.1.im a ω at hb
  have hspos : 0 ≤ 1 / d - d / (delta k) ^ 2 := by
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (sq_pos_of_pos hδ) hd).mpr
    nlinarith [pow_le_pow_left₀ hd.le hdδ.le 2]
  have hm : (1 : ℝ) ≤ (analyticZetaZeroMultiplicity ρ : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hmass := mul_le_mul_of_nonneg_right hm hspos
  have hi := one_div_le_one_div_of_le hd hdu
  have hrad := div_le_div_of_nonneg_right hdu (sq_nonneg (delta k))
  have hsource : 1 / ((r + 1) * u) - ((r + 1) * u) / (delta k) ^ 2 ≤
      (analyticZetaZeroMultiplicity ρ : ℝ) * (1 / d - d / (delta k) ^ 2) := by
    nlinarith only [hmass, hi, hrad]
  have hweighted := mul_le_mul_of_nonneg_left hsource (ha 1)
  have hlower : a 1 * (1 / ((r + 1) * u) - ((r + 1) * u) / (delta k) ^ 2) ≤
      a 0 / (r * u) + budget k (r * u) ρ.1.im a ω := by
    nlinarith only [hweighted, hb]
  have hmul := mul_le_mul_of_nonneg_left hlower hu.le
  have heL : u * (a 1 * (1 / ((r + 1) * u) - ((r + 1) * u) / (delta k) ^ 2)) =
      a 1 / (r + 1) - a 1 * (r + 1) * (u / delta k) ^ 2 := by
    field_simp
  have heR : u * (a 0 / (r * u) + budget k (r * u) ρ.1.im a ω) =
      a 0 / r + u * budget k (r * u) ρ.1.im a ω := by
    field_simp
  rw [heL, heR] at hmul
  unfold PhasePoleMargin.margin cost
  linarith

end
end RiemannGaussian.ZetaAngularPhaseFamily

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughSquarefreeBareFilter
import RiemannGaussian.ZetaSignedPoleZeroFree
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# The actual squarefree Euler response

The convergent squarefree arithmetic series is the quotient zeta(s)/zeta(2s).
Keeping this quotient replaces the absolute prime-square product in the
analytic continuation argument. The genuine squarefree coefficients and
the original logarithmic moment kernels remain available throughout.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Topology
open scoped Classical LSeries.notation

/-- The analytic expression for the complete unmarked squarefree
response. Its Dirichlet-series identity is proved in the Euler half-plane. -/
def squarefreeEulerResponse (s : ℂ) : ℂ := riemannZeta s / riemannZeta (2 * s)

private theorem squarefree_euler_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ 1 + (p : ℂ) ^ (-s))
      (∑' n : ℕ, if Squarefree n then (n : ℂ) ^ (-s) else 0) := by
  let g := riemannZetaSummandHom (ne_zero_of_one_lt_re hs)
  let f : ℕ → ℂ := fun n ↦ if Squarefree n then g n else 0
  have hsum : Summable (fun n ↦ ‖f n‖) := by
    apply (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    intro n
    dsimp [f, g]
    split_ifs <;> simp
  have h1 : f 1 = 1 := by simp [f]
  have h0 : f 0 = 0 := by simp [f]
  have hmul {m n : ℕ} (hc : m.Coprime n) : f (m * n) = f m * f n := by
    simp only [f, Nat.squarefree_mul hc, map_mul]
    split_ifs <;> simp_all
  have h := EulerProduct.eulerProduct_hasProd h1 (fun {_ _} hc ↦ hmul hc) hsum h0
  have hlocal (p : Nat.Primes) : (∑' k : ℕ, f (p.val ^ k)) = 1 + (p : ℂ) ^ (-s) := by
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [f, Finset.sum_range_succ, p.property.squarefree, g, riemannZetaSummandHom]
    · intro k hk
      have hk2 : 2 ≤ k := by simp only [Finset.mem_range] at hk; omega
      have hsf : ¬Squarefree (p.val ^ k) := by
        rw [Nat.squarefree_pow_iff p.property.ne_one (by omega)]
        omega
      simp [f, hsf]
  simp only [hlocal] at h
  exact h

private theorem prime_inverse_factor_mul {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    (1 + (p : ℂ) ^ (-s)) * (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ =
      (1 - (p : ℂ) ^ (-s))⁻¹ := by
  have hp := (summable_riemannZetaSummand hs).of_norm.norm_lt_one
    (f := (riemannZetaSummandHom (ne_zero_of_one_lt_re hs)).toMonoidHom) p.property.one_lt
  change ‖(p : ℂ) ^ (-s)‖ < 1 at hp
  have hminus : 1 - (p : ℂ) ^ (-s) ≠ 0 := by
    intro he
    have hpow : (p : ℂ) ^ (-s) = 1 := sub_eq_zero.mp he |>.symm
    simp [hpow] at hp
  have hplus : 1 + (p : ℂ) ^ (-s) ≠ 0 := by
    intro he
    have hpow : (p : ℂ) ^ (-s) = -1 := by linear_combination he
    simp [hpow] at hp
  have he : (p : ℂ) ^ (-(2 * s)) = ((p : ℂ) ^ (-s)) ^ 2 := by
    rw [show -(2 * s) = -s + -s by ring,
      Complex.cpow_add _ _ (by exact_mod_cast p.property.ne_zero), pow_two]
  rw [he, show 1 - ((p : ℂ) ^ (-s)) ^ 2 =
    (1 + (p : ℂ) ^ (-s)) * (1 - (p : ℂ) ^ (-s)) by ring, mul_inv_rev]
  field_simp

/-- The full squarefree Dirichlet series has this exact quotient,
including its genuine convergence. No assertion of series convergence
to the left of the Euler half-plane is made. -/
theorem LSeriesHasSum_squarefreeEuler {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (RoughSquarefreeBare.coefficient ∅ 1) s (squarefreeEulerResponse s) := by
  have hs2 : 1 < (2 * s).re := by norm_num; linarith
  have hsum : Summable (fun n : ℕ ↦ if Squarefree n then (n : ℂ) ^ (-s) else 0) := by
    apply ((summable_riemannZetaSummand hs).of_norm.indicator {n | Squarefree n}).congr
    intro n
    by_cases hn : Squarefree n
    · rw [Set.indicator_of_mem hn, if_pos hn]
      rfl
    · rw [Set.indicator_of_notMem hn, if_neg hn]
  have hprod := (squarefree_euler_hasProd hs).mul (riemannZeta_eulerProduct_hasProd hs2)
  simp only [prime_inverse_factor_mul hs] at hprod
  have he := hprod.unique (riemannZeta_eulerProduct_hasProd hs)
  have hz := riemannZeta_ne_zero_of_one_lt_re hs2
  have hvalue : (∑' n : ℕ, if Squarefree n then (n : ℂ) ^ (-s) else 0) =
      squarefreeEulerResponse s := by
    unfold squarefreeEulerResponse
    exact (eq_div_iff hz).mpr he
  rw [← hvalue]
  apply hsum.hasSum.congr_fun
  intro n
  by_cases hn : n = 0
  · simp [hn, LSeries.term]
  · by_cases hsf : Squarefree n <;>
      simp [LSeries.term_of_ne_zero hn, RoughSquarefreeBare.coefficient, Complex.cpow_neg, hsf]

/-- The convergent product of the literal squarefree local Euler factors
has the same quotient value as the genuine arithmetic series. -/
theorem hasProd_squarefreeEuler {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ 1 + (p : ℂ) ^ (-s)) (squarefreeEulerResponse s) := by
  convert squarefree_euler_hasProd hs using 1
  rw [← (LSeriesHasSum_squarefreeEuler hs).LSeries_eq, LSeries]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, LSeries.term]
  · by_cases hsf : Squarefree n <;>
      simp [LSeries.term_of_ne_zero hn, RoughSquarefreeBare.coefficient, Complex.cpow_neg, hsf]

/-- The proved edge width decreases as the absolute ordinate grows. -/
theorem zetaSignedPoleZeroMargin_antitone_abs {a b : ℝ} (h : |a| ≤ |b|) :
    zetaSignedPoleZeroMargin b ≤ zetaSignedPoleZeroMargin a := by
  have hlog := Real.log_le_log (by positivity : 0 < |a| + 2)
    (by linarith : |a| + 2 ≤ |b| + 2)
  unfold zetaSignedPoleZeroMargin
  exact div_le_div_of_nonneg_left (by norm_num) (zetaSignedPole_denominator_pos a) (by linarith)

/-- An explicit Cauchy radius beyond one. It uses the actual proved
zero-free width at twice the largest possible ordinate in the disc. -/
def squarefreeEulerRadius (y : ℝ) : ℝ :=
  1 + min ((|y| - 1) / 2) (zetaSignedPoleZeroMargin (2 * |y| + 3) / 4)

/-- The radius is strictly beyond one, avoids both zeta poles, and
stays within the zero-free allowance for the doubled argument. -/
theorem squarefreeEulerRadius_bounds {y : ℝ} (hy : 1 < |y|) :
    1 < squarefreeEulerRadius y ∧ squarefreeEulerRadius y < |y| ∧
      squarefreeEulerRadius y < 17 / 16 ∧
      4 * (squarefreeEulerRadius y - 1) ≤ zetaSignedPoleZeroMargin (2 * |y| + 3) := by
  have hm := zetaSignedPoleZeroMargin_pos (2 * |y| + 3)
  have hmu := zetaSignedPoleZeroMargin_lt_one_quarter (2 * |y| + 3)
  have hmin : 0 < min ((|y| - 1) / 2) (zetaSignedPoleZeroMargin (2 * |y| + 3) / 4) := by
    exact lt_min (by linarith) (by positivity)
  have hleft := min_le_left ((|y| - 1) / 2) (zetaSignedPoleZeroMargin (2 * |y| + 3) / 4)
  have hright := min_le_right ((|y| - 1) / 2) (zetaSignedPoleZeroMargin (2 * |y| + 3) / 4)
  unfold squarefreeEulerRadius
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The entire enlarged closed disc avoids the pole of zeta and every
zero or pole of the doubled zeta denominator. The zero-free edge theorem
is applied to the actual doubled argument, not to an Euler-product proxy. -/
theorem squarefreeEuler_disc_safe {y : ℝ} (hy : 1 < |y|) {s : ℂ}
    (hs : s ∈ Metric.closedBall (3 / 2 + I * y) (squarefreeEulerRadius y)) :
    s ≠ 1 ∧ 2 * s ≠ 1 ∧ riemannZeta (2 * s) ≠ 0 := by
  obtain ⟨hr, hry, hru, hmargin⟩ := squarefreeEulerRadius_bounds hy
  have hre := (Complex.abs_re_le_norm (s - (3 / 2 + I * y))).trans
    (mem_closedBall_iff_norm.mp hs)
  have him := (Complex.abs_im_le_norm (s - (3 / 2 + I * y))).trans
    (mem_closedBall_iff_norm.mp hs)
  norm_num at hre him
  have him0 : s.im ≠ 0 := by
    intro h
    simp only [h, zero_sub, abs_neg] at him
    linarith
  have hs1 : s ≠ 1 := by intro h; apply him0; simp [h]
  have hs2 : 2 * s ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
    exact him0 (by linarith)
  have himBound : |s.im| ≤ |y| + squarefreeEulerRadius y := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp him).1, (abs_le.mp him).2, le_abs_self y, neg_abs_le y]
  have harg : |(2 * s).im| ≤ |2 * |y| + 3| := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * |y| + 3)]
    norm_num [abs_mul]
    linarith
  have hwidth := zetaSignedPoleZeroMargin_antitone_abs harg
  have hedge : 1 - zetaSignedPoleZeroMargin (2 * s).im ≤ (2 * s).re := by
    norm_num at hwidth ⊢
    have hM := zetaSignedPoleZeroMargin_pos (2 * |y| + 3)
    nlinarith [(abs_le.mp hre).1]
  exact ⟨hs1, hs2, riemannZeta_ne_zero_of_signedPole_margin hs2 hedge⟩

/-- The genuine squarefree response is analytic on a neighbourhood of
the enlarged closed disc, including points to the left of one half. -/
theorem analyticOnNhd_squarefreeEulerResponse {y : ℝ} (hy : 1 < |y|) :
    AnalyticOnNhd ℂ squarefreeEulerResponse
      (Metric.closedBall (3 / 2 + I * y) (squarefreeEulerRadius y)) := by
  intro s hs
  obtain ⟨hs1, hs2, hz⟩ := squarefreeEuler_disc_safe hy hs
  have hnum := analyticOn_riemannZeta s (by simpa using hs1)
  have hden := (analyticOn_riemannZeta (2 * s) (by simpa using hs2)).comp
    (analyticAt_const.mul analyticAt_id)
  exact hnum.div hden hz

/-- The original squarefree coefficient series converges absolutely
throughout the Euler half-plane. This controls every logarithmic moment
before the quotient is continued to the larger analytic disc. -/
theorem abscissaOfAbsConv_squarefreeEuler_le_one :
    LSeries.abscissaOfAbsConv (RoughSquarefreeBare.coefficient ∅ 1) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
  intro y hy
  exact (LSeriesHasSum_squarefreeEuler (by simpa using hy)).LSeriesSummable

/-- Every factorial moment of the quotient is the genuine convergent
sum of the original squarefree coefficients with their full complex phase. -/
theorem hasSum_squarefreeEuler_moment (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ RoughSquarefreeBare.coefficient ∅ 1 n *
      ((Real.log n : ℂ) ^ N / (N.factorial : ℂ)) * zetaPrimeFeature s n)
      (signedTaylorMoment N squarefreeEulerResponse s) := by
  have he : squarefreeEulerResponse =ᶠ[𝓝 s] LSeries (RoughSquarefreeBare.coefficient ∅ 1) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact (LSeriesHasSum_squarefreeEuler hz).LSeries_eq.symm
  rw [signedTaylorMoment_congr N he]
  exact hasSum_signedTaylorMoment_LSeries _ (by simp [RoughSquarefreeBare.coefficient])
    (lt_of_le_of_lt abscissaOfAbsConv_squarefreeEuler_le_one (by exact_mod_cast hs)) N

/-- The complete original polynomial filter equals the quotient's
finite moment combination. Coefficient signs and all phases are unchanged. -/
theorem hasSum_squarefreeEuler_filter (p : Polynomial ℂ) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ RoughSquarefreeBare.coefficient ∅ 1 n * zetaPrimeFilterKernel p N s n)
      (zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k squarefreeEulerResponse s) N) := by
  have h := hasSum_sum (s := p.support) (fun k _ ↦
    (hasSum_squarefreeEuler_moment (N + k) hs).mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ ↦ by ring)

/-- The quotient controls every bounded analytic multiplier on the
larger disc. Its constant is independent of the multiplier, moment and
polynomial; the full polynomial coefficient envelope is retained. -/
theorem exists_squarefreeEuler_multiplier_filter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ),
      AnalyticOnNhd ℂ f (Metric.closedBall (3 / 2 + I * y) (squarefreeEulerRadius y)) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ s ∈ Metric.closedBall (3 / 2 + I * y) (squarefreeEulerRadius y), ‖f s‖ ≤ A) →
      ∀ (p : Polynomial ℂ) (N : ℕ),
        ‖zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k
          (fun s ↦ f s * squarefreeEulerResponse s) (3 / 2 + I * y)) N‖ ≤
          C * A * (squarefreeEulerRadius y)⁻¹ ^ N *
            ∑ k ∈ p.support, ‖p.coeff k‖ * (squarefreeEulerRadius y)⁻¹ ^ k := by
  let c : ℂ := 3 / 2 + I * y
  let r := squarefreeEulerRadius y
  have hr : 0 < r := zero_lt_one.trans (squarefreeEulerRadius_bounds hy).1
  have hQ := analyticOnNhd_squarefreeEulerResponse hy
  obtain ⟨M, hM⟩ := ((isCompact_closedBall c r).image_of_continuousOn
    hQ.continuousOn.norm).isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ ⟨c, Metric.mem_closedBall_self hr.le, rfl⟩)
  refine ⟨M + 1, by linarith, ?_⟩
  intro f hf A hA hfA p N
  have ha : AnalyticOnNhd ℂ (fun s ↦ f s * squarefreeEulerResponse s) (Metric.closedBall c r) :=
    fun s hs ↦ (hf s hs).mul (hQ s hs)
  have hd : DiffContOnCl ℂ (fun s ↦ f s * squarefreeEulerResponse s) (Metric.ball c r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    exact ha.differentiableOn
  have hb (s : ℂ) (hs : s ∈ Metric.sphere c r) :
      ‖f s * squarefreeEulerResponse s‖ ≤ (M + 1) * A := by
    have hsB := Metric.sphere_subset_closedBall hs
    have hbound := hM _ ⟨s, hsB, rfl⟩
    rw [Real.norm_of_nonneg (norm_nonneg _)] at hbound
    rw [norm_mul]
    have h := mul_le_mul (hfA s hsB) (show ‖squarefreeEulerResponse s‖ ≤ M + 1 by linarith)
      (norm_nonneg _) hA
    simpa only [mul_comm] using h
  have hmoment (k : ℕ) :
      ‖signedTaylorMoment k (fun s ↦ f s * squarefreeEulerResponse s) c‖ ≤
        (M + 1) * A * r⁻¹ ^ k := by
    simpa only [div_eq_mul_inv, inv_pow] using norm_signedTaylorMoment_le hr hd hb k
  rw [zetaMomentSequenceFilter, Polynomial.sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * ((M + 1) * A * r⁻¹ ^ (N + k)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hmoment (N + k)) (norm_nonneg _)
    _ = _ := by
      simp_rw [pow_add, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ ↦ by ring)

/-- The actual complete unmarked squarefree filter decays geometrically
before any selected-zero normalization. The radius is strictly greater
than one and the bound works for every complex polynomial. -/
theorem exists_squarefreeEuler_filter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (N : ℕ),
      ‖RoughSquarefreeBare.response p ∅ 1 N (3 / 2 + I * y)‖ ≤
        C * (squarefreeEulerRadius y)⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * (squarefreeEulerRadius y)⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_squarefreeEuler_multiplier_filter_bound y hy
  refine ⟨C, hC, fun p N ↦ ?_⟩
  have h := hb (fun _ ↦ 1) (fun _ _ ↦ analyticAt_const) 1 (by norm_num)
    (fun _ _ ↦ by simp) p N
  simp only [one_mul, mul_one] at h
  rw [RoughSquarefreeBare.response, (hasSum_squarefreeEuler_filter p N (by norm_num)).tsum_eq]
  exact h

/-- In particular the complete original squarefree arithmetic filter
tends to zero at every fixed nonzero eligible height, with no zeta-zero
hypothesis and no coefficient-dependent choice of the Cauchy radius. -/
theorem tendsto_squarefreeEuler_filter (y : ℝ) (hy : 1 < |y|) (p : Polynomial ℂ) :
    Tendsto (fun N ↦ RoughSquarefreeBare.response p ∅ 1 N (3 / 2 + I * y)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_squarefreeEuler_filter_bound y hy
  let B := ∑ k ∈ p.support, ‖p.coeff k‖ * (squarefreeEulerRadius y)⁻¹ ^ k
  have hr := (squarefreeEulerRadius_bounds hy).1
  have hpos : 0 ≤ (squarefreeEulerRadius y)⁻¹ := by positivity
  have hlt : (squarefreeEulerRadius y)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  apply squeeze_zero_norm (fun N ↦ hb p N)
  simpa only [mul_zero, zero_mul] using
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hpos hlt).const_mul C).mul_const B

end
end RiemannGaussian

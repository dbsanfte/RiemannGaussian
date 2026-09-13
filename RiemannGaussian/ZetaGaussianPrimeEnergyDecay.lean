/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerPoissonDifference
import RiemannGaussian.ZetaGaussianPrimeEnergyBound

/-!
# Ordinary-prime energy decay at logarithmic dilation

The actual log-log zero-free region gives an arbitrarily small logarithmic
coefficient for the signed Euler response. Its affine global version passes
through the complete Gaussian average, uniformly in every dilation at least
one. Combining this response with the actual total-mass cap before squaring
requires only the first logarithmic frequency moment, even for infinite families.

The normalized complete ordinary-prime energy now tends to zero when absolute
height tends to infinity and logarithmic height divided by dilation is bounded.
The current explicit-region dilation satisfies this condition. The complete
auxiliary allowance and the actual positive squared source surplus over its
original signed boundary budget have the same normalized vanishing limit.
The signed boundary budget remains; no RH contradiction or new region follows
from this slice. All small-coefficient height thresholds are unevaluated.
-/

namespace RiemannGaussian.ZetaGaussianPrimeEnergyDecay
noncomputable section
open Complex Filter MeasureTheory
open GaussianVerticalAverage ZetaGaussianScaledBandBudget
open ZetaGaussianPrimeEnergyBound ZetaGaussianPrimeReduction ZetaAngularPhaseAllowance
open scoped Topology

/-- The affine small-coefficient Euler bound passes through the complete complex Gaussian average with its exact first absolute moment. -/
theorem abs_regularMean_re_le_affine {ε K B x : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 3 →
      |(logDeriv riemannZeta₁ ((σ : ℂ) + I * t)).re| ≤ ε * zetaEulerLogHeight t + K)
    (hB : 0 < B) (hx : 0 < x) (hx2 : x ≤ 2) (t : ℝ) :
    |(regularMean B x t).re| ≤
      ε * (zetaEulerLogHeight t + 4 * B / GaussianPolynomialTransport.mass B) + K := by
  have hi := integrable_regularMean hB hx t
  have hm := ((integrable_density hB).mul_const (ε * zetaEulerLogHeight t + K)).add
    ((ZetaGaussianCompletionAverage.integrable_density_abs hB).const_mul ε)
  rw [regularMean, average_re hi]
  calc
    _ ≤ ∫ y : ℝ, |density B y *
        (logDeriv riemannZeta₁ (((1 + x : ℝ) : ℂ) + I * (t - y))).re| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y : ℝ, density B y * (ε * zetaEulerLogHeight t + K) +
        ε * (density B y * |y|) := by
      apply integral_mono_ae (by
        simpa only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, Real.norm_eq_abs] using hi.re.norm) hm
      filter_upwards with y
      rw [abs_mul, abs_of_pos (density_pos hB y)]
      have hb := hbound (1 + x) (t - y) (by linarith) (by linarith)
      have hl := mul_le_mul_of_nonneg_left (logHeight_sub_le t y) hε
      simp only [Complex.ofReal_sub] at hb
      dsimp only [Pi.add_apply]
      nlinarith only [mul_le_mul_of_nonneg_left hb (density_pos hB y).le,
        mul_le_mul_of_nonneg_left hl (density_pos hB y).le]
    _ = _ := by
      rw [integral_add ((integrable_density hB).mul_const _)
        ((ZetaGaussianCompletionAverage.integrable_density_abs hB).const_mul ε),
        integral_mul_const, integral_const_mul, integral_density hB,
        ZetaGaussianCompletionAverage.integral_density_abs hB]
      ring

/-- Every positive logarithmic coefficient eventually bounds the complete ordinary-prime cosine response, uniformly in every dilation at least one. The Euler, Gaussian and proper-prime-power inputs are all discharged. -/
theorem exists_uniform_prime_small_log_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ q t : ℝ, 1 ≤ q → T ≤ |t| →
      |primeCosine q t| ≤ ε * zetaEulerLogHeight t := by
  obtain ⟨K, _, hb⟩ := ZetaEulerPoissonDifference.exists_affine_small_log_bound (half_pos hε)
  let R := allowance + 13 + ε / 2 + K
  refine ⟨max 2 (Real.exp (2 * R / ε)), le_max_left _ _, ?_⟩
  intro q t hq ht
  have ht1 : 1 ≤ |t| := by linarith [le_max_left (2 : ℝ) (Real.exp (2 * R / ε))]
  have hx := (shift_bounds hq).1
  have hx2 : shift q ≤ 2 := by
    have hh := (shift_bounds hq).2
    norm_num [GaussianStripProfile.shift, GaussianStripProfile.width] at hh
    linarith
  have hr := abs_regularMean_re_le_affine (half_pos hε).le hb
    (gaussianScale_bounds hq).1 hx hx2 t
  have hm := completion_le hq
  have hg : |GaussianFermiPrimeComparison.ordinarySum (1 + shift q) (gaussianScale q) t| ≤
      13 + ε / 2 * (zetaEulerLogHeight t + 1) + K := by
    rw [← ZetaGaussianPrimeAverage.primeSum_re (by linarith : 2 / 3 < 1 + shift q)
      le_rfl (gaussianScale_bounds hq).1,
      primeSum_eq_transform_sub_regularMean (gaussianScale_bounds hq).1 hx, Complex.sub_re]
    have hh := abs_sub (GaussianComplexHalfMoments.transform (gaussianScale q)
      ((shift q : ℂ) + I * t)).re (regularMean (gaussianScale q) (shift q) t).re
    have hp := (Complex.abs_re_le_norm _).trans (norm_transform_le_thirteen hq ht1)
    nlinarith
  have hp := abs_primeCosine_sub_gaussian_le hq t
  have ht' := abs_add_le (primeCosine q t -
    GaussianFermiPrimeComparison.ordinarySum (1 + shift q) (gaussianScale q) t)
    (GaussianFermiPrimeComparison.ordinarySum (1 + shift q) (gaussianScale q) t)
  rw [sub_add_cancel] at ht'
  have hlog := Real.log_le_log (Real.exp_pos (2 * R / ε)) ((le_max_right _ _).trans ht)
  rw [Real.log_exp] at hlog
  have hl : Real.log |t| ≤ zetaEulerLogHeight t :=
    Real.log_le_log (by linarith) (by linarith)
  have hR := (div_le_iff₀ hε).mp (hlog.trans hl)
  dsimp only [R] at hR
  linarith

/-- One fixed positive Euler-mass constant gives every small logarithmic energy coefficient above its own threshold, uniformly over all eligible countable families and dilations. Only the first logarithmic frequency moment is required. -/
theorem exists_uniform_energy_small_log_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 2 ≤ T ∧ ∀ (a ω : ℕ → ℝ),
        (∀ n, 0 ≤ a n) → Summable a → (∀ n, n ≠ 0 → 1 ≤ ω n) →
        Summable (fun n => tail a n * Real.log (ω n)) → ∀ q t : ℝ,
        1 ≤ q → T ≤ |t| → fullEnergy a ω q t ≤
          D * ε * q * (mass a * zetaEulerLogHeight t + frequencyCost a ω) := by
  obtain ⟨D, _, hD, _, hb⟩ := exists_prime_bounds
  refine ⟨D, hD, ?_⟩
  intro ε hε
  obtain ⟨T, hT, ht⟩ := exists_uniform_prime_small_log_bound hε
  refine ⟨T, hT, ?_⟩
  intro a ω ha hs hω hlog q t hq htt
  have hq0 : 0 < q := by linarith
  have hu (n : ℕ) : tail a n * (primeCosine q (ω n * t)) ^ 2 ≤
      tail a n * (D * ε * q * zetaEulerLogHeight t) +
        (tail a n * Real.log (ω n)) * (D * ε * q) := by
    by_cases hn : n = 0
    · simp [tail, hn]
    have hω0 : 0 < ω n := by linarith [hω n hn]
    have htt' : T ≤ |ω n * t| := by
      rw [abs_mul, abs_of_pos hω0]
      nlinarith [hω n hn, abs_nonneg t]
    have hsmall := ht q (ω n * t) hq htt'
    have hheight := mul_le_mul_of_nonneg_left (logHeight_mul_le (hω n hn) t) hε.le
    have hcap := (hb q (ω n * t) hq).1
    have he := mul_le_mul hcap (hsmall.trans hheight)
      (abs_nonneg (primeCosine q (ω n * t))) (show 0 ≤ D * q by positivity)
    rw [← sq, sq_abs] at he
    nlinarith only [mul_le_mul_of_nonneg_left he (tail_nonneg ha n)]
  have hh := (summable_fullEnergy ha hs hq t).tsum_le_tsum hu
    (((tail_summable ha hs).mul_right _).add (hlog.mul_right _))
  have he := ((tail_summable ha hs).hasSum.mul_right (D * ε * q * zetaEulerLogHeight t)).add
    (hlog.hasSum.mul_right (D * ε * q))
  have hh' := hh.trans_eq he.tsum_eq
  change fullEnergy a ω q t ≤ mass a * (D * ε * q * zetaEulerLogHeight t) +
    frequencyCost a ω * (D * ε * q) at hh'
  nlinarith only [hh']

/-- The normalized complete energy tends to zero for moving countable families of bounded mass and first logarithmic frequency cost, when absolute height diverges and its logarithmic ratio to dilation stays bounded. -/
theorem tendsto_normalized_fullEnergy_of_bounded_height_ratio
    (a ω : ℕ → ℕ → ℝ) (q t : ℕ → ℝ)
    (ha : ∀ N n, 0 ≤ a N n) (hs : ∀ N, Summable (a N))
    (hω : ∀ N n, n ≠ 0 → 1 ≤ ω N n)
    (hlog : ∀ N, Summable (fun n => tail (a N) n * Real.log (ω N n)))
    (hq : ∀ N, 1 ≤ q N) (ht : Tendsto (fun N => |t N|) atTop atTop)
    (A F C : ℝ) (hA : ∀ N, mass (a N) ≤ A)
    (hF : ∀ N, frequencyCost (a N) (ω N) ≤ F)
    (hC : ∀ N, zetaEulerLogHeight (t N) / q N ≤ C) :
    Tendsto (fun N => fullEnergy (a N) (ω N) (q N) (t N) / (q N) ^ 2) atTop (𝓝 0) := by
  obtain ⟨D, hD, hb⟩ := exists_uniform_energy_small_log_bound
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall (fun N => hb.trans_le
      (div_nonneg (tsum_nonneg (fun n =>
        mul_nonneg (tail_nonneg (ha N) n) (sq_nonneg _))) (sq_nonneg _)))
  · intro b hb0
    let R := |A| * |C| + |F| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    let ε := b / (2 * D * R)
    have hε : 0 < ε := by dsimp [ε]; positivity
    obtain ⟨T, _, hT⟩ := hb ε hε
    filter_upwards [ht.eventually (eventually_ge_atTop T)] with N hNt
    have hq0 : 0 < q N := by linarith [hq N]
    have he := hT (a N) (ω N) (ha N) (hs N) (hω N) (hlog N) (q N) (t N) (hq N) hNt
    have hL : 0 ≤ zetaEulerLogHeight (t N) / q N :=
      div_nonneg (by linarith [three_lt_zetaEulerLogHeight (t N)]) hq0.le
    have hm := mul_le_mul ((hA N).trans (le_abs_self A))
      ((hC N).trans (le_abs_self C)) hL (abs_nonneg A)
    have hf : frequencyCost (a N) (ω N) / q N ≤ |F| := by
      apply (div_le_iff₀ hq0).mpr
      have hmul := mul_le_mul_of_nonneg_left (hq N) (abs_nonneg F)
      linarith [hF N, le_abs_self F]
    have hsum : mass (a N) * (zetaEulerLogHeight (t N) / q N) +
        frequencyCost (a N) (ω N) / q N ≤ R := by dsimp [R]; linarith
    have hu : fullEnergy (a N) (ω N) (q N) (t N) / (q N) ^ 2 ≤ b / 2 := by
      calc
        _ ≤ (D * ε * q N * (mass (a N) * zetaEulerLogHeight (t N) +
            frequencyCost (a N) (ω N))) / (q N) ^ 2 :=
          div_le_div_of_nonneg_right he (sq_nonneg _)
        _ = D * ε * (mass (a N) * (zetaEulerLogHeight (t N) / q N) +
            frequencyCost (a N) (ω N) / q N) := by field_simp
        _ ≤ D * ε * R := mul_le_mul_of_nonneg_left hsum (mul_nonneg hD.le hε.le)
        _ = b / 2 := by dsimp [ε]; field_simp
    linarith

/-- The current dilation bounds the enlarged Euler logarithmic height ratio by 320000 plus log 13. The distinct height smoothings are retained exactly. -/
theorem current_dilation_height_ratio_upper (t : ℝ) :
    zetaEulerLogHeight t / ZetaGaussianAllHeight.dilation t ≤ 320000 + Real.log 13 := by
  have hq : 1 ≤ ZetaGaussianAllHeight.dilation t := le_max_left _ _
  have hq0 : 0 < ZetaGaussianAllHeight.dilation t := by linarith
  have h13 : 0 ≤ Real.log (13 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : zetaEulerLogHeight t ≤ ZetaNearOneBudgetLimit.scale t + Real.log 13 := by
    have h := Real.log_le_log (by positivity : 0 < |t| + 26)
      (show |t| + 26 ≤ 13 * (|t| + 2) by nlinarith [abs_nonneg t])
    rw [Real.log_mul (by norm_num : (13 : ℝ) ≠ 0) (by positivity)] at h
    simpa only [zetaEulerLogHeight, ZetaNearOneBudgetLimit.scale,
      ZetaNearOneLogProfile.height, add_comm] using h
  apply (div_le_iff₀ hq0).mpr
  have hscale := ZetaGaussianAllHeight.scale_le_dilation t
  have hm := mul_le_mul_of_nonneg_left hq h13
  nlinarith

/-- The complete ordinary Gaussian-prime energy divided by squared current-region dilation tends to zero at large absolute height, for every moving eligible family with bounded mass and first logarithmic frequency cost. -/
theorem tendsto_current_dilation_fullEnergy
    (a ω : ℕ → ℕ → ℝ) (t : ℕ → ℝ)
    (ha : ∀ N n, 0 ≤ a N n) (hs : ∀ N, Summable (a N))
    (hω : ∀ N n, n ≠ 0 → 1 ≤ ω N n)
    (hlog : ∀ N, Summable (fun n => tail (a N) n * Real.log (ω N n)))
    (ht : Tendsto (fun N => |t N|) atTop atTop)
    (A F : ℝ) (hA : ∀ N, mass (a N) ≤ A) (hF : ∀ N, frequencyCost (a N) (ω N) ≤ F) :
    Tendsto (fun N => fullEnergy (a N) (ω N) (ZetaGaussianAllHeight.dilation (t N)) (t N) /
      (ZetaGaussianAllHeight.dilation (t N)) ^ 2) atTop (𝓝 0) := by
  exact tendsto_normalized_fullEnergy_of_bounded_height_ratio a ω _ t ha hs hω hlog
    (fun _ => le_max_left _ _) ht A F (320000 + Real.log 13) hA hF
    (fun N => current_dilation_height_ratio_upper (t N))

/-- The actual current-region dilation diverges whenever the absolute height does. -/
theorem current_dilation_tendsto (t : ℕ → ℝ)
    (ht : Tendsto (fun N => |t N|) atTop atTop) :
    Tendsto (fun N => ZetaGaussianAllHeight.dilation (t N)) atTop atTop := by
  have hs : Tendsto (fun N => ZetaNearOneBudgetLimit.scale (t N)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_mono (fun N => show |t N| ≤ |t N| + 2 by linarith) ht)
  exact tendsto_atTop_mono (fun N => le_max_right _ _)
    (hs.atTop_div_const (by norm_num : (0 : ℝ) < 320000))

/-- The entire right side of the actual squared source constraint, including all auxiliary and mixed-term allowances, vanishes after division by squared current dilation. -/
theorem tendsto_current_source_cost
    (a ω : ℕ → ℕ → ℝ) (t : ℕ → ℝ)
    (ha : ∀ N n, 0 ≤ a N n) (hs : ∀ N, Summable (a N))
    (hω : ∀ N n, n ≠ 0 → 1 ≤ ω N n)
    (hlog : ∀ N, Summable (fun n => tail (a N) n * Real.log (ω N n)))
    (ht : Tendsto (fun N => |t N|) atTop atTop)
    (A F : ℝ) (hA : ∀ N, mass (a N) ≤ A) (hF : ∀ N, frequencyCost (a N) (ω N) ≤ F) :
    Tendsto (fun N =>
      ((1 + 1 / ZetaGaussianAllHeight.dilation (t N)) * mass (a N) *
        fullEnergy (a N) (ω N) (ZetaGaussianAllHeight.dilation (t N)) (t N) +
          energyAllowance (ZetaGaussianAllHeight.dilation (t N)) (mass (a N))) /
            (ZetaGaussianAllHeight.dilation (t N)) ^ 2) atTop (𝓝 0) := by
  let q := fun N => ZetaGaussianAllHeight.dilation (t N)
  have hq (N : ℕ) : 1 ≤ q N := le_max_left _ _
  have hm (N : ℕ) : 0 ≤ mass (a N) := tsum_nonneg (tail_nonneg (ha N))
  have he := tendsto_current_dilation_fullEnergy a ω t ha hs hω hlog ht A F hA hF
  have hr := tendsto_normalized_energyAllowance q (fun N => mass (a N)) hq
    (current_dilation_tendsto t ht) hm A hA
  have hlim : Tendsto (fun N => 2 * |A| *
      (fullEnergy (a N) (ω N) (q N) (t N) / (q N) ^ 2) +
        energyAllowance (q N) (mass (a N)) / (q N) ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (he.const_mul (2 * |A|)).add hr
  apply squeeze_zero _ _ hlim
  · intro N
    have hmN := hm N
    have hQ : 0 ≤ fullEnergy (a N) (ω N) (q N) (t N) :=
      tsum_nonneg (fun n => mul_nonneg (tail_nonneg (ha N) n) (sq_nonneg _))
    have hq0 : 0 < q N := by linarith [hq N]
    change 0 ≤ ((1 + 1 / q N) * mass (a N) * fullEnergy (a N) (ω N) (q N) (t N) +
      energyAllowance (q N) (mass (a N))) / (q N) ^ 2
    unfold energyAllowance
    positivity
  · intro N
    have hq0 : 0 < q N := by linarith [hq N]
    have hi : 1 + 1 / q N ≤ 2 := by
      have hh := (div_le_one hq0).mpr (hq N)
      linarith
    have hmult := mul_le_mul hi ((hA N).trans (le_abs_self A)) (hm N) (by norm_num : (0 : ℝ) ≤ 2)
    have hQ : 0 ≤ fullEnergy (a N) (ω N) (q N) (t N) / (q N) ^ 2 :=
      div_nonneg (tsum_nonneg (fun n => mul_nonneg (tail_nonneg (ha N) n) (sq_nonneg _)))
        (sq_nonneg _)
    change ((1 + 1 / q N) * mass (a N) * fullEnergy (a N) (ω N) (q N) (t N) +
      energyAllowance (q N) (mass (a N))) / (q N) ^ 2 ≤ _
    rw [add_div, mul_div_assoc]
    linarith only [mul_le_mul_of_nonneg_right hmult hQ]

open ZetaStripEulerConstraint

/-- The actual positive squared finite-zero source surplus over the original signed boundary budget has vanishing normalized limit at the current dilation. Arbitrary moving finite zero windows, multiplicities, families and clipping depths remain; the signed budget is not bounded here. -/
theorem tendsto_current_source_surplus_sq
    (a ω : ℕ → ℕ → ℝ) (t M : ℕ → ℝ) (Z : ℕ → Finset NontrivialZetaZero)
    (ha : ∀ N n, 0 ≤ a N n) (hs : ∀ N, Summable (a N))
    (hP : ∀ N u, 0 ≤ zetaPhaseKernel (a N) (ω N) u)
    (hω0 : ∀ N, ω N 0 = 0) (hω1 : ∀ N, ω N 1 = 1)
    (hω : ∀ N n, n ≠ 0 → 1 ≤ ω N n)
    (hlog : ∀ N, Summable (fun n => tail (a N) n * Real.log (ω N n)))
    (hM : ∀ N, 0 ≤ M N) (hscale : ∀ N, 1 ≤ ZetaNearOneBudgetLimit.scale (t N))
    (ht : Tendsto (fun N => |t N|) atTop atTop)
    (A F : ℝ) (hA : ∀ N, mass (a N) ≤ A) (hF : ∀ N, frequencyCost (a N) (ω N) ≤ F) :
    Tendsto (fun N =>
      (max 0 ((a N 1 * ∑ ρ ∈ Z N, ZetaGaussianNearCancellation.compensated
        (gaussianScale (ZetaGaussianAllHeight.dilation (t N)))
        (halfWidth 9 (shift (ZetaGaussianAllHeight.dilation (t N))))
        (ZetaNearOneLocalDisc.center (shift (ZetaGaussianAllHeight.dilation (t N))) (t N)) ρ) -
          signedBudget (ZetaGaussianAllHeight.dilation (t N)) (M N) (t N) (a N) (ω N))) ^ 2 /
            (ZetaGaussianAllHeight.dilation (t N)) ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero _ _ (tendsto_current_source_cost a ω t ha hs hω hlog ht A F hA hF)
  · intro N
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · intro N
    exact div_le_div_of_nonneg_right
      (finite_source_le_fullEnergy (ha N) (hs N) (hP N) (hω0 N) (hω1 N) (hω N) (hlog N)
        (le_max_left _ _) (hM N) (t N) (Z N) (hscale N)) (sq_nonneg _)

end
end RiemannGaussian.ZetaGaussianPrimeEnergyDecay

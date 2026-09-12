/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaZeroFreeRegionBand
import RiemannGaussian.ZetaSquarefreeEulerPhaseBound

/-!
# Any complete zero-free band in the actual squarefree Cauchy bound

The arithmetic quotient is `zeta(s)/zeta(2*s)`. A proved common zero margin
`m` up to height `2*abs(y)+3` gives radius `1+m/2` about `3/2+i*y`, subject
to the explicit pole-separation cap. This statement does not restrict the
functional shape of `m` or replace it by an older logarithmic margin.

The actual marked arithmetic response inherits this radius. Its signed
prime harmonics stay in the radius-dependent envelope; they are not
silently bounded uniformly as the excluded prime set grows. The original
complex identities remain available upstream of the Cauchy estimate.
-/

namespace RiemannGaussian.SquarefreeEulerBand
noncomputable section
open Complex Filter Topology

/-- The common-band radius, capped to avoid the numerator and doubled
denominator poles at every ordinate with `abs(y)>1`. -/
def radius (y m : ℝ) : ℝ := 1 + min ((|y| - 1) / 2) (m / 2)

/-- A positive band margin below one quarter supplies a radius between
one and `9/8`, with the exact doubled-argument allowance retained. -/
theorem radius_bounds {y m : ℝ} (hy : 1 < |y|) (hm : 0 < m) (hmu : m < 1 / 4) :
    1 < radius y m ∧ radius y m < |y| ∧ radius y m < 9 / 8 ∧
      2 * (radius y m - 1) ≤ m := by
  have hp : 0 < min ((|y| - 1) / 2) (m / 2) :=
    lt_min (by linarith) (by positivity)
  have hl := min_le_left ((|y| - 1) / 2) (m / 2)
  have hr := min_le_right ((|y| - 1) / 2) (m / 2)
  unfold radius
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Increasing a valid common margin never decreases its analytic radius. -/
theorem radius_mono (y : ℝ) : Monotone (radius y) := by
  intro a b hab
  exact add_le_add le_rfl (min_le_min_left _ (by linarith : a / 2 ≤ b / 2))

/-- Away from the pole cap, the whole margin is used without further loss. -/
theorem radius_eq {y m : ℝ} (hy : 3 / 2 ≤ |y|) (hm : m < 1 / 4) :
    radius y m = 1 + m / 2 := by
  unfold radius
  rw [min_eq_right (by linarith : m / 2 ≤ (|y| - 1) / 2)]

/-- Every point of the full closed disc avoids the genuine numerator
pole and all zeros or poles of the doubled zeta denominator. Only the
actual common band is used, not a particular zero-free width formula. -/
theorem disc_safe {y m : ℝ} (hy : 1 < |y|) (hm : 0 < m) (hmu : m < 1 / 4)
    (hband : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ 2 * |y| + 3 → ρ.1.re < 1 - m)
    {s : ℂ} (hs : s ∈ Metric.closedBall (3 / 2 + I * y) (radius y m)) :
    s ≠ 1 ∧ 2 * s ≠ 1 ∧ riemannZeta (2 * s) ≠ 0 := by
  obtain ⟨_, hry, hru, hmargin⟩ := radius_bounds hy hm hmu
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
  have himBound : |s.im| ≤ |y| + radius y m := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp him).1, (abs_le.mp him).2, le_abs_self y, neg_abs_le y]
  have harg : |(2 * s).im| ≤ 2 * |y| + 3 := by
    norm_num [abs_mul]
    linarith
  have hedge : 1 - m ≤ (2 * s).re := by
    norm_num
    linarith [(abs_le.mp hre).1]
  exact ⟨hs1, hs2, riemannZeta_ne_zero_of_common_margin (by linarith) hband hs2 harg hedge⟩

/-- The literal squarefree quotient is analytic on a neighbourhood of
the complete closed disc supplied by any proved common margin. -/
theorem analyticOnNhd_response {y m : ℝ} (hy : 1 < |y|) (hm : 0 < m) (hmu : m < 1 / 4)
    (hband : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ 2 * |y| + 3 → ρ.1.re < 1 - m) :
    AnalyticOnNhd ℂ squarefreeEulerResponse (Metric.closedBall (3 / 2 + I * y) (radius y m)) := by
  intro s hs
  obtain ⟨hs1, hs2, hz⟩ := disc_safe hy hm hmu hband hs
  have hnum := analyticOn_riemannZeta s (by simpa using hs1)
  have hden := (analyticOn_riemannZeta (2 * s) (by simpa using hs2)).comp
    (analyticAt_const.mul analyticAt_id)
  exact hnum.div hden hz

/-- An open zero-free region supplies every strictly smaller closed
disc. This preserves the published boundary convention without choosing
a fixed fractional loss in its width. -/
theorem disc_safe_of_weak_band {y m r : ℝ} (hy : 1 < |y|) (hm : 0 < m) (hmu : m < 1 / 4)
    (hband : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ 2 * |y| + 3 → ρ.1.re ≤ 1 - m)
    (hr : r < radius y m) {s : ℂ} (hs : s ∈ Metric.closedBall (3 / 2 + I * y) r) :
    s ≠ 1 ∧ 2 * s ≠ 1 ∧ riemannZeta (2 * s) ≠ 0 := by
  obtain ⟨_, hry, hru, hmargin⟩ := radius_bounds hy hm hmu
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
  have himBound : |s.im| ≤ |y| + r := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp him).1, (abs_le.mp him).2, le_abs_self y, neg_abs_le y]
  have harg : |(2 * s).im| ≤ 2 * |y| + 3 := by
    norm_num [abs_mul]
    linarith
  have hedge : 1 - m < (2 * s).re := by
    norm_num
    linarith [(abs_le.mp hre).1]
  exact ⟨hs1, hs2, riemannZeta_ne_zero_of_common_weak_margin (by linarith) hband hs2 harg hedge⟩

/-- The literal quotient is analytic on every closed disc strictly
inside the radius from a non-strict bound on the surviving zeros. -/
theorem analyticOnNhd_response_of_weak_band {y m r : ℝ}
    (hy : 1 < |y|) (hm : 0 < m) (hmu : m < 1 / 4)
    (hband : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ 2 * |y| + 3 → ρ.1.re ≤ 1 - m)
    (hr : r < radius y m) :
    AnalyticOnNhd ℂ squarefreeEulerResponse (Metric.closedBall (3 / 2 + I * y) r) := by
  intro s hs
  obtain ⟨hs1, hs2, hz⟩ := disc_safe_of_weak_band hy hm hmu hband hr hs
  have hnum := analyticOn_riemannZeta s (by simpa using hs1)
  have hden := (analyticOn_riemannZeta (2 * s) (by simpa using hs2)).comp
    (analyticAt_const.mul analyticAt_id)
  exact hnum.div hden hz

/-- A general open eventual zero-free region supplies every closed
Cauchy disc strictly inside its full width at sufficiently large heights.
The low divisor and all boundary conditions are discharged first. -/
theorem exists_eventual_analytic_discs_of_weak_region (w : ℝ → ℝ) {T : ℝ}
    (hT : 1 ≤ T) (hpos : ∀ H : ℝ, T ≤ H → 0 < w H)
    (hanti : AntitoneOn w (Set.Ici T)) (hlim : Tendsto w atTop (𝓝 0))
    (hregion : ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      w |ρ.1.im| ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - w |ρ.1.im|) :
    ∃ Y : ℝ, 3 / 2 ≤ Y ∧ ∀ y : ℝ, Y ≤ |y| →
      ∀ r : ℝ, r < radius y (w (2 * |y| + 3)) →
        AnalyticOnNhd ℂ squarefreeEulerResponse (Metric.closedBall (3 / 2 + I * y) r) := by
  obtain ⟨H₀, _, hband⟩ :=
    exists_eventual_common_weak_margin_of_antitone w hT hpos hanti hlim hregion
  refine ⟨max (3 / 2) H₀, le_max_left _ _, ?_⟩
  intro y hy r hr
  have hy1 : 3 / 2 ≤ |y| := (le_max_left _ _).trans hy
  have hyH : H₀ ≤ |y| := (le_max_right _ _).trans hy
  obtain ⟨hm, hmu, hz⟩ := hband (2 * |y| + 3) (by linarith)
  exact analyticOnNhd_response_of_weak_band (by linarith) hm hmu (fun ρ hρ ↦ (hz ρ hρ).2) hr

/-- The full band margin reaches every excluded prime set, squarefree
mark, complex polynomial and moment order. Its only prime-set cost is
the signed two-harmonic envelope on the actual chosen radius. -/
theorem exists_response_bound {y m : ℝ} (hy : 1 < |y|) (hm : 0 < m) (hmu : m < 1 / 4)
    (hband : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ 2 * |y| + 3 → ρ.1.re < 1 - m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ radius y m →
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
        ∀ (p : Polynomial ℂ) (N : ℕ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * SquarefreeEulerPhase.envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k :=
  SquarefreeEulerPhase.exists_response_bound_of_analytic y (radius y m)
    (by linarith [(radius_bounds hy hm hmu).1]) (radius_bounds hy hm hmu).2.2.1.le
    (analyticOnNhd_response hy hm hmu hband)

/-- A proved eventual region of any positive decreasing shape tending to
zero feeds directly into the literal marked arithmetic estimates. Low
zeros and the full doubled-height disc are covered before Cauchy is used. -/
theorem exists_eventual_response_bound_of_region (w : ℝ → ℝ) {T : ℝ}
    (hT : 1 ≤ T) (hpos : ∀ H : ℝ, T ≤ H → 0 < w H)
    (hanti : AntitoneOn w (Set.Ici T)) (hlim : Tendsto w atTop (𝓝 0))
    (hregion : ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      w |ρ.1.im| < ρ.1.re ∧ ρ.1.re < 1 - w |ρ.1.im|) :
    ∃ Y : ℝ, 3 / 2 ≤ Y ∧ ∀ y : ℝ, Y ≤ |y| →
      ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ radius y (w (2 * |y| + 3)) →
        ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
          Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
          ∀ (p : Polynomial ℂ) (N : ℕ),
            ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
              C * SquarefreeEulerPhase.envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
                ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨H₀, _, hband⟩ :=
    exists_eventual_common_margin_of_antitone w hT hpos hanti hlim hregion
  refine ⟨max (3 / 2) H₀, le_max_left _ _, ?_⟩
  intro y hy
  have hy1 : 3 / 2 ≤ |y| := (le_max_left _ _).trans hy
  have hyH : H₀ ≤ |y| := (le_max_right _ _).trans hy
  obtain ⟨hm, hmu, hz⟩ := hband (2 * |y| + 3) (by linarith)
  exact exists_response_bound (by linarith) hm hmu (fun ρ hρ ↦ (hz ρ hρ).2)

/-- With the arithmetic mark and polynomial fixed, any geometric rate
strictly below the new outer radius is absorbed by the actual response.
The envelope is fixed here; no assertion for growing marks is hidden. -/
theorem tendsto_scaled_response {y m : ℝ} (hy : 1 < |y|) (hm : 0 < m) (hmu : m < 1 / 4)
    (hband : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ 2 * |y| + 3 → ρ.1.re < 1 - m)
    {a : ℝ} (ha : 0 ≤ a) (har : a < radius y m)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (P : ℕ)
    (hP : Squarefree P) (hPS : ∀ q ∈ P.primeFactors, q ∉ S) (p : Polynomial ℂ) :
    Tendsto (fun N : ℕ ↦ ((a ^ N : ℝ) : ℂ) *
      RoughSquarefreeBare.response p S P N (3 / 2 + I * y)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_response_bound hy hm hmu hband
  let r := radius y m
  let A := SquarefreeEulerPhase.envelope 2 S (3 / 2 + I * y) r
  let E := ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hr : 0 < r := by dsimp [r]; linarith [(radius_bounds hy hm hmu).1]
  have hratio : a * r⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_one hr).mpr har
  have hbound (N : ℕ) :
      ‖((a ^ N : ℝ) : ℂ) * RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
        (C * A * E) * (a * r⁻¹) ^ N := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg ha _)]
    calc
      _ ≤ a ^ N * (C * A * r⁻¹ ^ N * E) :=
        mul_le_mul_of_nonneg_left (hb r hr le_rfl S hS P hP hPS p N) (pow_nonneg ha _)
      _ = _ := by rw [mul_pow]; ring
  apply squeeze_zero_norm hbound
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg ha (inv_nonneg.mpr hr.le)) hratio).const_mul
      (C * A * E)

end
end RiemannGaussian.SquarefreeEulerBand

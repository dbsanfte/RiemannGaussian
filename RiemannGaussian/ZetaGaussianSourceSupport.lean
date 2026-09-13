/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianScaledBandBudget

/-!
# Exact visibility of the Gaussian zero source

The nearby source has an exact coupled horizontal/vertical support condition.
Changing dilation or phase frequency does not move its left horizontal edge.
Zeros outside that edge remain in the original complex far remainder; their
absence from the compensated source is a cutoff, not a nonvanishing theorem.

At the current dilation, every bounded-height zero window eventually leaves
the source altogether when detector height diverges. The source-surplus limit
then controls only the negative part of the left mean. The broader strip
identity instead admits adaptive geometry retaining any fixed right-half zero
with strictly positive source and every original signed budget term. The
independent arithmetic comparison remains open; no new zero-free region or
RH proof is claimed.
-/

namespace RiemannGaussian.ZetaGaussianSourceSupport
noncomputable section
open Complex Filter
open ZetaGaussianNearCancellation ZetaGaussianDistanceRemainder
open ZetaNearOneLocalDisc ZetaStripEulerConstraint
open DirichletPowerParameters DerivativeOrderComparison
open scoped Topology Classical

/-- The exact nearby ball retains its coupled horizontal depth and vertical displacement. -/
theorem near_iff (k : ℕ) {x : ℝ} (hx : 0 < x) (t : ℝ) (ρ : NontrivialZetaZero) :
    ‖center x t - ρ.1‖ < halfWidth k x ↔
      (t - ρ.1.im) ^ 2 < (ρ.1.re - line k) * (2 * (1 + x) - ρ.1.re - line k) := by
  have hη := halfWidth_pos k hx
  rw [← sq_lt_sq₀ (norm_nonneg _) hη.le, Complex.sq_norm]
  simp only [center, halfWidth, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, sub_zero, zero_add, add_zero]
  rw [delta_eq_one_sub_line]
  constructor <;> intro h <;> nlinarith

/-- Any zero on or left of the balanced line lies outside the source ball at every center height and shift. -/
theorem not_near_of_re_le_line (k : ℕ) (x t : ℝ) (ρ : NontrivialZetaZero)
    (hρ : ρ.1.re ≤ line k) : ¬ ‖center x t - ρ.1‖ < halfWidth k x := by
  have hr := Complex.re_le_norm (center x t - ρ.1)
  have hδ := delta_eq_one_sub_line k
  simp only [center, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero] at hr
  change 1 + x - ρ.1.re ≤ ‖center x t - ρ.1‖ at hr
  unfold halfWidth
  linarith

/-- At its own ordinate, a zero enters the ball exactly when it is strictly right of the balanced line. -/
theorem near_at_ordinate_iff (k : ℕ) {x : ℝ} (hx : 0 ≤ x) (ρ : NontrivialZetaZero) :
    ‖center x ρ.1.im - ρ.1‖ < halfWidth k x ↔ line k < ρ.1.re := by
  have he : center x ρ.1.im - ρ.1 = ((1 + x - ρ.1.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [center]
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith [NontrivialZetaZero.re_lt_one ρ] : 0 < 1 + x - ρ.1.re)]
  unfold halfWidth
  rw [delta_eq_one_sub_line]
  constructor <;> intro h <;> linarith

/-- Outside the actual nearby ball the full compensated source is exactly zero. -/
theorem compensated_eq_zero_of_not_near (B η : ℝ) (s : ℂ) (ρ : NontrivialZetaZero)
    (hρ : ¬ ‖s - ρ.1‖ < η) : compensated B η s ρ = 0 := by
  simp [compensated, nearSource, nearRestrict, nearPoisson, hρ]

/-- Changing Gaussian scale, center shift or height cannot detect a zero left of the fixed strip edge. -/
theorem compensated_eq_zero_of_re_le_line (k : ℕ) (B x t : ℝ) (ρ : NontrivialZetaZero)
    (hρ : ρ.1.re ≤ line k) : compensated B (halfWidth k x) (center x t) ρ = 0 :=
  compensated_eq_zero_of_not_near B _ _ ρ (not_near_of_re_le_line k x t ρ hρ)

/-- A source-invisible zero remains exactly in the original complex far remainder. -/
theorem farTerm_eq_of_re_le_line (k : ℕ) (B x t : ℝ) (ρ : NontrivialZetaZero)
    (hρ : ρ.1.re ≤ line k) :
    farTerm B (halfWidth k x) (center x t) ρ = ZetaGaussianPoleRemainder.term B (center x t) ρ := by
  simp [farTerm, le_of_not_gt (not_near_of_re_le_line k x t ρ hρ)]

/-- The complete finite source sum is unchanged by retaining only the zeros right of the actual left edge. -/
theorem sum_eq_filter_right (k : ℕ) (B x t : ℝ) (Z : Finset NontrivialZetaZero) :
    (∑ ρ ∈ Z, compensated B (halfWidth k x) (center x t) ρ) =
      ∑ ρ ∈ Z.filter (fun ρ => line k < ρ.1.re), compensated B (halfWidth k x) (center x t) ρ := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro ρ hZ hnot
  apply compensated_eq_zero_of_re_le_line
  exact le_of_not_gt (fun h => hnot (Finset.mem_filter.mpr ⟨hZ, h⟩))

/-- The current order-nine family has the exact fixed left edge 2035/2046, independently of dilation. -/
theorem current_compensated_eq_zero {q : ℝ} (B t : ℝ) (ρ : NontrivialZetaZero)
    (hρ : ρ.1.re ≤ 2035 / 2046) :
    compensated B (halfWidth 9 (ZetaGaussianScaledBandBudget.shift q))
      (center (ZetaGaussianScaledBandBudget.shift q) t) ρ = 0 := by
  apply compensated_eq_zero_of_re_le_line
  norm_num [line, DerivativePowerExponents.alpha] at hρ ⊢
  exact hρ

/-- Even varying every currently admissible derivative order cannot move the source left of 5/7; this is the range of this interface, not a statement about actual zero locations. -/
theorem admissible_order_compensated_eq_zero (k : ℕ) (hk : 2 ≤ k)
    (B x t : ℝ) (ρ : NontrivialZetaZero) (hρ : ρ.1.re ≤ 5 / 7) :
    compensated B (halfWidth k x) (center x t) ρ = 0 := by
  apply compensated_eq_zero_of_re_le_line
  have hd := delta_antitone hk
  rw [delta_eq_one_sub_line, delta_eq_one_sub_line] at hd
  have hl : line 2 = 5 / 7 := by norm_num [line, DerivativePowerExponents.alpha]
  rw [hl] at hd
  linarith

/-- Vertical separation alone can remove a zero from the source, with no assertion that the zero does not exist. -/
theorem compensated_eq_zero_of_height_gap (B η x t : ℝ) (ρ : NontrivialZetaZero)
    (hρ : η ≤ |t - ρ.1.im|) : compensated B η (center x t) ρ = 0 := by
  apply compensated_eq_zero_of_not_near
  have hi := Complex.abs_im_le_norm (center x t - ρ.1)
  simp only [center, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    zero_mul, one_mul, zero_add] at hi
  change |t - ρ.1.im| ≤ ‖center x t - ρ.1‖ at hi
  linarith

/-- At current geometry, any finite zero window in a bounded ordinate range has exactly zero source once the detector leaves that range by one unit. -/
theorem bounded_window_source_eq_zero {q t H B : ℝ} (hq : 1 ≤ q)
    (ht : H + 1 ≤ |t|) (Z : Finset NontrivialZetaZero)
    (hZ : ∀ ρ ∈ Z, |ρ.1.im| ≤ H) :
    (∑ ρ ∈ Z, compensated B (halfWidth 9 (ZetaGaussianScaledBandBudget.shift q))
      (center (ZetaGaussianScaledBandBudget.shift q) t) ρ) = 0 := by
  apply Finset.sum_eq_zero
  intro ρ hρ
  apply compensated_eq_zero_of_height_gap
  have hh := abs_add_le (t - ρ.1.im) ρ.1.im
  rw [sub_add_cancel] at hh
  linarith [(ZetaGaussianScaledBandBudget.geometry hq).2.1, hZ ρ hρ]

/-- A fixed finite actual zero window eventually contributes exactly zero at every dilation at least one when absolute detector height diverges. -/
theorem eventually_fixed_window_source_eq_zero (q B t : ℕ → ℝ)
    (hq : ∀ N, 1 ≤ q N) (ht : Tendsto (fun N => |t N|) atTop atTop)
    (Z : Finset NontrivialZetaZero) :
    ∀ᶠ N in atTop, (∑ ρ ∈ Z, compensated (B N)
      (halfWidth 9 (ZetaGaussianScaledBandBudget.shift (q N)))
      (center (ZetaGaussianScaledBandBudget.shift (q N)) (t N)) ρ) = 0 := by
  let H : ℝ := ∑ ρ ∈ Z, |ρ.1.im|
  filter_upwards [ht.eventually_ge_atTop (H + 1)] with N hN
  apply bounded_window_source_eq_zero (hq N) hN
  intro ρ hρ
  exact Finset.single_le_sum (fun τ _ => abs_nonneg τ.1.im) hρ

/-- Arbitrary moving scalar weights cannot recover a fixed zero window after the height cutoff has made its source identically zero. -/
theorem eventually_weighted_fixed_window_source_eq_zero (a q B t : ℕ → ℝ)
    (hq : ∀ N, 1 ≤ q N) (ht : Tendsto (fun N => |t N|) atTop atTop)
    (Z : Finset NontrivialZetaZero) :
    ∀ᶠ N in atTop, a N * (∑ ρ ∈ Z, compensated (B N)
      (halfWidth 9 (ZetaGaussianScaledBandBudget.shift (q N)))
      (center (ZetaGaussianScaledBandBudget.shift (q N)) (t N)) ρ) = 0 := by
  filter_upwards [eventually_fixed_window_source_eq_zero q B t hq ht Z] with N hN
  rw [hN, mul_zero]

/-- Every actual zero strictly inside the aligned source ball has a strictly positive compensated source, with its full multiplicity and every positive Gaussian scale. -/
theorem compensated_pos_at_ordinate {σ B η : ℝ} (hσ : 1 ≤ σ) (hB : 0 < B)
    (hη : 0 < η) (ρ : NontrivialZetaZero) (hρ : σ - ρ.1.re < η) :
    0 < compensated B η ((σ : ℂ) + I * ρ.1.im) ρ := by
  have hu : 0 < σ - ρ.1.re := by linarith [NontrivialZetaZero.re_lt_one ρ]
  have hm : 0 < (analyticZetaZeroMultiplicity ρ : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hs := SmoothedCotangentSource.gaussian_source_re_lower hB hη
    (z := ((σ - ρ.1.re : ℝ) : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu] using hρ.le)
    (by simpa using hu.le)
  rw [SmoothedCotangentSource.gaussian_source_real hη B hu (by linarith)] at hs
  have hms := mul_le_mul_of_nonneg_left hs hm.le
  have hp : (analyticZetaZeroMultiplicity ρ : ℝ) / (2 * η) <
      (analyticZetaZeroMultiplicity ρ : ℝ) / (σ + η - ρ.1.re) :=
    div_lt_div_of_pos_left hm (by linarith) (by linarith)
  have hf : 0 < 24 * B / η ^ 2 := by positivity
  have hmp := mul_lt_mul_of_pos_left hp hf
  have he : (24 * B / η ^ 2) * ((analyticZetaZeroMultiplicity ρ : ℝ) / (2 * η)) =
      (analyticZetaZeroMultiplicity ρ : ℝ) * (12 * B / η ^ 3) := by
    field_simp
    ring
  rw [he] at hmp
  rw [ZetaGaussianStripBound.compensated_at_ordinate hσ hη B ρ hρ]
  linarith

/-- An adaptive strip detects every fixed right-half zero while its right edge stays exactly at 3/2 and its left edge remains above 1/2. -/
theorem fixed_zero_geometry (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re) :
    ∃ σ η : ℝ, 1 < σ ∧ 0 < η ∧ 1 / 2 ≤ σ - η ∧ σ + η = 3 / 2 ∧
      σ - ρ.1.re < η := by
  refine ⟨1 + (ρ.1.re - 1 / 2) / 4, 1 / 2 - (ρ.1.re - 1 / 2) / 4, ?_⟩
  have hr := NontrivialZetaZero.re_lt_one ρ
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · ring
  · linarith

/-- The existing complete Gaussian strip identity gives every fixed right-half zero a strictly positive source in valid adaptive geometry; its full signed boundary and correction budget remains unbounded here. -/
theorem exists_fixed_zero_source_constraint (ρ : NontrivialZetaZero)
    (hρ : 1 / 2 < ρ.1.re) {B M : ℝ} (hB : 0 < B) (hM : 0 ≤ M) :
    ∃ σ η : ℝ, 1 < σ ∧ 0 < η ∧ 1 / 2 ≤ σ - η ∧ σ + η = 3 / 2 ∧
      0 < compensated B η ((σ : ℂ) + I * ρ.1.im) ρ ∧
      GaussianFermiPrimeComparison.ordinarySum σ B ρ.1.im +
          compensated B η ((σ : ℂ) + I * ρ.1.im) ρ ≤
        ZetaStripBoundaryConstraint.boundary ((σ : ℂ) + I * ρ.1.im) η M +
          (GaussianComplexHalfMoments.transform B ((σ : ℂ) + I * ρ.1.im - 1)).re -
          (1 / ((σ : ℂ) + I * ρ.1.im + 1) : ℂ).re +
          (ZetaGaussianCompletionAverage.response B ((σ : ℂ) + I * ρ.1.im) -
            zetaGlobalRegularCorrection ((σ : ℂ) + I * ρ.1.im)).re +
          (24 * B / η ^ 2) * (logDeriv riemannXi ((σ : ℂ) + I * ρ.1.im + (η : ℂ))).re := by
  obtain ⟨σ, η, hσ, hη, hlo, hhi, hnear⟩ := fixed_zero_geometry ρ hρ
  refine ⟨σ, η, hσ, hη, hlo, hhi, compensated_pos_at_ordinate hσ.le hB hη ρ hnear, ?_⟩
  simpa using ZetaGaussianStripBound.prime_add_selected_le hσ hB hη hlo hhi.le hM ρ.1.im {ρ}

end
end RiemannGaussian.ZetaGaussianSourceSupport

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianLaplacePoleRemainder
import RiemannGaussian.GaussianFermiZeroTail

/-!
# The complete Gaussian pole remainder over the actual zeta divisor

The exact complex remainder is summed with every analytic multiplicity.
A complete bounded-height window and an inverse-cube tail prove genuine
absolute convergence, including on `Re s = 1`. Outside height `H`, the
bound retains the extra factor `1/H` as well as the original divisor tail.
The complex sum and exact window decomposition precede their norm bounds.
-/

namespace RiemannGaussian.ZetaGaussianPoleRemainder
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology Classical
open GaussianComplexHalfMoments GaussianLaplacePoleRemainder
open GaussianFermiZeroTail (divisorWeight divisorTail summable_divisorWeight
  divisorWeight_nonneg summable_divisorTail_terms tendsto_divisorTail)

/-- One actual zero contributes its complete complex remainder with analytic multiplicity. -/
def term (B : ℝ) (s : ℂ) (ρ : NontrivialZetaZero) : ℂ :=
  (analyticZetaZeroMultiplicity ρ : ℂ) * remainder B (s - ρ.1)

/-- The original complex contribution outside the actual height window. -/
def outside (B : ℝ) (s : ℂ) (H : ℝ) (ρ : NontrivialZetaZero) : ℂ :=
  if H < |ρ.1.im| then term B s ρ else 0

/-- The original complex contribution inside the complete finite height window. -/
def inside (B : ℝ) (s : ℂ) (H : ℝ) (ρ : NontrivialZetaZero) : ℂ :=
  if |ρ.1.im| ≤ H then term B s ρ else 0

/-- Every actual zero has strictly positive real displacement from the closed
right half-plane; in particular the pole being subtracted is never totalized at zero. -/
theorem re_displacement_pos {s : ℂ} (hs : 1 ≤ s.re) (ρ : NontrivialZetaZero) :
    0 < (s - ρ.1).re := by
  simp only [Complex.sub_re]
  linarith [NontrivialZetaZero.re_lt_one ρ]

/-- The true multiplicity-weighted complex remainder has the cubic bound. -/
theorem norm_term_le {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re)
    (ρ : NontrivialZetaZero) :
    ‖term B s ρ‖ ≤ (analyticZetaZeroMultiplicity ρ : ℝ) *
      (12 * B / ‖s - ρ.1‖ ^ 3) := by
  have hr := re_displacement_pos hs ρ
  have hz : s - ρ.1 ≠ 0 := by intro h; simp [h] at hr
  rw [term, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_remainder_le hB hr.le hz) (Nat.cast_nonneg _)

/-- A distant ordinate controls both the full complex distance and its
inverse-square divisor weight, without discarding the displacement phase. -/
theorem separated_distance {s : ℂ} {γ H : ℝ} (ht : 2 * |s.im| ≤ H)
    (hH : 1 ≤ H) (hγ : H ≤ |γ|) {ρ : ℂ} (hρ : ρ.im = γ) :
    H / 2 ≤ ‖s - ρ‖ ∧ 1 + γ ^ 2 ≤ 8 * ‖s - ρ‖ ^ 2 := by
  have htriangle : |γ| ≤ |s.im - γ| + |s.im| := by
    simpa only [sub_add_cancel, abs_sub_comm] using abs_add_le (γ - s.im) s.im
  have him : |s.im - γ| ≤ ‖s - ρ‖ := by
    simpa only [Complex.sub_im, hρ] using Complex.abs_im_le_norm (s - ρ)
  have hgap : |γ| ≤ 2 * ‖s - ρ‖ := by linarith
  have hsq := (sq_le_sq₀ (abs_nonneg γ) (by positivity : 0 ≤ 2 * ‖s - ρ‖)).mpr hgap
  simp only [mul_pow, sq_abs] at hsq
  have hγsq : 1 ≤ γ ^ 2 := by nlinarith [sq_abs γ]
  exact ⟨by linarith, by nlinarith⟩

/-- The extra inverse power survives the passage to the existing summable
divisor weight. The coefficient is linear in `B` and inversely proportional to `H`. -/
theorem norm_term_le_divisorWeight {B H : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re)
    (ht : 2 * |s.im| ≤ H) (hH : 1 ≤ H) (ρ : NontrivialZetaZero) (hρ : H ≤ |ρ.1.im|) :
    ‖term B s ρ‖ ≤ (192 * B / H) * divisorWeight ρ := by
  obtain ⟨hgap, hden⟩ := separated_distance ht hH hρ (ρ := ρ.1) rfl
  have hH0 : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hq : 0 < ‖s - ρ.1‖ := by linarith
  have hD : 0 < 1 + ρ.1.im ^ 2 := by positivity
  have hcube : H * (1 + ρ.1.im ^ 2) ≤ 16 * ‖s - ρ.1‖ ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right (show H ≤ 2 * ‖s - ρ.1‖ by linarith)
      (sq_nonneg ‖s - ρ.1‖)
    have hd := mul_le_mul_of_nonneg_left hden hH0.le
    nlinarith only [hh, hd]
  have he : 12 * B / ‖s - ρ.1‖ ^ 3 ≤ (192 * B / H) / (1 + ρ.1.im ^ 2) := by
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < ‖s - ρ.1‖ ^ 3) (mul_pos hH0 hD)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hcube (show 0 ≤ 12 * B by positivity)]
  apply (norm_term_le hB hs ρ).trans
  calc
    _ ≤ (analyticZetaZeroMultiplicity ρ : ℝ) *
        ((192 * B / H) / (1 + ρ.1.im ^ 2)) :=
      mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
    _ = _ := by unfold divisorWeight; ring

/-- One genuine summable majorant controls every outside summand. -/
theorem norm_outside_le {B H : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re)
    (ht : 2 * |s.im| ≤ H) (hH : 1 ≤ H) (ρ : NontrivialZetaZero) :
    ‖outside B s H ρ‖ ≤ (192 * B / H) *
      (if H < |ρ.1.im| then divisorWeight ρ else 0) := by
  unfold outside
  split_ifs with hρ
  · exact norm_term_le_divisorWeight hB hs ht hH ρ hρ.le
  · simp

/-- The complete outside complex series is absolutely convergent. -/
theorem summable_outside {B H : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re)
    (ht : 2 * |s.im| ≤ H) (hH : 1 ≤ H) : Summable (outside B s H) :=
  ((summable_divisorTail_terms H).mul_left (192 * B / H)).of_norm_bounded
    (norm_outside_le hB hs ht hH)

/-- The complete complex outside sum is bounded by a vanishing tail, with
the additional inverse-height factor left explicit. -/
theorem norm_tsum_outside_le {B H : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re)
    (ht : 2 * |s.im| ≤ H) (hH : 1 ≤ H) :
    ‖∑' ρ : NontrivialZetaZero, outside B s H ρ‖ ≤ (192 * B / H) * divisorTail H := by
  have hsumm := summable_outside hB hs ht hH
  calc
    _ ≤ ∑' ρ : NontrivialZetaZero, ‖outside B s H ρ‖ := norm_tsum_le_tsum_norm hsumm.norm
    _ ≤ ∑' ρ : NontrivialZetaZero, (192 * B / H) *
        (if H < |ρ.1.im| then divisorWeight ρ else 0) :=
      hsumm.norm.tsum_le_tsum (norm_outside_le hB hs ht hH)
        ((summable_divisorTail_terms H).mul_left _)
    _ = _ := by rw [tsum_mul_left]; rfl

/-- The original bounded-height remainder has finite support in the actual divisor. -/
theorem finite_support_inside (B : ℝ) (s : ℂ) {H : ℝ} (hH : 0 ≤ H) :
    (Function.support (inside B s H)).Finite := by
  have hf : {ρ : NontrivialZetaZero | |ρ.1.im| ≤ H}.Finite := by
    simpa only [zetaSpectralCoordinate_re] using spectralZetaZeroWindowSet_finite hH
  apply hf.subset
  intro ρ hρ
  by_contra hn
  change ¬|ρ.1.im| ≤ H at hn
  exact hρ (by simp [inside, hn])

/-- The finite window and outside tail partition each original complex summand exactly. -/
theorem inside_add_outside (B : ℝ) (s : ℂ) (H : ℝ) (ρ : NontrivialZetaZero) :
    inside B s H ρ + outside B s H ρ = term B s ρ := by
  by_cases hρ : |ρ.1.im| ≤ H
  · simp [inside, outside, hρ, not_lt.mpr hρ]
  · simp [inside, outside, hρ, lt_of_not_ge hρ]

/-- The full actual multiplicity-weighted complex remainder series converges
absolutely on the entire closed half-plane `Re s ≥ 1`. -/
theorem summable_term {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re) :
    Summable (term B s) := by
  let H := max (2 * |s.im|) 1
  have hin : Summable (inside B s H) :=
    summable_of_hasFiniteSupport (finite_support_inside B s (by dsimp [H]; positivity))
  have hout := summable_outside hB hs (le_max_left (2 * |s.im|) 1) (le_max_right _ _)
  exact (hin.add hout).congr (inside_add_outside B s H)

/-- Complete convergence justifies the exact complex window decomposition. -/
theorem tsum_eq_inside_add_outside {B H : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re)
    (ht : 2 * |s.im| ≤ H) (hH : 1 ≤ H) :
    (∑' ρ : NontrivialZetaZero, term B s ρ) =
      (∑' ρ : NontrivialZetaZero, inside B s H ρ) +
      ∑' ρ : NontrivialZetaZero, outside B s H ρ := by
  have hin : Summable (inside B s H) :=
    summable_of_hasFiniteSupport (finite_support_inside B s (by linarith : 0 ≤ H))
  rw [← hin.tsum_add (summable_outside hB hs ht hH)]
  exact tsum_congr fun ρ => (inside_add_outside B s H ρ).symm

/-- The outside complex sum tends to zero as the actual complete height cutoff grows. -/
theorem tendsto_tsum_outside {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re) :
    Tendsto (fun H : ℝ => ∑' ρ : NontrivialZetaZero, outside B s H ρ) atTop (𝓝 0) := by
  have hp (ρ : NontrivialZetaZero) :
      Tendsto (fun H : ℝ => outside B s H ρ) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop |ρ.1.im|] with H hH
    simp [outside, not_lt.mpr hH]
  have hd : ∀ᶠ H : ℝ in atTop, ∀ ρ : NontrivialZetaZero,
      ‖outside B s H ρ‖ ≤ ‖term B s ρ‖ := by
    exact Eventually.of_forall fun H ρ => by unfold outside; split_ifs <;> simp
  simpa only [tsum_zero] using
    tendsto_tsum_of_dominated_convergence (summable_term hB hs).norm hp hd

/-- Finite complete zeta windows converge to the original full complex remainder,
with no change of phase, multiplicity, or summation convention. -/
theorem tendsto_tsum_inside {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re) :
    Tendsto (fun H : ℝ => ∑' ρ : NontrivialZetaZero, inside B s H ρ) atTop
      (𝓝 (∑' ρ : NontrivialZetaZero, term B s ρ)) := by
  have hp (ρ : NontrivialZetaZero) :
      Tendsto (fun H : ℝ => inside B s H ρ) atTop (𝓝 (term B s ρ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop |ρ.1.im|] with H hH
    simp [inside, hH]
  have hd : ∀ᶠ H : ℝ in atTop, ∀ ρ : NontrivialZetaZero,
      ‖inside B s H ρ‖ ≤ ‖term B s ρ‖ := by
    exact Eventually.of_forall fun H ρ => by unfold inside; split_ifs <;> simp
  exact tendsto_tsum_of_dominated_convergence (summable_term hB hs).norm hp hd

end
end RiemannGaussian.ZetaGaussianPoleRemainder

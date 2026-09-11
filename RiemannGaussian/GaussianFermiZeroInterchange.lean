/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiGaussianMixture
import RiemannGaussian.GaussianFermiZeroTail
import RiemannGaussian.GaussianXiLogDerivativeGrowth

/-!
# Spectral averaging through the actual zeta divisor

The spectral density has inverse-square decay. Keep the Gaussian localized
at each actual zero until after integrating: its convolution with this
density retains inverse-square decay in the zero ordinate. The existing
multiplicity-weighted divisor theorem then supplies the summable integral
norms required by the infinite-sum interchange.
-/

namespace RiemannGaussian.GaussianFermiZeroInterchange

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianFermiSpectralWeight GaussianFermiZeroTail

private def moment (ε x : ℝ) : ℝ := (1 + x ^ 2) * Real.exp (-ε * x ^ 2)

private theorem integrable_moment {ε : ℝ} (hε : 0 < ε) : Integrable (moment ε) := by
  have h0 := integrable_exp_neg_mul_sq hε
  have h2 : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-ε * x ^ 2)) := by
    simpa only [Real.rpow_two] using
      integrable_rpow_mul_exp_neg_mul_sq hε (by norm_num : (-1 : ℝ) < 2)
  exact (h0.add h2).congr (Eventually.of_forall fun x => by dsimp [moment]; ring)

private theorem one_add_sq_add_le (x y : ℝ) :
    1 + (x + y) ^ 2 ≤ 2 * (1 + x ^ 2) * (1 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y), mul_nonneg (sq_nonneg x) (sq_nonneg y)]

private theorem inverse_square_localization (t γ y : ℝ) :
    1 / (1 + y ^ 2) ≤
      4 * (1 + t ^ 2) * (1 + (γ - t + y) ^ 2) / (1 + γ ^ 2) := by
  have h1 := one_add_sq_add_le (t - y) (γ - t + y)
  have h2 := one_add_sq_add_le t (-y)
  have hm := mul_le_mul_of_nonneg_right h2
    (by positivity : 0 ≤ 2 * (1 + (γ - t + y) ^ 2))
  rw [neg_sq] at hm
  have htop : 1 + γ ^ 2 ≤
      4 * (1 + t ^ 2) * (1 + y ^ 2) * (1 + (γ - t + y) ^ 2) := by
    nlinarith
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- Multiplying the actual density by any translated Gaussian is
integrable before a zero is substituted into its center. -/
theorem integrable_density_gaussian {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hε : 0 < ε) (t γ : ℝ) :
    Integrable (fun y : ℝ => |density a b y| * Real.exp (-ε * (γ - t + y) ^ 2)) := by
  have hd := continuous_density hb a
  apply (integrable_density ha hb).abs.mono' (by fun_prop)
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_mul, abs_abs, Real.abs_exp]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr
    (by nlinarith [mul_nonneg hε.le (sq_nonneg (γ - t + y))]))

/-- A uniform ordinate bound for the localized density/Gaussian
convolution. Its constant is independent of the zero ordinate. -/
theorem exists_density_gaussian_bound {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hε : 0 < ε) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : ℝ,
      (∫ y : ℝ, |density a b y| * Real.exp (-ε * (γ - t + y) ^ 2)) ≤
        C / (1 + γ ^ 2) := by
  obtain ⟨D, hD, hd⟩ := exists_density_bound ha hb
  let M := ∫ x : ℝ, moment ε x
  have hM : 0 ≤ M := integral_nonneg fun x => by dsimp [moment]; positivity
  refine ⟨4 * D * (1 + t ^ 2) * M, by positivity, ?_⟩
  intro γ
  have hm : Integrable (fun y : ℝ => moment ε (γ - t + y)) :=
    (integrable_moment hε).comp_add_left (γ - t)
  have hpoint (y : ℝ) : |density a b y| * Real.exp (-ε * (γ - t + y) ^ 2) ≤
      (4 * D * (1 + t ^ 2) / (1 + γ ^ 2)) * moment ε (γ - t + y) := by
    have hp : |density a b y| ≤
        D * (4 * (1 + t ^ 2) * (1 + (γ - t + y) ^ 2) / (1 + γ ^ 2)) := by
      calc
        _ ≤ D / (1 + y ^ 2) := hd y
        _ = D * (1 / (1 + y ^ 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (inverse_square_localization t γ y) hD.le
    exact (mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)).trans_eq (by dsimp [moment]; ring)
  calc
    _ ≤ ∫ y : ℝ, (4 * D * (1 + t ^ 2) / (1 + γ ^ 2)) * moment ε (γ - t + y) :=
      integral_mono (integrable_density_gaussian ha hb hε t γ) (hm.const_mul _) hpoint
    _ = (4 * D * (1 + t ^ 2) / (1 + γ ^ 2)) * M := by
      rw [integral_const_mul, integral_add_left_eq_self]
    _ = _ := by ring

/-- The complete complex Gaussian summand with its original spectral
averaging weight and actual analytic multiplicity. -/
def zeroIntegrand (a b ε t : ℝ) (ρ : NontrivialZetaZero) (y : ℝ) : ℂ :=
  (density a b y : ℂ) *
    zetaGaussianDistinctZeroSummand analyticZetaZeroMultiplicity ε (t - y) ρ

/-- Each original complex zero integrand is absolutely integrable. -/
theorem integrable_zeroIntegrand {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hε : 0 < ε) (t : ℝ) (ρ : NontrivialZetaZero) :
    Integrable (zeroIntegrand a b ε t ρ) := by
  have hd := continuous_density hb a
  apply ((integrable_density ha hb).norm.mul_const
    ((analyticZetaZeroMultiplicity ρ : ℝ) *
      Real.exp (ε * (zetaSpectralCoordinate ρ.1).im ^ 2))).mono'
      (by unfold zeroIntegrand zetaGaussianDistinctZeroSummand complexTranslatedGaussian; fun_prop)
  filter_upwards with y
  simp only [zeroIntegrand, zetaGaussianDistinctZeroSummand, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_natCast, norm_complexTranslatedGaussian]
  gcongr
  nlinarith [mul_nonneg hε.le (sq_nonneg ((zetaSpectralCoordinate ρ.1).re - (t - y)))]

/-- The sum/integral interchange has an unconditional multiplicity-aware
majorant: each integral norm decays inversely quadratically in the actual
zero ordinate. -/
theorem exists_integral_norm_zeroIntegrand_bound {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hε : 0 < ε) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : NontrivialZetaZero,
      (∫ y : ℝ, ‖zeroIntegrand a b ε t ρ y‖) ≤ C * divisorWeight ρ := by
  obtain ⟨C, hC, hbound⟩ := exists_density_gaussian_bound ha hb hε t
  refine ⟨C * Real.exp (ε / 4), by positivity, ?_⟩
  intro ρ
  let m : ℝ := analyticZetaZeroMultiplicity ρ
  let γ := ρ.1.im
  let δ := (zetaSpectralCoordinate ρ.1).im
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hδ : δ ^ 2 ≤ 1 / 4 := by
    have h := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half ρ
    have hs : δ ^ 2 < (1 / 2 : ℝ) ^ 2 := by
      apply sq_lt_sq.mpr
      simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using h
    nlinarith
  have hamp : Real.exp (ε * δ ^ 2) ≤ Real.exp (ε / 4) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hδ hε.le])
  have hpoint (y : ℝ) : ‖zeroIntegrand a b ε t ρ y‖ ≤
      (m * Real.exp (ε / 4)) *
        (|density a b y| * Real.exp (-ε * (γ - t + y) ^ 2)) := by
    simp only [zeroIntegrand, zetaGaussianDistinctZeroSummand, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_natCast, norm_complexTranslatedGaussian,
      zetaSpectralCoordinate_re]
    change |density a b y| * (m * Real.exp (ε * δ ^ 2 - ε * (γ - (t - y)) ^ 2)) ≤ _
    rw [show ε * δ ^ 2 - ε * (γ - (t - y)) ^ 2 =
        ε * δ ^ 2 + -ε * (γ - t + y) ^ 2 by ring, Real.exp_add]
    calc
      _ = (m * Real.exp (ε * δ ^ 2)) *
          (|density a b y| * Real.exp (-ε * (γ - t + y) ^ 2)) := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∫ y : ℝ, (m * Real.exp (ε / 4)) *
        (|density a b y| * Real.exp (-ε * (γ - t + y) ^ 2)) :=
      integral_mono (integrable_zeroIntegrand ha hb hε t ρ).norm
        ((integrable_density_gaussian ha hb hε t γ).const_mul _) hpoint
    _ = (m * Real.exp (ε / 4)) *
        (∫ y : ℝ, |density a b y| * Real.exp (-ε * (γ - t + y) ^ 2)) := integral_const_mul _ _
    _ ≤ (m * Real.exp (ε / 4)) * (C / (1 + γ ^ 2)) := by gcongr; exact hbound γ
    _ = _ := by dsimp [m, γ, divisorWeight]; ring

/-- The complete family of integral norms is genuinely summable, using
the proved inverse-square actual divisor theorem. -/
theorem summable_integral_norm_zeroIntegrand {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hε : 0 < ε) (t : ℝ) :
    Summable (fun ρ : NontrivialZetaZero => ∫ y : ℝ, ‖zeroIntegrand a b ε t ρ y‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_norm_zeroIntegrand_bound ha hb hε t
  exact (summable_divisorWeight.mul_left C).of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _) hbound

/-- Averaging commutes with the entire actual zero divisor, retaining the
complex Gaussian phase and every analytic multiplicity. -/
theorem tsum_integral_zeroIntegrand {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hε : 0 < ε) (t : ℝ) :
    (∑' ρ : NontrivialZetaZero, ∫ y : ℝ, zeroIntegrand a b ε t ρ y) =
      ∫ y : ℝ, ∑' ρ : NontrivialZetaZero, zeroIntegrand a b ε t ρ y :=
  integral_tsum_of_summable_integral_norm (integrable_zeroIntegrand ha hb hε t)
    (summable_integral_norm_zeroIntegrand ha hb hε t)

/-- The averaged whole zero sum is itself absolutely integrable. The
counting-measure product proof makes the total integral norm explicit. -/
theorem integrable_tsum_zeroIntegrand {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hε : 0 < ε) (t : ℝ) :
    Integrable (fun y : ℝ => ∑' ρ : NontrivialZetaZero, zeroIntegrand a b ε t ρ y) := by
  have hd := continuous_density hb a
  have hmeas : Measurable (fun p : NontrivialZetaZero × ℝ =>
      zeroIntegrand a b ε t p.1 p.2) := by
    apply measurable_from_prod_countable_right
    intro ρ
    have hcont : Continuous (zeroIntegrand a b ε t ρ) := by
      unfold zeroIntegrand zetaGaussianDistinctZeroSummand complexTranslatedGaussian
      fun_prop
    exact hcont.measurable
  have hprod : Integrable (fun p : NontrivialZetaZero × ℝ =>
      zeroIntegrand a b ε t p.1 p.2) (Measure.count.prod volume) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (integrable_zeroIntegrand ha hb hε t), ?_⟩
    apply integrable_count_iff.mpr
    simpa only [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] using
      summable_integral_norm_zeroIntegrand ha hb hε t
  apply hprod.integral_prod_right.congr
  filter_upwards [hprod.prod_left_ae] with y hy
  simpa using integral_countable hy

/-- The full distinct-zero sum is the canonical Gaussian value, with
analytic multiplicities and the complex-to-real identification discharged. -/
theorem tsum_zeroIntegrand_eq {ε : ℝ} (hε : 0 < ε) (a b t y : ℝ) :
    (∑' ρ : NontrivialZetaZero, zeroIntegrand a b ε t ρ y) =
      (density a b y : ℂ) * (canonicalZetaGaussianZeroSum ε (t - y) : ℂ) := by
  unfold zeroIntegrand
  rw [tsum_mul_left]
  congr 1
  exact (hasSum_zetaGaussianDistinctZeroSummand analyticZetaZeroMultiplicity ε (t - y)
    (canonicalZetaGaussianZeroSum ε (t - y) : ℂ)
    (representsCanonicalZetaGaussianZeroSum_unconditional ε (t - y) hε)).tsum_eq

/-- The canonical Gaussian zero value can be averaged against the actual
Fermi spectral density with absolute integrability. -/
theorem integrable_density_canonical {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hε : 0 < ε) (t : ℝ) :
    Integrable (fun y : ℝ => (density a b y : ℂ) *
      (canonicalZetaGaussianZeroSum ε (t - y) : ℂ)) := by
  exact (integrable_tsum_zeroIntegrand ha hb hε t).congr
    (Eventually.of_forall fun y => tsum_zeroIntegrand_eq hε a b t y)

/-- A `HasSum` version of the full interchange identifies the canonical
average and records convergence of all integrated complex zero terms. -/
theorem hasSum_integral_zeroIntegrand {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hε : 0 < ε) (t : ℝ) :
    HasSum (fun ρ : NontrivialZetaZero => ∫ y : ℝ, zeroIntegrand a b ε t ρ y)
      (∫ y : ℝ, (density a b y : ℂ) * (canonicalZetaGaussianZeroSum ε (t - y) : ℂ)) := by
  have hs := hasSum_integral_of_summable_integral_norm
    (integrable_zeroIntegrand ha hb hε t) (summable_integral_norm_zeroIntegrand ha hb hε t)
  have he : (∫ y : ℝ, ∑' ρ : NontrivialZetaZero, zeroIntegrand a b ε t ρ y) =
      ∫ y : ℝ, (density a b y : ℂ) * (canonicalZetaGaussianZeroSum ε (t - y) : ℂ) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun y => tsum_zeroIntegrand_eq hε a b t y
  rw [he] at hs
  exact hs

end
end RiemannGaussian.GaussianFermiZeroInterchange

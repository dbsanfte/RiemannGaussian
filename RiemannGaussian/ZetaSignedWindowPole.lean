import RiemannGaussian.ZetaSignedExactPole

/-!
# Simultaneous signed pole control for actual zero windows

The three-height prime inequality bounds the entire local pole sum.
Actual zeros can be translated to a common center without losing their
analytic multiplicities. A finite selection and its complete complex
complement reconstruct that pole sum before the real estimate is taken.
-/

open Complex MeromorphicOn Metric Set
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The prime inequality bounds every enclosed pole simultaneously, with the exact height errors. -/
theorem four_mul_localZetaPoleSum_re_le_exactPole {y x : ℝ} (hy : y ≠ 0)
    (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    4 * (localZetaPoleSum y ((x - 1 / 2 : ℝ) : ℂ)).re ≤
      3 / x + 448 * (3 * localZetaLogHeight 0 + 4 * localZetaLogHeight y +
        localZetaLogHeight (2 * y)) + 17 * x / (4 * y ^ 2) := by
  have hprime := neg_logDeriv_riemannZeta_three_height_nonneg (a := 1 + x) (by linarith) y
  have hreal := neg_logDeriv_riemannZeta_real_le_local hx hxsmall
  have hzero := neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum y hx hxsmall
  have hp : x / (x ^ 2 + y ^ 2) ≤ x / y ^ 2 :=
    div_le_div_of_nonneg_left hx.le (sq_pos_of_ne_zero hy) (by nlinarith [sq_nonneg x])
  have hdouble := neg_logDeriv_riemannZeta_re_le_shift_div_sq
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hy) hx hxsmall
  rw [show x / (2 * y) ^ 2 = (x / y ^ 2) / 4 by ring] at hdouble
  simp only [Complex.neg_re, div_eq_mul_inv, mul_inv_rev] at hprime hreal hzero hdouble hp ⊢
  nlinarith

/-- A single logarithmic height controls the complete simultaneous zero contribution. -/
theorem four_mul_localZetaPoleSum_re_le_quadraticHeight {y x : ℝ} (hy : y ≠ 0)
    (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    4 * (localZetaPoleSum y ((x - 1 / 2 : ℝ) : ℂ)).re ≤
      3 / x + 4032 * localZetaLogHeight y + 17 * x / (4 * y ^ 2) := by
  have h := four_mul_localZetaPoleSum_re_le_exactPole hy hx hxsmall
  linarith [localZetaLogHeight_zero_le y, localZetaLogHeight_two_mul_le y]

/-- The position of an actual zero in the canonical disc with common ordinate center `y`. -/
def localZetaZeroTranslate (y : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  rho.1 - (3 / 2 + I * y)

/-- Translation to a common disc keeps distinct actual zeros distinct. -/
theorem localZetaZeroTranslate_injective (y : ℝ) : Function.Injective (localZetaZeroTranslate y) := by
  intro rho tau h
  exact Subtype.ext (sub_left_injective h)

/-- Every actual zero in a small edge window belongs to the common canonical disc. -/
theorem localZetaZeroTranslate_mem_canonicalBall (y D : ℝ) (hD : D ≤ 1 / 16)
    (rho : NontrivialZetaZero) (hbeta : 1 - D ≤ rho.1.re) (hgamma : |rho.1.im - y| ≤ D) :
    localZetaZeroTranslate y rho ∈ ball 0 (localZetaCanonicalRadius y) := by
  have hre : (localZetaZeroTranslate y rho).re = rho.1.re - 3 / 2 := by
    simp [localZetaZeroTranslate]
  have him : (localZetaZeroTranslate y rho).im = rho.1.im - y := by
    simp [localZetaZeroTranslate]
  have hn := Complex.norm_le_abs_re_add_abs_im (localZetaZeroTranslate y rho)
  rw [hre, him, abs_of_nonpos (by linarith [NontrivialZetaZero.re_lt_one rho])] at hn
  rw [mem_ball, dist_zero_right]
  linarith [(localZetaCanonicalRadius_spec y).1]

/-- At an arbitrary center, the local divisor retains the full analytic multiplicity of an enclosed zero. -/
theorem divisor_localZetaPoleRemoved_translate (y : ℝ) (rho : NontrivialZetaZero)
    (hmem : localZetaZeroTranslate y rho ∈ ball 0 (localZetaCanonicalRadius y)) :
    divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y))
      (localZetaZeroTranslate y rho) = (analyticZetaZeroMultiplicity rho : ℤ) := by
  rw [((analyticOnNhd_localZetaPoleRemoved_canonicalDisc y).mono ball_subset_closedBall).meromorphicOn.divisor_apply hmem]
  have hf : localZetaPoleRemoved y = riemannZeta₁ ∘ (· + (3 / 2 + I * (y : ℂ))) := by
    funext z
    simp only [localZetaPoleRemoved, Function.comp_def, add_comm z]
  rw [hf, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  rw [show localZetaZeroTranslate y rho + (3 / 2 + I * (y : ℂ)) = rho.1 by
    simp [localZetaZeroTranslate], meromorphicOrderAt_riemannZeta₁_nontrivialZero]
  simp

/-- A finite actual zero selection and every remaining pole reconstruct the exact complex local sum. -/
theorem localZetaPoleSum_eq_selected_add_complement (y : ℝ) (S : Finset NontrivialZetaZero)
    (hS : ∀ rho ∈ S, localZetaZeroTranslate y rho ∈ ball 0 (localZetaCanonicalRadius y)) (z : ℂ) :
    localZetaPoleSum y z =
      (∑ rho ∈ S, (analyticZetaZeroMultiplicity rho : ℂ) / (z - localZetaZeroTranslate y rho)) +
      ∑ᶠ i, ∑ᶠ (_ : i ∉ S.image (localZetaZeroTranslate y)),
        divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i • (1 / (z - i)) := by
  let d : ℂ → ℤ := fun i ↦ divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i
  let f : ℂ → ℂ := fun i ↦ d i • (1 / (z - i))
  have hd : (Function.support d).Finite :=
    (localZetaCanonicalResidual_decomp y).meromorphicOn.divisor_ball_support_finite
  have hf : f.HasFiniteSupport := hd.subset (by
    intro i hi hdi
    exact hi (by simp [f, hdi]))
  have hsplit := finsum_mem_add_sdiff' (f := f)
    (s := (S.image (localZetaZeroTranslate y) : Set ℂ)) (t := Set.univ)
    (Set.subset_univ _) (by rw [Set.univ_inter]; exact hf)
  rw [finsum_mem_univ] at hsplit
  have hselected : (∑ᶠ i, ∑ᶠ (_ : i ∈ S.image (localZetaZeroTranslate y)), f i) =
      ∑ rho ∈ S, (analyticZetaZeroMultiplicity rho : ℂ) / (z - localZetaZeroTranslate y rho) := by
    rw [finsum_mem_finset_eq_sum, Finset.sum_image (localZetaZeroTranslate_injective y).injOn]
    apply Finset.sum_congr rfl
    intro rho hrho
    dsimp [f, d]
    rw [divisor_localZetaPoleRemoved_translate y rho (hS rho hrho)]
    simp [zsmul_eq_mul, div_eq_mul_inv]
  simpa only [Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe,
    hselected, f, d, localZetaPoleSum] using hsplit.symm

/-- The exact real Cauchy contribution retains both coordinates and the analytic multiplicity. -/
theorem localZetaSelectedPole_re_eq (y x : ℝ) (rho : NontrivialZetaZero) :
    ((analyticZetaZeroMultiplicity rho : ℂ) /
      (((x - 1 / 2 : ℝ) : ℂ) - localZetaZeroTranslate y rho)).re =
      (analyticZetaZeroMultiplicity rho : ℝ) *
        ((x + 1 - rho.1.re) / ((x + 1 - rho.1.re) ^ 2 + (y - rho.1.im) ^ 2)) := by
  have he : ((x - 1 / 2 : ℝ) : ℂ) - localZetaZeroTranslate y rho =
      ((x + 1 - rho.1.re : ℝ) : ℂ) + I * ((y - rho.1.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [localZetaZeroTranslate]
    ring
  rw [he, div_eq_mul_one_div, Complex.mul_re, zetaPole_real_part]
  simp

/-- The common local sum bounds every selected actual zero simultaneously; omitted poles have nonnegative real part. -/
theorem sum_multiplicity_cauchy_le_localZetaPoleSum_re (y : ℝ) (S : Finset NontrivialZetaZero)
    (hS : ∀ rho ∈ S, localZetaZeroTranslate y rho ∈ ball 0 (localZetaCanonicalRadius y))
    {x : ℝ} (hx : 0 < x) :
    (∑ rho ∈ S, (analyticZetaZeroMultiplicity rho : ℝ) *
      ((x + 1 - rho.1.re) / ((x + 1 - rho.1.re) ^ 2 + (y - rho.1.im) ^ 2))) ≤
      (localZetaPoleSum y ((x - 1 / 2 : ℝ) : ℂ)).re := by
  let d : ℂ → ℤ := fun i ↦ divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i
  let g : ℂ → ℂ := fun i ↦ ∑ᶠ (_ : i ∉ S.image (localZetaZeroTranslate y)),
    d i • (1 / (((x - 1 / 2 : ℝ) : ℂ) - i))
  have hd : (Function.support d).Finite :=
    (localZetaCanonicalResidual_decomp y).meromorphicOn.divisor_ball_support_finite
  have hg : g.HasFiniteSupport := hd.subset (by
    intro i hi hdi
    exact hi (by simp [g, hdi]))
  have hc : 0 ≤ (∑ᶠ i, g i).re := by
    change 0 ≤ Complex.reAddGroupHom (∑ᶠ i, g i)
    rw [map_finsum Complex.reAddGroupHom hg]
    apply finsum_nonneg
    intro i
    by_cases hi : i ∉ S.image (localZetaZeroTranslate y)
    · simp only [g, hi]
      simpa [d, zsmul_eq_mul] using localZetaPoleSum_term_nonneg y hx i
    · simp only [g, hi]
      simp
  rw [localZetaPoleSum_eq_selected_add_complement y S hS, Complex.add_re, Complex.re_sum]
  simp only [localZetaSelectedPole_re_eq]
  exact le_add_of_nonneg_right hc

end

end RiemannGaussian

import RiemannGaussian.ZetaSignedPoleControl
import RiemannGaussian.EtaZetaPrimeProduct

/-!
# Signed local zero contributions to the zeta logarithmic derivative

On the right of one every local zero contributes a nonnegative Cauchy
kernel to the pole sum. Keeping this sign gives an upper bound for the
negative logarithmic derivative with a selected actual zero's complete
multiplicity subtracted, while only the analytic remainder is bounded.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Taking the real part retains the complete weighted Cauchy sum. -/
theorem localZetaPoleSum_re_eq (y : ℝ) (z : ℂ) :
    (localZetaPoleSum y z).re =
      ∑ᶠ i, (divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i : ℝ) *
        (1 / (z - i)).re := by
  let d : ℂ → ℤ := fun i ↦ divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i
  have hd : (Function.support d).Finite :=
    (localZetaCanonicalResidual_decomp y).meromorphicOn.divisor_ball_support_finite
  have ht : (fun i ↦ d i • (1 / (z - i))).HasFiniteSupport := hd.subset (by
    intro i hi hdi
    exact hi (by simp [hdi]))
  change Complex.reAddGroupHom (∑ᶠ i, d i • (1 / (z - i))) = _
  rw [map_finsum Complex.reAddGroupHom ht]
  apply finsum_congr
  intro i
  simp [d, zsmul_eq_mul]

/-- Each complete divisor term has nonnegative real Cauchy contribution
to the right of the line corresponding to `re s = 1`. -/
theorem localZetaPoleSum_term_nonneg (y : ℝ) {x : ℝ} (hx : 0 < x) (i : ℂ) :
    0 ≤ (divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i : ℝ) *
      (1 / (((x - 1 / 2 : ℝ) : ℂ) - i)).re := by
  let d : ℤ := divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i
  by_cases hi : d = 0
  · change 0 ≤ (d : ℝ) * _
    simp [hi]
  · have hri := localZetaDivisor_re_lt_neg_half y hi
    have hre : 0 ≤ (((x - 1 / 2 : ℝ) : ℂ) - i).re := by simp; linarith
    apply mul_nonneg
    · exact_mod_cast ((analyticOnNhd_localZetaPoleRemoved_canonicalDisc y).mono ball_subset_closedBall).divisor_nonneg i
    · rw [one_div, Complex.inv_re]
      exact div_nonneg hre (Complex.normSq_nonneg _)

/-- The complete signed local pole sum has nonnegative real part on
the right of one. -/
theorem localZetaPoleSum_re_nonneg (y : ℝ) {x : ℝ} (hx : 0 < x) :
    0 ≤ (localZetaPoleSum y ((x - 1 / 2 : ℝ) : ℂ)).re := by
  rw [localZetaPoleSum_re_eq]
  exact finsum_nonneg (localZetaPoleSum_term_nonneg y hx)

/-- A selected actual zero contributes its entire multiplicity to
the real pole sum; every other enclosed zero has the same nonnegative sign. -/
theorem multiplicity_div_gap_le_localZetaPoleSum_re (rho : NontrivialZetaZero)
    (hrho : 3 / 4 ≤ rho.1.re) {x : ℝ} (hx : 0 < x) :
    (analyticZetaZeroMultiplicity rho : ℝ) / (x + 1 - rho.1.re) ≤
      (localZetaPoleSum rho.1.im ((x - 1 / 2 : ℝ) : ℂ)).re := by
  let y := rho.1.im
  let z : ℂ := ((x - 1 / 2 : ℝ) : ℂ)
  let j : ℂ := ((rho.1.re - 3 / 2 : ℝ) : ℂ)
  let d : ℂ → ℤ := fun i ↦ divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i
  have hd : (Function.support d).Finite :=
    (localZetaCanonicalResidual_decomp y).meromorphicOn.divisor_ball_support_finite
  have ht : (fun i ↦ (d i : ℝ) * (1 / (z - i)).re).HasFiniteSupport := hd.subset (by
    intro i hi hdi
    exact hi (by simp [hdi]))
  have h := single_le_finsum j ht (localZetaPoleSum_term_nonneg y hx)
  have he : z - j = ((x + 1 - rho.1.re : ℝ) : ℂ) := by dsimp [z, j]; push_cast; ring
  have hdj : d j = (analyticZetaZeroMultiplicity rho : ℤ) :=
    divisor_localZetaPoleRemoved_nontrivialZero rho hrho
  calc
    (analyticZetaZeroMultiplicity rho : ℝ) / (x + 1 - rho.1.re) =
        (d j : ℝ) * (1 / (z - j)).re := by
      rw [hdj, he, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]
      simp only [Int.cast_natCast, div_eq_mul_inv]
    _ ≤ ∑ᶠ i, (d i : ℝ) * (1 / (z - i)).re := h
    _ = _ := (localZetaPoleSum_re_eq y z).symm

/-- The exact local decomposition includes the simple pole at one
and the full signed zero sum before either is bounded. -/
theorem neg_logDeriv_riemannZeta_eq_local (y : ℝ) {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    -logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * y) =
      1 / ((x : ℂ) + I * y) - localZetaLogRemainder y ((x - 1 / 2 : ℝ) : ℂ) -
        localZetaPoleSum y ((x - 1 / 2 : ℝ) : ℂ) := by
  let s : ℂ := ((1 + x : ℝ) : ℂ) + I * y
  let z : ℂ := ((x - 1 / 2 : ℝ) : ℂ)
  have hs : 1 < s.re := by dsimp [s]; simp; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have he : 3 / 2 + I * (y : ℂ) + z = s := by dsimp [z, s]; push_cast; ring
  have hnorm : ‖z‖ ≤ 1 / 2 := by
    dsimp [z]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hmem : z ∈ ball 0 (localZetaCanonicalRadius y) := by
    rw [mem_ball, dist_zero_right]
    linarith [(localZetaCanonicalRadius_spec y).1]
  have hf : localZetaPoleRemoved y z ≠ 0 := by
    rw [localZetaPoleRemoved, he]
    exact riemannZeta₁_ne_zero_of_one_le_re hs.le
  have hlog : logDeriv riemannZeta₁ s = localZetaLogRemainder y z + localZetaPoleSum y z := by
    rw [← he, ← logDeriv_localZetaPoleRemoved_eq]
    exact logDeriv_localZetaPoleRemoved_eq_remainder_add_poleSum y hmem hf
  have hp : s - 1 = (x : ℂ) + I * y := by dsimp [s]; push_cast; ring
  change -logDeriv riemannZeta s = _
  rw [neg_logDeriv_riemannZeta_eq_pole_sub hs1 (riemannZeta_ne_zero_of_one_le_re hs.le), hlog, hp]
  ring

/-- The signed local estimate bounds only the analytic remainder and
the pole at one, retaining the whole real zero sum with negative sign. -/
theorem neg_logDeriv_riemannZeta_re_le_sub_poleSum {y x : ℝ} (hy : y ≠ 0)
    (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * y)).re ≤
      1 / |y| + 448 * localZetaLogHeight y - (localZetaPoleSum y ((x - 1 / 2 : ℝ) : ℂ)).re := by
  have hnorm : ‖((x - 1 / 2 : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hrem := norm_localZetaLogRemainder_le y hnorm
  have hp : (1 / ((x : ℂ) + I * y)).re ≤ 1 / |y| := by
    apply (Complex.re_le_norm _).trans
    rw [norm_div, norm_one]
    apply one_div_le_one_div_of_le (abs_pos.mpr hy)
    simpa using Complex.abs_im_le_norm ((x : ℂ) + I * y)
  rw [neg_logDeriv_riemannZeta_eq_local y hx hxsmall, Complex.sub_re, Complex.sub_re]
  linarith [(abs_le.mp (Complex.abs_re_le_norm (localZetaLogRemainder y ((x - 1 / 2 : ℝ) : ℂ)))).1]

/-- Every nonzero height has an unconditional signed upper bound on
the right of one. -/
theorem neg_logDeriv_riemannZeta_re_le {y x : ℝ} (hy : y ≠ 0) (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * y)).re ≤
      1 / |y| + 448 * localZetaLogHeight y := by
  exact (neg_logDeriv_riemannZeta_re_le_sub_poleSum hy hx hxsmall).trans
    (sub_le_self _ (localZetaPoleSum_re_nonneg y hx))

/-- An actual nearby zero gives a negative term of its full genuine
multiplicity in the signed zeta logarithmic-derivative estimate. -/
theorem neg_logDeriv_riemannZeta_re_le_sub_zero (rho : NontrivialZetaZero)
    (hrho : 3 / 4 ≤ rho.1.re) {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * rho.1.im)).re ≤
      1 / |rho.1.im| + 448 * localZetaLogHeight rho.1.im -
        (analyticZetaZeroMultiplicity rho : ℝ) / (x + 1 - rho.1.re) := by
  exact (neg_logDeriv_riemannZeta_re_le_sub_poleSum (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) hx hxsmall).trans
    (sub_le_sub_left (multiplicity_div_gap_le_localZetaPoleSum_re rho hrho hx) _)

end

end RiemannGaussian

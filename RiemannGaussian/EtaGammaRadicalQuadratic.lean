import RiemannGaussian.EtaGammaRadicalBulk
import RiemannGaussian.EtaDivisorGcdBound

/-!
# A finite signed radical expression for the original gamma quadratic

Every original gcd block contributes its exact radical bulk and complete
tail. The floor-cutoff inequality is proved for every retained gcd, so
the infinite tails can be bounded together at a single physical threshold.
The final finite sum retains both complex powers and all arithmetic signs;
no sign or cancellation estimate for that sum is assumed.
-/

open Complex
open RiemannGaussian.EtaGammaSmoothing RiemannGaussian.EtaGammaQuadratic
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaGcd

noncomputable section

/-- The finite signed physical bulk of every original gcd block, retaining its squarefree weight, complex power, and divided cutoff. -/
def radicalQuadratic (rho : NontrivialZetaZero) (A : ℝ) (U : ℕ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 U, ((μ g : ℂ) ^ 2 * (g : ℂ) ^ (-2 * rho.1)) *
    radicalBulk rho (A / (g : ℝ) ^ 2) (U / g) g

/-- The full original quadratic equals its finite radical expression plus every retained complex gcd tail. -/
theorem smoothQuadratic_eq_radicalQuadratic_add_tail (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) (U : ℕ) :
    smoothQuadratic rho A U = radicalQuadratic rho A U +
      ∑ g ∈ Finset.Icc 1 U, ((μ g : ℂ) ^ 2 * (g : ℂ) ^ (-2 * rho.1)) *
        radicalTail rho (A / (g : ℝ) ^ 2) (U / g) g := by
  rw [smoothQuadratic_eq_sum_gcdBlock rho hA]
  unfold radicalQuadratic
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g hg
  have hgp := (Finset.mem_Icc.mp hg).1
  rw [gcdBlock_eq_factor_mul_reducedCore rho hA U hgp,
    reducedGcdCore_eq_radicalBulk_add_tail rho
      (div_pos hA (pow_pos (by exact_mod_cast hgp : (0 : ℝ) < g) 2)), mul_add]

private theorem divided_cutoff_bounds {U g : ℕ} (hg : g ∈ Finset.Icc 1 U) :
    1 ≤ U / g ∧ U / g ≤ U ∧ (U : ℝ) ≤ 2 * (g : ℝ) * (U / g : ℕ) := by
  have hgp := (Finset.mem_Icc.mp hg).1
  have hgU := (Finset.mem_Icc.mp hg).2
  have hN : 1 ≤ U / g := Nat.div_pos hgU hgp
  refine ⟨hN, Nat.div_le_self U g, ?_⟩
  have hU := Nat.lt_mul_div_succ U hgp
  have hgg : g ≤ g * (U / g) := Nat.le_mul_of_pos_right g hN
  have hb : U ≤ 2 * g * (U / g) := by nlinarith
  exact_mod_cast hb

private theorem divided_cutoff_sq {U g : ℕ} (hg : g ∈ Finset.Icc 1 U) :
    (U : ℝ) ^ 2 ≤ 4 * (g : ℝ) ^ 2 * ((U / g : ℕ) : ℝ) ^ 2 := by
  have h := (sq_le_sq₀ (Nat.cast_nonneg U) (by positivity)).mpr (divided_cutoff_bounds hg).2.2
  nlinarith

private theorem norm_gcd_factor_le_one (rho : NontrivialZetaZero) {g : ℕ} (hg : 1 ≤ g) :
    ‖(μ g : ℂ) ^ 2 * (g : ℂ) ^ (-2 * rho.1)‖ ≤ 1 := by
  have hm : ‖(μ g : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := g)
  rw [norm_mul, norm_pow, Complex.norm_natCast_cpow_of_pos hg]
  have hp : (g : ℝ) ^ (-2 * rho.1).re ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hg)
    have he : (-2 * rho.1).re = -2 * rho.1.re := by simp [Complex.mul_re]
    rw [he]
    linarith [NontrivialZetaZero.zero_lt_re rho]
  exact mul_le_one₀ (by nlinarith [norm_nonneg (μ g : ℂ)]) (by positivity) hp

private theorem norm_scaled_radicalTail_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) {U : ℕ} (hU : 8 * A ≤ (U : ℝ) ^ 2)
    {g : ℕ} (hg : g ∈ Finset.Icc 1 U) :
    ‖((μ g : ℂ) ^ 2 * (g : ℂ) ^ (-2 * rho.1)) *
      radicalTail rho (A / (g : ℝ) ^ 2) (U / g) g‖ ≤
        (16 * ‖pairedEtaXiCompletionFactor rho.1‖ * A * (U : ℝ) ^ 2 *
          Real.exp (-(U : ℝ) ^ 2 / (8 * A))) * (1 / (g : ℝ)) ^ 2 := by
  have hgp := (Finset.mem_Icc.mp hg).1
  have hgR : (0 : ℝ) < g := by exact_mod_cast hgp
  have hT : 0 < A / (g : ℝ) ^ 2 := div_pos hA (pow_pos hgR 2)
  obtain ⟨hN, hNU, _⟩ := divided_cutoff_bounds hg
  have hN1 : (1 : ℝ) ≤ (U / g : ℕ) := by exact_mod_cast hN
  have hNUr : ((U / g : ℕ) : ℝ) ^ 2 ≤ (U : ℝ) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left hNU 2
  have hsq := divided_cutoff_sq hg
  have hTN : 2 * (A / (g : ℝ) ^ 2) ≤ ((U / g : ℕ) : ℝ) ^ 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (pow_pos hgR 2)).mpr
    nlinarith
  have hratio : (U : ℝ) ^ 2 / (8 * A) ≤
      ((U / g : ℕ) : ℝ) ^ 2 / (2 * (A / (g : ℝ) ^ 2)) := by
    have he : ((U / g : ℕ) : ℝ) ^ 2 / (2 * (A / (g : ℝ) ^ 2)) =
        ((U / g : ℕ) : ℝ) ^ 2 * (g : ℝ) ^ 2 / (2 * A) := by field_simp
    rw [he]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq hA.le]
  have he : Real.exp (-((U / g : ℕ) : ℝ) ^ 2 / (2 * (A / (g : ℝ) ^ 2))) ≤
      Real.exp (-(U : ℝ) ^ 2 / (8 * A)) := by
    simpa only [neg_div] using Real.exp_le_exp.mpr (neg_le_neg hratio)
  have hp : (((U / g : ℕ) : ℝ) ^ 2) ^ (-rho.1.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith)
      (neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le)
  have hprod : ((U / g : ℕ) : ℝ) ^ 2 *
      (((U / g : ℕ) : ℝ) ^ 2) ^ (-rho.1.re) ≤ (U : ℝ) ^ 2 :=
    (mul_le_of_le_one_right (sq_nonneg _) hp).trans hNUr
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) (norm_gcd_factor_le_one rho hgp)).trans
  apply (norm_radicalTail_le rho hT hTN g).trans
  calc
    _ = (16 * ‖pairedEtaXiCompletionFactor rho.1‖ * (A / (g : ℝ) ^ 2)) *
        (((U / g : ℕ) : ℝ) ^ 2 * (((U / g : ℕ) : ℝ) ^ 2) ^ (-rho.1.re)) *
          Real.exp (-((U / g : ℕ) : ℝ) ^ 2 / (2 * (A / (g : ℝ) ^ 2))) := by ring
    _ ≤ (16 * ‖pairedEtaXiCompletionFactor rho.1‖ * (A / (g : ℝ) ^ 2)) * (U : ℝ) ^ 2 *
        Real.exp (-(U : ℝ) ^ 2 / (8 * A)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprod (by positivity)) he
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- The original full gamma quadratic differs from its finite signed radical expression by a proved exponential allowance, simultaneously over all gcd blocks and all omitted cofactor integers. -/
theorem norm_smoothQuadratic_sub_radicalQuadratic_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) {U : ℕ} (hU : 8 * A ≤ (U : ℝ) ^ 2) :
    ‖smoothQuadratic rho A U - radicalQuadratic rho A U‖ ≤
      32 * ‖pairedEtaXiCompletionFactor rho.1‖ * A * (U : ℝ) ^ 2 *
        Real.exp (-(U : ℝ) ^ 2 / (8 * A)) := by
  rw [smoothQuadratic_eq_radicalQuadratic_add_tail rho hA, add_sub_cancel_left]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun g hg ↦ norm_scaled_radicalTail_le rho hA hU hg)).trans
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le_two U) (by positivity)).trans_eq
  ring

end

end RiemannGaussian.EtaGammaGcd

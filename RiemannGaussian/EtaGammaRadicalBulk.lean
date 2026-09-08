import RiemannGaussian.EtaCoprimeRadicalCutoff
import RiemannGaussian.EtaGammaQuadraticGcd

/-!
# The actual gamma gcd core with its divisor multiplicities cancelled

The complete reduced gcd core is transported to the literal coprime
divisor coefficients. In the full product bulk their exact radical signs
replace the finite divisor square. The complementary infinite tail is
retained and bounded exponentially for the actual gamma carrier. The
remaining bulk is still a signed sum over physical integers; its phase
cancellation is not supplied by the coefficient bound.
-/

open Complex Filter
open RiemannGaussian.EtaGammaSmoothing RiemannGaussian.EtaGammaQuadratic
open scoped Classical Topology ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaGcd

noncomputable section

private theorem coefficient_mul_eq_sum (g N n : ℕ) (z : ℂ) :
    (EtaCoprimeRadical.coefficient g N N n : ℂ) * z =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        if a.Coprime b ∧ g.Coprime a ∧ g.Coprime b then
          (μ a : ℂ) * (μ b : ℂ) * (if a * b ∣ n then z else 0) else 0 := by
  simp only [EtaCoprimeRadical.coefficient, Int.cast_sum, Int.cast_ite,
    Int.cast_mul, Int.cast_zero, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hd : a * b ∣ n <;>
    by_cases hc : a.Coprime b ∧ g.Coprime a ∧ g.Coprime b <;> simp [hd, hc]

/-- The literal coprime divisor coefficients sum to the complete original reduced core, with every positive cofactor row and its convergence accounted for. -/
theorem hasSum_coefficient_gamma (rho : NontrivialZetaZero) {T : ℝ} (hT : 0 < T) (N g : ℕ) :
    HasSum (fun n : ℕ ↦ (EtaCoprimeRadical.coefficient g N N (n + 1) : ℂ) *
      gammaCarrier rho T (n + 1)) (-reducedGcdCore rho T N g) := by
  have hrow (a : ℕ) (ha : a ∈ Finset.Icc 1 N) (b : ℕ) (hb : b ∈ Finset.Icc 1 N) :
      HasSum (fun n : ℕ ↦ if a.Coprime b ∧ g.Coprime a ∧ g.Coprime b then
        (μ a : ℂ) * (μ b : ℂ) *
          (if a * b ∣ n + 1 then gammaCarrier rho T (n + 1) else 0) else 0)
        (if a.Coprime b ∧ g.Coprime a ∧ g.Coprime b then
          (μ a : ℂ) * (μ b : ℂ) * gammaRow rho T (a * b) else 0) := by
    by_cases hc : a.Coprime b ∧ g.Coprime a ∧ g.Coprime b
    · simp only [if_pos hc]
      exact (hasSum_dvd_gammaRow rho hT
        (Nat.mul_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1)).mul_left _
    · simp only [if_neg hc]
      exact hasSum_zero
  have hs := hasSum_sum (s := Finset.Icc 1 N) (fun a ha ↦
    hasSum_sum (s := Finset.Icc 1 N) (fun b hb ↦ hrow a ha b hb))
  simp only [reducedGcdCore, neg_neg]
  simpa only [coefficient_mul_eq_sum] using hs

/-- An exact single physical sum for the original reduced gcd core, prior to any cutoff or norm estimate. -/
theorem reducedGcdCore_eq_tsum_coefficient (rho : NontrivialZetaZero) {T : ℝ}
    (hT : 0 < T) (N g : ℕ) :
    reducedGcdCore rho T N g =
      -(∑' n : ℕ, (EtaCoprimeRadical.coefficient g N N (n + 1) : ℂ) *
        gammaCarrier rho T (n + 1)) := by
  rw [(hasSum_coefficient_gamma rho hT N g).tsum_eq, neg_neg]

/-- The exact physical product bulk, keeping its eligible-radical sign, cutoff reversal, and complete complex gamma carrier. -/
def radicalBulk (rho : NontrivialZetaZero) (T : ℝ) (N g : ℕ) : ℂ :=
  -(∑ n ∈ Finset.range (N ^ 2),
    (if EtaCoprimeRadical.eligibleRadical g (n + 1) ≤ N then
      (μ (EtaCoprimeRadical.eligibleRadical g (n + 1)) : ℂ) else
      -(μ (EtaCoprimeRadical.eligibleRadical g (n + 1)) : ℂ)) *
        gammaCarrier rho T (n + 1))

/-- The complementary complete infinite physical tail, with the original clipped divisor coefficient. -/
def radicalTail (rho : NontrivialZetaZero) (T : ℝ) (N g : ℕ) : ℂ :=
  -(∑' n : ℕ, (EtaCoprimeRadical.coefficient g N N (N ^ 2 + n + 1) : ℂ) *
    gammaCarrier rho T (N ^ 2 + n + 1))

/-- The signed radical bulk is exactly the finite prefix of the original coprime divisor coefficients, rather than a replacement model. -/
theorem radicalBulk_eq_coefficient_prefix (rho : NontrivialZetaZero) (T : ℝ) (N g : ℕ) :
    radicalBulk rho T N g =
      -(∑ n ∈ Finset.range (N ^ 2), (EtaCoprimeRadical.coefficient g N N (n + 1) : ℂ) *
        gammaCarrier rho T (n + 1)) := by
  unfold radicalBulk
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [EtaCoprimeRadical.coefficient_square_eq_signed_radical g (by omega)
    (by have := Finset.mem_range.mp hn; omega)]
  simp only [Int.cast_ite, Int.cast_neg]

/-- The complete original reduced core is the sign-preserving radical bulk plus the entire omitted physical tail. -/
theorem reducedGcdCore_eq_radicalBulk_add_tail (rho : NontrivialZetaZero)
    {T : ℝ} (hT : 0 < T) (N g : ℕ) :
    reducedGcdCore rho T N g = radicalBulk rho T N g + radicalTail rho T N g := by
  rw [reducedGcdCore_eq_tsum_coefficient rho hT, radicalBulk_eq_coefficient_prefix, radicalTail]
  have hs := (hasSum_coefficient_gamma rho hT N g).summable.sum_add_tsum_nat_add (N ^ 2)
  simp only [Nat.add_comm _ (N ^ 2)] at hs
  rw [← hs]
  ring

/-- The actual product bulk pays at most one copy of each physical gamma norm after exact coprime divisor cancellation. -/
theorem norm_radicalBulk_le (rho : NontrivialZetaZero) (T : ℝ) (N g : ℕ) :
    ‖radicalBulk rho T N g‖ ≤ ∑ n ∈ Finset.range (N ^ 2), ‖gammaCarrier rho T (n + 1)‖ := by
  rw [radicalBulk_eq_coefficient_prefix, norm_neg]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul]
  have hc : ‖(EtaCoprimeRadical.coefficient g N N (n + 1) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast EtaCoprimeRadical.abs_coefficient_le_one g (by omega : 1 ≤ n + 1)
      (by have := Finset.mem_range.mp hn; nlinarith : n + 1 ≤ N * N)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg _)

private theorem norm_gammaCarrier_large_le (rho : NontrivialZetaZero) {T : ℝ} (hT : 0 < T)
    {n : ℕ} (hn : 1 ≤ n) (hTn : 2 * T ≤ n) :
    ‖gammaCarrier rho T n‖ ≤ 8 * ‖pairedEtaXiCompletionFactor rho.1‖ *
      (n : ℝ) ^ (-rho.1.re) * Real.exp (-(n : ℝ) / (2 * T)) := by
  rw [gammaCarrier, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
  have hg := norm_gammaDampedEta_le_exp_half (NontrivialZetaZero.zero_lt_re rho)
    ((le_div_iff₀ hT).mpr hTn)
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq
  rw [show -((n : ℝ) / T) / 2 = -(n : ℝ) / (2 * T) by ring]
  ring

private theorem radicalTail_majorant (rho : NontrivialZetaZero) {T : ℝ} (hT : 0 < T)
    {N : ℕ} (hN : 2 * T ≤ (N : ℝ) ^ 2) (g n : ℕ) :
    ‖(EtaCoprimeRadical.coefficient g N N (N ^ 2 + n + 1) : ℂ) *
      gammaCarrier rho T (N ^ 2 + n + 1)‖ ≤
        (8 * ‖pairedEtaXiCompletionFactor rho.1‖ * (N : ℝ) ^ 2 *
          ((N : ℝ) ^ 2) ^ (-rho.1.re)) *
          Real.exp (-((N ^ 2 + n + 1 : ℕ) : ℝ) * (1 / (2 * T))) := by
  have hN0 : (0 : ℝ) < (N : ℝ) ^ 2 := (by positivity : (0 : ℝ) < 2 * T).trans_le hN
  have hNd : (N : ℝ) ^ 2 ≤ (N ^ 2 + n + 1 : ℕ) := by
    exact_mod_cast (show N ^ 2 ≤ N ^ 2 + n + 1 by omega)
  have hc : ‖(EtaCoprimeRadical.coefficient g N N (N ^ 2 + n + 1) : ℂ)‖ ≤ (N : ℝ) ^ 2 := by
    have hz : |EtaCoprimeRadical.coefficient g N N (N ^ 2 + n + 1)| ≤ (N : ℤ) ^ 2 := by
      exact (EtaCoprimeRadical.abs_coefficient_le_cutoffs g N N (N ^ 2 + n + 1)).trans_eq
        (pow_two (N : ℤ)).symm
    rw [Complex.norm_intCast]
    exact_mod_cast hz
  have hp := Real.rpow_le_rpow_of_nonpos hN0 hNd
    (neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le)
  rw [norm_mul]
  apply (mul_le_mul hc (norm_gammaCarrier_large_le rho hT (by omega) (hN.trans hNd))
    (norm_nonneg _) (sq_nonneg _)).trans
  have hbound := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 8 * ‖pairedEtaXiCompletionFactor rho.1‖))
    (Real.exp_pos (-((N ^ 2 + n + 1 : ℕ) : ℝ) / (2 * T))).le) (sq_nonneg (N : ℝ))
  simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm, mul_comm] using hbound

/-- The entire complementary tail has an unconditional exponential bound; no cancellation between its physical integers is assumed. -/
theorem norm_radicalTail_le (rho : NontrivialZetaZero) {T : ℝ} (hT : 0 < T)
    {N : ℕ} (hN : 2 * T ≤ (N : ℝ) ^ 2) (g : ℕ) :
    ‖radicalTail rho T N g‖ ≤
      16 * ‖pairedEtaXiCompletionFactor rho.1‖ * T * (N : ℝ) ^ 2 *
        ((N : ℝ) ^ 2) ^ (-rho.1.re) * Real.exp (-(N : ℝ) ^ 2 / (2 * T)) := by
  have hx : 0 < 1 / (2 * T) := by positivity
  have hb := (hasSum_exp_nat_tail hx (N ^ 2)).mul_left
    (8 * ‖pairedEtaXiCompletionFactor rho.1‖ * (N : ℝ) ^ 2 * ((N : ℝ) ^ 2) ^ (-rho.1.re))
  have hs : Summable (fun n : ℕ ↦ (EtaCoprimeRadical.coefficient g N N (N ^ 2 + n + 1) : ℂ) *
      gammaCarrier rho T (N ^ 2 + n + 1)) :=
    (hb.summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (radicalTail_majorant rho hT hN g)).of_norm
  rw [radicalTail, norm_neg]
  apply (hs.hasSum.norm_le_of_bounded hb (radicalTail_majorant rho hT hN g)).trans
  have he : 1 / (2 * T) ≤ Real.exp (1 / (2 * T)) - 1 := by
    linarith [Real.add_one_le_exp (1 / (2 * T))]
  rw [← mul_div_assoc]
  calc
    _ ≤ (8 * ‖pairedEtaXiCompletionFactor rho.1‖ * (N : ℝ) ^ 2 * ((N : ℝ) ^ 2) ^ (-rho.1.re) *
        Real.exp (-((N ^ 2 : ℕ) : ℝ) * (1 / (2 * T)))) / (1 / (2 * T)) :=
      div_le_div_of_nonneg_left (by positivity) hx he
    _ = _ := by
      push_cast
      simp only [one_div, div_inv_eq_mul]
      rw [show -(N : ℝ) ^ 2 * (2 * T)⁻¹ = -(N : ℝ) ^ 2 / (2 * T) by ring]
      ring

/-- The original complete reduced gcd core is approximated by its literal radical-sign bulk with a fully proved tail allowance. -/
theorem norm_reducedGcdCore_sub_radicalBulk_le (rho : NontrivialZetaZero)
    {T : ℝ} (hT : 0 < T) {N : ℕ} (hN : 2 * T ≤ (N : ℝ) ^ 2) (g : ℕ) :
    ‖reducedGcdCore rho T N g - radicalBulk rho T N g‖ ≤
      16 * ‖pairedEtaXiCompletionFactor rho.1‖ * T * (N : ℝ) ^ 2 *
        ((N : ℝ) ^ 2) ^ (-rho.1.re) * Real.exp (-(N : ℝ) ^ 2 / (2 * T)) := by
  rw [reducedGcdCore_eq_radicalBulk_add_tail rho hT, add_sub_cancel_left]
  exact norm_radicalTail_le rho hT hN g

end

end RiemannGaussian.EtaGammaGcd

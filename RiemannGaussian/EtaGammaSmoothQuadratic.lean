import RiemannGaussian.EtaGammaFiniteBand

/-!
# The full smooth Möbius quadratic and its complete remainder

The classical truncated Möbius square is retained with its actual omitted
coefficient and a proved exponential tail allowance. Both short copies and
the original source endpoints remain explicit. The quadratic tends to the
nonzero source; its independent signed upper bound remains open.
-/

open Complex Filter MeasureTheory Set RiemannGaussian RiemannGaussian.EtaGammaSmoothing
open scoped Classical Topology ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaQuadratic

noncomputable section

/-- The actual Möbius function restricted to the short interval. -/
def shortMoebius (U : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n ≤ U then (μ n : ℂ) else 0, by simp⟩

/-- The complementary coefficients retain all original signs. -/
def longMoebius (U : ℕ) : ArithmeticFunction ℂ := (μ : ArithmeticFunction ℂ) - shortMoebius U

/-- The complete cofactor coefficient, including every positive triple product. -/
def cofactor (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * f ^ 2

/-- The omitted coefficients vanish below their original cutoff. -/
theorem longMoebius_apply_of_le {U n : ℕ} (hn : n ≤ U) : longMoebius U n = 0 := by
  change (μ n : ℂ) - (if n ≤ U then (μ n : ℂ) else 0) = 0
  rw [if_pos hn, sub_self]

/-- Every actual short coefficient has norm at most one. -/
theorem norm_shortMoebius_le_one (U n : ℕ) : ‖shortMoebius U n‖ ≤ 1 := by
  change ‖if n ≤ U then (μ n : ℂ) else 0‖ ≤ 1
  split_ifs
  · rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  · simp

/-- The same bound holds for the omitted coefficients. -/
theorem norm_longMoebius_le_one (U n : ℕ) : ‖longMoebius U n‖ ≤ 1 := by
  change ‖(μ n : ℂ) - (if n ≤ U then (μ n : ℂ) else 0)‖ ≤ 1
  split_ifs
  · simp
  · rw [sub_zero, Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- Two omitted factors cannot fit below the squared cutoff. -/
theorem longMoebius_square_apply {U n : ℕ} (hn : n ≤ U ^ 2) :
    (longMoebius U ^ 2) n = 0 := by
  rw [pow_two, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases hleft : p.1 ≤ U
  · rw [longMoebius_apply_of_le hleft, zero_mul]
  · have hright : p.2 ≤ U := by
      by_contra h
      have hm := Nat.mul_le_mul (show U + 1 ≤ p.1 by omega) (show U + 1 ≤ p.2 by omega)
      nlinarith
    rw [longMoebius_apply_of_le hright, mul_zero]

/-- The whole omitted cofactor vanishes on the squared interval. -/
theorem cofactor_long_apply_of_le {U n : ℕ} (hn : n ≤ U ^ 2) :
    cofactor (longMoebius U) n = 0 := by
  rw [cofactor, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hpn : p.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) ⟨p.1, by nlinarith⟩
  rw [longMoebius_square_apply (hpn.trans hn), mul_zero]

/-- The global quadratic identity keeps the full omitted square, without a product cutoff. -/
theorem moebius_eq_short_sub_cofactor (U : ℕ) :
    (μ : ArithmeticFunction ℂ) =
      shortMoebius U + shortMoebius U - cofactor (shortMoebius U) + cofactor (longMoebius U) := by
  have he : cofactor (longMoebius U) =
      (μ : ArithmeticFunction ℂ) - (shortMoebius U + shortMoebius U) + cofactor (shortMoebius U) := by
    unfold cofactor longMoebius
    calc
      _ = ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * μ) * μ -
          (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * μ) * shortMoebius U +
            ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * μ) * shortMoebius U) +
              (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * shortMoebius U ^ 2 := by ring
      _ = _ := by rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]; simp
  rw [he]
  ring

/-- A bounded coefficient square is at most the actual divisor count, hence at most its product. -/
theorem norm_square_le_nat (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖(f ^ 2) n‖ ≤ n := by
  rw [pow_two, ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, ‖f p.1 * f p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      rw [norm_mul]
      exact (mul_le_mul (hf _) (hf _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    _ = (n.divisors.card : ℝ) := by rw [← Nat.map_div_right_divisors]; simp
    _ ≤ n := by exact_mod_cast Nat.card_divisors_le_self n

/-- The full triple cofactor has a polynomial envelope independent of its truncation. -/
theorem norm_cofactor_le_square (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖cofactor f n‖ ≤ (n : ℝ) ^ 2 := by
  rw [cofactor, mul_comm, ArithmeticFunction.coe_mul_zeta_apply]
  calc
    _ ≤ ∑ d ∈ n.divisors, ‖(f ^ 2) d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ n.divisors, (n : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact (norm_square_le_nat f hf d).trans (by exact_mod_cast Nat.divisor_le hd)
    _ ≤ (n : ℝ) * n := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self n) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The original completed gamma term before multiplying by an arithmetic coefficient. -/
def gammaCarrier (rho : NontrivialZetaZero) (A : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ (-rho.1) *
    (pairedEtaXiCompletionFactor rho.1 * gammaDampedEta rho.1 ((n : ℝ) / A))

/-- The full smooth carrier has an exponential envelope above twice the physical scale. -/
theorem norm_gammaCarrier_large (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {n : ℕ} (hn : 1 ≤ n) (hAn : 2 * A ≤ n) :
    ‖gammaCarrier rho A n‖ ≤
      8 * ‖pairedEtaXiCompletionFactor rho.1‖ * Real.exp (-(n : ℝ) / (2 * A)) := by
  have hp : (n : ℝ) ^ (-rho.1.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hn) (by linarith [NontrivialZetaZero.zero_lt_re rho])
  have hg := norm_gammaDampedEta_le_exp_half (NontrivialZetaZero.zero_lt_re rho)
    ((le_div_iff₀ hA).mpr hAn)
  rw [gammaCarrier, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
  calc
    _ ≤ 1 * (‖pairedEtaXiCompletionFactor rho.1‖ * (8 * Real.exp (-((n : ℝ) / A) / 2))) :=
      mul_le_mul hp (mul_le_mul_of_nonneg_left hg (norm_nonneg _)) (by positivity) (by norm_num)
    _ = _ := by rw [show -((n : ℝ) / A) / 2 = -(n : ℝ) / (2 * A) by ring]; ring

/-- Half of an exponential absorbs the entire quadratic coefficient envelope. -/
theorem square_mul_exp_le (A : ℝ) (hA : 0 < A) (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x / (2 * A)) ≤ 32 * A ^ 2 * Real.exp (-x / (4 * A)) := by
  have he := Real.sum_le_exp_of_nonneg (show 0 ≤ x / (4 * A) by positivity) 3
  norm_num [Finset.sum_range_succ] at he
  have hpoly : x ^ 2 ≤ 32 * A ^ 2 * Real.exp (x / (4 * A)) := by
    have hdrop : (x / (4 * A)) ^ 2 / 2 ≤ Real.exp (x / (4 * A)) := by
      have hdiv : 0 ≤ x / (4 * A) := by positivity
      linarith
    have hm := mul_le_mul_of_nonneg_left hdrop (show 0 ≤ 32 * A ^ 2 by positivity)
    field_simp at hm
    convert! hm using 1
    ring_nf
  apply (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le).trans_eq
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Every bounded arithmetic cofactor has the same summable exponential tail majorant. -/
theorem cofactor_gamma_majorant (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) (hAn : 2 * A ≤ n) :
    ‖cofactor f n * gammaCarrier rho A n‖ ≤
      (256 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 2) *
        Real.exp (-(n : ℝ) / (4 * A)) := by
  rw [norm_mul]
  calc
    _ ≤ (n : ℝ) ^ 2 * (8 * ‖pairedEtaXiCompletionFactor rho.1‖ *
        Real.exp (-(n : ℝ) / (2 * A))) :=
      mul_le_mul (norm_cofactor_le_square f hf n) (norm_gammaCarrier_large rho hA hn hAn)
        (norm_nonneg _) (by positivity)
    _ = (8 * ‖pairedEtaXiCompletionFactor rho.1‖) *
        ((n : ℝ) ^ 2 * Real.exp (-(n : ℝ) / (2 * A))) := by ring
    _ ≤ (8 * ‖pairedEtaXiCompletionFactor rho.1‖) *
        (32 * A ^ 2 * Real.exp (-(n : ℝ) / (4 * A))) :=
      mul_le_mul_of_nonneg_left (square_mul_exp_le A hA n (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by ring

private theorem cofactor_tail_majorant (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {R : ℕ} (hR : 2 * A ≤ R) (n : ℕ) :
    ‖cofactor f (R + n + 1) * gammaCarrier rho A (R + n + 1)‖ ≤
      (256 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 2) *
        Real.exp (-((R + n + 1 : ℕ) : ℝ) * (1 / (4 * A))) := by
  have hRn : (R : ℝ) ≤ ((R + n + 1 : ℕ) : ℝ) := by exact_mod_cast (show R ≤ R + n + 1 by omega)
  simpa only [div_eq_mul_inv, one_mul] using
    cofactor_gamma_majorant rho hA f hf (by omega : 1 ≤ R + n + 1) (hR.trans hRn)

/-- The complete cofactor series is absolutely convergent before any source identity is used. -/
theorem summable_norm_cofactor_gamma (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) :
    Summable (fun n : ℕ ↦ ‖cofactor f (n + 1) * gammaCarrier rho A (n + 1)‖) := by
  let R : ℕ := ⌈2 * A⌉₊
  have hR : 2 * A ≤ R := Nat.le_ceil _
  have hb := (hasSum_exp_nat_tail (show 0 < 1 / (4 * A) by positivity) R).summable.mul_left
    (256 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 2)
  apply (summable_nat_add_iff R).mp
  apply hb.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro n
  simpa only [Nat.add_comm n R] using cofactor_tail_majorant rho hA f hf hR n

/-- The entire cofactor tail has a uniform exponential allowance, independent of the arithmetic cutoff. -/
theorem norm_tsum_cofactor_gamma_tail_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {R : ℕ} (hR : 2 * A ≤ R) :
    ‖∑' n : ℕ, cofactor f (R + n + 1) * gammaCarrier rho A (R + n + 1)‖ ≤
      1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 3 * Real.exp (-(R : ℝ) / (4 * A)) := by
  have hx : 0 < 1 / (4 * A) := by positivity
  have hb := (hasSum_exp_nat_tail hx R).mul_left
    (256 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 2)
  have hs : Summable (fun n : ℕ ↦ cofactor f (R + n + 1) * gammaCarrier rho A (R + n + 1)) := by
    apply Summable.of_norm
    exact hb.summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (cofactor_tail_majorant rho hA f hf hR)
  have hnorm := hs.hasSum.norm_le_of_bounded hb (cofactor_tail_majorant rho hA f hf hR)
  have he : 1 / (4 * A) ≤ Real.exp (1 / (4 * A)) - 1 := by
    linarith [Real.add_one_le_exp (1 / (4 * A))]
  apply hnorm.trans
  rw [← mul_div_assoc]
  calc
    _ ≤ (256 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 2 *
        Real.exp (-(R : ℝ) * (1 / (4 * A)))) / (1 / (4 * A)) :=
      div_le_div_of_nonneg_left (by positivity) hx he
    _ = _ := by
      simp only [one_div, div_inv_eq_mul]
      rw [show -(R : ℝ) * (4 * A)⁻¹ = -(R : ℝ) / (4 * A) by ring]
      ring

/-- The full smooth quadratic uses every cofactor and both original short Möbius factors. -/
def smoothQuadratic (rho : NontrivialZetaZero) (A : ℝ) (U : ℕ) : ℂ :=
  -∑' n : ℕ, cofactor (shortMoebius U) (n + 1) * gammaCarrier rho A (n + 1)

/-- The exact omitted quadratic contribution, with both long factors retained. -/
def smoothError (rho : NontrivialZetaZero) (A : ℝ) (U : ℕ) : ℂ :=
  ∑' n : ℕ, cofactor (longMoebius U) (n + 1) * gammaCarrier rho A (n + 1)

/-- The omitted double-long contribution is bounded entirely beyond the squared cutoff. -/
theorem norm_smoothError_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {U : ℕ} (hU : 2 * A ≤ (U : ℝ) ^ 2) :
    ‖smoothError rho A U‖ ≤
      1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 3 * Real.exp (-(U : ℝ) ^ 2 / (4 * A)) := by
  have hs := (summable_norm_cofactor_gamma rho hA (longMoebius U) (norm_longMoebius_le_one U)).of_norm
  have he := hs.sum_add_tsum_nat_add (U ^ 2)
  have hh : (∑ n ∈ Finset.range (U ^ 2),
      cofactor (longMoebius U) (n + 1) * gammaCarrier rho A (n + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [cofactor_long_apply_of_le (by have := Finset.mem_range.mp hn; omega), zero_mul]
  rw [hh, zero_add] at he
  unfold smoothError
  rw [← he]
  have hb := norm_tsum_cofactor_gamma_tail_le rho hA (longMoebius U) (norm_longMoebius_le_one U)
    (R := U ^ 2) (by exact_mod_cast hU)
  have hcast : ((U ^ 2 : ℕ) : ℝ) = (U : ℝ) ^ 2 := by norm_cast
  rw [hcast] at hb
  simpa only [Nat.add_comm _ (U ^ 2)] using hb

/-- The short smooth sum is the original finite selected gamma family. -/
theorem hasSum_short_gamma (rho : NontrivialZetaZero) (A : ℝ) (U : ℕ) :
    HasSum (fun n : ℕ ↦ shortMoebius U (n + 1) * gammaCarrier rho A (n + 1))
      (gammaMoebiusSelected rho (Finset.Icc 1 U) A) := by
  have hf : ∀ n ∉ Finset.range U,
      shortMoebius U (n + 1) * gammaCarrier rho A (n + 1) = 0 := by
    intro n hn
    have hUn : ¬ n + 1 ≤ U := by simp only [Finset.mem_range] at hn; omega
    change (if n + 1 ≤ U then (μ (n + 1) : ℂ) else 0) * _ = 0
    rw [if_neg hUn, zero_mul]
  have h : HasSum (fun n : ℕ ↦ shortMoebius U (n + 1) * gammaCarrier rho A (n + 1))
      (∑ n ∈ Finset.range U, shortMoebius U (n + 1) * gammaCarrier rho A (n + 1)) :=
    hasSum_sum_of_ne_finset_zero hf
  convert! h using 1
  rw [gammaMoebiusSelected, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  apply Finset.sum_congr rfl
  intro n hn
  have hnU : n + 1 ≤ U := by have := Finset.mem_range.mp hn; omega
  change gammaMoebiusTerm rho A (n + 1) =
    (if n + 1 ≤ U then (μ (n + 1) : ℂ) else 0) * gammaCarrier rho A (n + 1)
  rw [if_pos hnU]
  simp only [gammaMoebiusTerm, gammaCarrier, mul_assoc]

/-- The exact smoothed quadratic identity retains both short copies and the complete omitted square. -/
theorem source_eq_short_add_quadratic_add_error (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) (U : ℕ) :
    gammaMoebiusSource rho A =
      gammaMoebiusSelected rho (Finset.Icc 1 U) A +
        gammaMoebiusSelected rho (Finset.Icc 1 U) A + smoothQuadratic rho A U + smoothError rho A U := by
  have hshort := hasSum_short_gamma rho A U
  have hq := (summable_norm_cofactor_gamma rho hA (shortMoebius U) (norm_shortMoebius_le_one U)).of_norm.hasSum
  have herr := (summable_norm_cofactor_gamma rho hA (longMoebius U) (norm_longMoebius_le_one U)).of_norm.hasSum
  have hsum := ((hshort.add hshort).sub hq).add herr
  have hc (n : ℕ) : gammaMoebiusTerm rho A (n + 1) =
      (shortMoebius U (n + 1) * gammaCarrier rho A (n + 1) +
        shortMoebius U (n + 1) * gammaCarrier rho A (n + 1) -
          cofactor (shortMoebius U) (n + 1) * gammaCarrier rho A (n + 1)) +
            cofactor (longMoebius U) (n + 1) * gammaCarrier rho A (n + 1) := by
    have hm := DFunLike.congr_fun (moebius_eq_short_sub_cofactor U) (n + 1)
    change (μ (n + 1) : ℂ) = shortMoebius U (n + 1) + shortMoebius U (n + 1) -
      cofactor (shortMoebius U) (n + 1) + cofactor (longMoebius U) (n + 1) at hm
    rw [gammaMoebiusTerm, mul_assoc]
    change (μ (n + 1) : ℂ) * gammaCarrier rho A (n + 1) = _
    rw [hm]
    ring
  simp_rw [← hc] at hsum
  have hh := hsum.unique (hasSum_gammaMoebiusTerm rho hA)
  simpa only [smoothQuadratic, smoothError, sub_eq_add_neg] using hh.symm

/-- All costs of replacing the exact smoothed source by the full smooth quadratic are explicit. -/
theorem norm_smoothQuadratic_sub_source_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) {U : ℕ} (hU : 2 * A ≤ (U : ℝ) ^ 2) :
    ‖smoothQuadratic rho A U - gammaMoebiusSource rho A‖ ≤
      2 * (gammaMoebiusConstant rho / A ^ 3 * (U : ℝ) ^ (4 - rho.1.re)) +
        1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 3 * Real.exp (-(U : ℝ) ^ 2 / (4 * A)) := by
  have he : smoothQuadratic rho A U - gammaMoebiusSource rho A =
      -(gammaMoebiusSelected rho (Finset.Icc 1 U) A +
        gammaMoebiusSelected rho (Finset.Icc 1 U) A + smoothError rho A U) := by
    rw [source_eq_short_add_quadratic_add_error rho hA U]
    ring
  rw [he, norm_neg]
  apply (norm_add_le _ _).trans
  apply add_le_add _ (norm_smoothError_le rho hA hU)
  apply (norm_add_le _ _).trans
  have hb := norm_gammaMoebiusSelected_le rho hA (S := Finset.Icc 1 U) (D := U) (fun _ h ↦ h)
  linarith

/-- The omitted square tends to zero on the explicit sixth/fourth schedule at every actual zero. -/
theorem smoothError_sixth_tendsto_zero (rho : NontrivialZetaZero) :
    Tendsto (fun u : ℕ ↦ smoothError rho ((u : ℝ) ^ 6) (u ^ 4)) atTop (𝓝 0) := by
  have hx : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ 2 / 4) atTop atTop := by
    have hp := (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [div_eq_mul_inv, Function.comp_def] using hp.atTop_mul_const (by norm_num : (0 : ℝ) < (4 : ℝ)⁻¹)
  have hlim := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 9).comp hx).mul_const
    (1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * (4 : ℝ) ^ 9)
  have hb : ∀ᶠ u : ℕ in atTop,
      ‖smoothError rho ((u : ℝ) ^ 6) (u ^ 4)‖ ≤
        ((u : ℝ) ^ 2 / 4) ^ 9 * Real.exp (-((u : ℝ) ^ 2 / 4)) *
          (1024 * ‖pairedEtaXiCompletionFactor rho.1‖ * (4 : ℝ) ^ 9) := by
    filter_upwards [eventually_ge_atTop 2] with u hu
    have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
    have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hu
    have hU : 2 * (u : ℝ) ^ 6 ≤ ((u ^ 4 : ℕ) : ℝ) ^ 2 := by
      push_cast
      nlinarith [mul_nonneg (sq_nonneg ((u : ℝ) ^ 3)) (show 0 ≤ (u : ℝ) ^ 2 - 2 by nlinarith)]
    apply (norm_smoothError_le rho (pow_pos huR 6) hU).trans_eq
    have he : -(((u ^ 4 : ℕ) : ℝ) ^ 2) / (4 * (u : ℝ) ^ 6) = -((u : ℝ) ^ 2 / 4) := by
      push_cast
      field_simp
    rw [he]
    ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hb
    (by simpa only [zero_mul, Function.comp_def] using hlim)

/-- The complete fourth-power short family has a negative exponent at every actual zero. -/
theorem norm_short_sixth_fourth_le (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u) :
    ‖gammaMoebiusSelected rho (Finset.Icc 1 (u ^ 4)) ((u : ℝ) ^ 6)‖ ≤
      gammaMoebiusConstant rho * (u : ℝ) ^ (-2 - 4 * rho.1.re) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  apply (norm_gammaMoebiusSelected_le rho (pow_pos huR 6)
    (S := Finset.Icc 1 (u ^ 4)) (D := u ^ 4) (fun _ h ↦ h)).trans_eq
  simp only [Nat.cast_pow]
  rw [← Real.rpow_natCast_mul huR.le, ← pow_mul, ← Real.rpow_natCast (u : ℝ) (6 * 3),
    div_mul_eq_mul_div, mul_div_assoc, ← Real.rpow_sub huR]
  congr 2
  norm_num
  ring

/-- Both short copies in the smooth quadratic identity tend to zero on the explicit schedule. -/
theorem short_sixth_fourth_tendsto_zero (rho : NontrivialZetaZero) :
    Tendsto (fun u : ℕ ↦ gammaMoebiusSelected rho (Finset.Icc 1 (u ^ 4)) ((u : ℝ) ^ 6))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (-2 - 4 * rho.1.re)) atTop (𝓝 0) := by
    convert! (tendsto_rpow_neg_atTop (show 0 < 2 + 4 * rho.1.re by
      linarith [NontrivialZetaZero.zero_lt_re rho])).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    funext u
    simp only [Function.comp_def]
    congr 1
    ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((eventually_ge_atTop 1).mono fun u hu ↦ norm_short_sixth_fourth_le rho hu)
    (by simpa only [mul_zero] using hp.const_mul (gammaMoebiusConstant rho))

/-- The unchanged two-endpoint smoothed source tends to the original source. -/
theorem source_sixth_tendsto_source (rho : NontrivialZetaZero) :
    Tendsto (fun u : ℕ ↦ gammaMoebiusSource rho ((u : ℝ) ^ 6)) atTop
      (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  have hinv : Tendsto (fun u : ℕ ↦ (u : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb := ((hinv.pow 6).pow 3).const_mul
    (‖pairedEtaXiCompletionFactor rho.1‖ * (1 + 16 * (2 : ℝ) ^ (-rho.1.re)) / 6)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((eventually_ge_atTop (1 : ℕ)).mono fun u hu ↦ norm_gammaMoebiusSource_sub_le rho
      (pow_pos (by exact_mod_cast hu : (0 : ℝ) < u) 6))
  simpa only [div_eq_mul_inv, mul_inv, inv_pow, mul_assoc,
    zero_pow (by decide : 6 ≠ 0), zero_pow (by decide : 3 ≠ 0), mul_zero] using hb

/-- The full smooth quadratic retains the original source at every actual nontrivial zero; no independent upper estimate is asserted. -/
theorem smoothQuadratic_sixth_tendsto_source (rho : NontrivialZetaZero) :
    Tendsto (fun u : ℕ ↦ smoothQuadratic rho ((u : ℝ) ^ 6) (u ^ 4)) atTop
      (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  have ht := (((source_sixth_tendsto_source rho).sub (short_sixth_fourth_tendsto_zero rho)).sub
    (short_sixth_fourth_tendsto_zero rho)).sub (smoothError_sixth_tendsto_zero rho)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with u hu
  have hA : 0 < (u : ℝ) ^ 6 := pow_pos (by exact_mod_cast hu : (0 : ℝ) < u) 6
  rw [source_eq_short_add_quadratic_add_error rho hA (u ^ 4)]
  ring

end

end RiemannGaussian.EtaGammaQuadratic

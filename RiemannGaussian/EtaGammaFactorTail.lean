import RiemannGaussian.EtaGammaBalancedOuter
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Gamma cofactor tails with both factor cutoffs retained

The full triple product is bounded before its two cutoff lengths are
compressed into a coefficient estimate. Three convergent geometric sums
retain the complex-power decay and give `64 norm(chi) A^2 (W V)^(-1-sigma)
exp(-W V/(2 A))`. The actual square and balanced rectangle inherit this
smaller allowance with every short sum and physical endpoint retained.
The independent signed upper bound for the surviving rectangle is open.
-/

open Complex Filter RiemannGaussian RiemannGaussian.EtaGammaSmoothing
open RiemannGaussian.EtaGammaQuadratic RiemannGaussian.EtaGammaRectangular
open scoped Classical Topology ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaFactorTail

noncomputable section

private def toComplex (f : ArithmeticFunction ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ (f n : ℂ), by simp⟩

private theorem toComplex_mul (f g : ArithmeticFunction ℝ) :
    toComplex (f * g) = toComplex f * toComplex g := by
  ext n
  change ((f * g) n : ℂ) = _
  simp only [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul]
  rfl

private theorem hasSum_mul (f g : ArithmeticFunction ℝ) {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun n ↦ (f * g : ArithmeticFunction ℝ) n) (a * b) := by
  have ht (F : ArithmeticFunction ℂ) : LSeries.term F 0 = F := by
    funext n
    simp only [LSeries.term_def₀ ArithmeticFunction.map_zero, neg_zero, Complex.cpow_zero, mul_one]
  have hf' : LSeriesHasSum (toComplex f) 0 (a : ℂ) := by
    change HasSum (LSeries.term (toComplex f) 0) (a : ℂ)
    rw [ht]
    exact Complex.hasSum_ofReal.mpr hf
  have hg' : LSeriesHasSum (toComplex g) 0 (b : ℂ) := by
    change HasSum (LSeries.term (toComplex g) 0) (b : ℂ)
    rw [ht]
    exact Complex.hasSum_ofReal.mpr hg
  have h := ArithmeticFunction.LSeriesHasSum_mul hf' hg'
  rw [← toComplex_mul] at h
  change HasSum (LSeries.term (toComplex (f * g)) 0) ((a : ℂ) * (b : ℂ)) at h
  rw [ht] at h
  have hh : HasSum (fun n ↦ ((f * g : ArithmeticFunction ℝ) n : ℂ)) ((a * b : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul]
    exact h.congr_fun (fun n ↦ rfl)
  exact Complex.hasSum_ofReal.mp hh

private def expWeight (f : ArithmeticFunction ℂ) (x : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ ‖f n‖ * Real.exp (-(n : ℝ) * x), by simp⟩

private theorem expWeight_nonneg (f : ArithmeticFunction ℂ) (x : ℝ) (n : ℕ) :
    0 ≤ expWeight f x n := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

private theorem summable_expWeight (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℝ} (hx : 0 < x) : Summable (expWeight f x) := by
  apply (summable_nat_add_iff 1).mp
  apply (hasSum_exp_nat_tail hx 0).summable.of_nonneg_of_le
  · intro n
    exact expWeight_nonneg f x (n + 1)
  · intro n
    change ‖f (n + 1)‖ * Real.exp (-((n + 1 : ℕ) : ℝ) * x) ≤ _
    simpa only [Nat.zero_add, one_mul] using mul_le_mul_of_nonneg_right
      (hf (n + 1)) (Real.exp_pos (-((n + 1 : ℕ) : ℝ) * x)).le

private theorem tsum_expWeight_le (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℝ} (hx : 0 < x) (W : ℕ)
    (hf0 : ∀ n ≤ W, f n = 0) :
    (∑' n, expWeight f x n) ≤ Real.exp (-(W : ℝ) * x) / x := by
  have hs := summable_expWeight f hf hx
  have he := hs.sum_add_tsum_nat_add (W + 1)
  have hz : (∑ n ∈ Finset.range (W + 1), expWeight f x n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    change ‖f n‖ * Real.exp (-(n : ℝ) * x) = 0
    rw [hf0 n (by have := Finset.mem_range.mp hn; omega), norm_zero, zero_mul]
  rw [hz, zero_add] at he
  rw [← he]
  have hb := hasSum_exp_nat_tail hx W
  have hpoint (n : ℕ) : expWeight f x (n + (W + 1)) ≤
      Real.exp (-((W + n + 1 : ℕ) : ℝ) * x) := by
    change ‖f (n + (W + 1))‖ * Real.exp (-((n + (W + 1) : ℕ) : ℝ) * x) ≤ _
    simpa only [one_mul, show n + (W + 1) = W + n + 1 by omega] using
      mul_le_mul_of_nonneg_right (hf (n + (W + 1))) (Real.exp_pos _).le
  apply ((hs.comp_injective (fun a b h ↦ by omega)).tsum_le_tsum hpoint hb.summable).trans
  rw [hb.tsum_eq]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hx
    (by linarith [Real.add_one_le_exp x])

private theorem norm_gammaCarrier_large_power (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {n : ℕ} (hn : 1 ≤ n) (hAn : 2 * A ≤ n) :
    ‖gammaCarrier rho A n‖ ≤ 8 * ‖pairedEtaXiCompletionFactor rho.1‖ *
      (n : ℝ) ^ (-rho.1.re) * Real.exp (-(n : ℝ) / (2 * A)) := by
  rw [gammaCarrier, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
  have hg := norm_gammaDampedEta_le_exp_half (NontrivialZetaZero.zero_lt_re rho)
    ((le_div_iff₀ hA).mpr hAn)
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq
  rw [show -((n : ℝ) / A) / 2 = -(n : ℝ) / (2 * A) by ring]
  ring

private theorem factor_product_lower {W V a b k : ℝ}
    (hW : 0 ≤ W) (hV : 0 ≤ V) (ha : W ≤ a) (hb : V ≤ b) (hk : 1 ≤ k) :
    a * V + b * W + k * (W * V) - 2 * (W * V) ≤ a * b * k := by
  have hab : W * V ≤ a * b := mul_le_mul ha hb hV (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb),
    mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hk)]

private def factorConstant (rho : NontrivialZetaZero) (A : ℝ) (W V : ℕ) : ℝ :=
  8 * ‖pairedEtaXiCompletionFactor rho.1‖ * ((W : ℝ) * V) ^ (-rho.1.re) *
    Real.exp ((W : ℝ) * V / A)

private theorem factorConstant_nonneg (rho : NontrivialZetaZero) (A : ℝ) (W V : ℕ) :
    0 ≤ factorConstant rho A W V := by
  unfold factorConstant
  positivity

private theorem norm_triple_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (f g : ArithmeticFunction ℂ) {W V : ℕ}
    (hf0 : ∀ n ≤ W, f n = 0) (hg0 : ∀ n ≤ V, g n = 0)
    (hWV : 2 * A ≤ (W : ℝ) * V) (a b : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ‖f a * g b * gammaCarrier rho A (a * b * k)‖ ≤
      factorConstant rho A W V * expWeight f ((V : ℝ) / (2 * A)) a *
        expWeight g ((W : ℝ) / (2 * A)) b *
          Real.exp (-(k : ℝ) * ((W : ℝ) * V / (2 * A))) := by
  by_cases ha : a ≤ W
  · rw [hf0 a ha, zero_mul, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (factorConstant_nonneg rho A W V)
      (expWeight_nonneg f _ a)) (expWeight_nonneg g _ b)) (Real.exp_pos _).le
  by_cases hb : b ≤ V
  · rw [hg0 b hb, mul_zero, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (factorConstant_nonneg rho A W V)
      (expWeight_nonneg f _ a)) (expWeight_nonneg g _ b)) (Real.exp_pos _).le
  have hWVp : 0 < (W : ℝ) * V := (by positivity : 0 < 2 * A).trans_le hWV
  have haR : (W : ℝ) ≤ a := by exact_mod_cast (show W ≤ a by omega)
  have hbR : (V : ℝ) ≤ b := by exact_mod_cast (show V ≤ b by omega)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn : 1 ≤ a * b * k := by
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hnR : (W : ℝ) * V ≤ ((a * b * k : ℕ) : ℝ) := by
    push_cast
    calc
      (W : ℝ) * V ≤ (a : ℝ) * b := mul_le_mul haR hbR (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ ≤ (a : ℝ) * b * k := le_mul_of_one_le_right (by positivity) hkR
  have hp := Real.rpow_le_rpow_of_nonpos hWVp hnR
    (neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le)
  have he : Real.exp (-((a * b * k : ℕ) : ℝ) / (2 * A)) ≤
      Real.exp ((W : ℝ) * V / A) * Real.exp (-(a : ℝ) * ((V : ℝ) / (2 * A))) *
        Real.exp (-(b : ℝ) * ((W : ℝ) / (2 * A))) *
          Real.exp (-(k : ℝ) * ((W : ℝ) * V / (2 * A))) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ht := factor_product_lower (Nat.cast_nonneg W) (Nat.cast_nonneg V) haR hbR hkR
    have hd := div_le_div_of_nonneg_right ht (show 0 ≤ 2 * A by positivity)
    push_cast
    convert! neg_le_neg hd using 1 <;> ring
  rw [norm_mul, norm_mul]
  apply (mul_le_mul_of_nonneg_left (norm_gammaCarrier_large_power rho hA hn (hWV.trans hnR))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul
    (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 8 * ‖pairedEtaXiCompletionFactor rho.1‖))
    he (Real.exp_pos _).le (by positivity)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq
  simp only [factorConstant, expWeight, ArithmeticFunction.coe_mk]
  ring

private def factorMajorant (f g : ArithmeticFunction ℂ) (A : ℝ) (W V : ℕ) : ArithmeticFunction ℝ :=
  expWeight (ArithmeticFunction.zeta : ArithmeticFunction ℂ) ((W : ℝ) * V / (2 * A)) *
    (expWeight f ((V : ℝ) / (2 * A)) * expWeight g ((W : ℝ) / (2 * A)))

private theorem norm_mixed_le_majorant (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (f g : ArithmeticFunction ℂ) {W V : ℕ}
    (hf0 : ∀ n ≤ W, f n = 0) (hg0 : ∀ n ≤ V, g n = 0)
    (hWV : 2 * A ≤ (W : ℝ) * V) (n : ℕ) :
    ‖mixedCofactor f g n * gammaCarrier rho A n‖ ≤
      factorConstant rho A W V * factorMajorant f g A W V n := by
  unfold mixedCofactor factorMajorant
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.sum_mul, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hk : 1 ≤ p.1 := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hp).1
  have hz : (ArithmeticFunction.zeta : ArithmeticFunction ℂ) p.1 = 1 := by
    simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne (by omega : p.1 ≠ 0), Nat.cast_one]
  rw [hz, one_mul, ArithmeticFunction.mul_apply, Finset.sum_mul]
  change ‖∑ q ∈ p.2.divisorsAntidiagonal, f q.1 * g q.2 * gammaCarrier rho A n‖ ≤
    factorConstant rho A W V *
      ((‖(ArithmeticFunction.zeta : ArithmeticFunction ℂ) p.1‖ *
        Real.exp (-(p.1 : ℝ) * ((W : ℝ) * V / (2 * A)))) *
        (expWeight f ((V : ℝ) / (2 * A)) * expWeight g ((W : ℝ) / (2 * A))) p.2)
  rw [hz, norm_one, one_mul, ArithmeticFunction.mul_apply, Finset.mul_sum, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  have hn : q.1 * q.2 * p.1 = n := by
    rw [(Nat.mem_divisorsAntidiagonal.mp hq).1, Nat.mul_comm,
      (Nat.mem_divisorsAntidiagonal.mp hp).1]
  have h := norm_triple_le rho hA f g hf0 hg0 hWV q.1 q.2 hk
  rw [hn] at h
  exact h.trans_eq (by ring)

private theorem norm_zeta_le_one (n : ℕ) :
    ‖(ArithmeticFunction.zeta : ArithmeticFunction ℂ) n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hn,
      Nat.cast_one, norm_one, le_refl]

private theorem tsum_expWeight_zeta_le {x : ℝ} (hx : 1 ≤ x) :
    (∑' n, expWeight (ArithmeticFunction.zeta : ArithmeticFunction ℂ) x n) ≤
      2 * Real.exp (-x) := by
  have hxp : 0 < x := by linarith
  have hh : HasSum (fun n : ℕ ↦
      expWeight (ArithmeticFunction.zeta : ArithmeticFunction ℂ) x (n + 1))
      (1 / (Real.exp x - 1)) := by
    convert! (hasSum_exp_nat_tail hxp 0).congr_fun (fun n ↦ ?_) using 1
    · simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero]
    · change ‖(ArithmeticFunction.zeta : ArithmeticFunction ℂ) (n + 1)‖ *
        Real.exp (-((n + 1 : ℕ) : ℝ) * x) = Real.exp (-((0 + n + 1 : ℕ) : ℝ) * x)
      simp only [ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply_ne (by omega : n + 1 ≠ 0), Nat.cast_one, norm_one,
        one_mul, Nat.zero_add]
  have hfull : HasSum (expWeight (ArithmeticFunction.zeta : ArithmeticFunction ℂ) x)
      (1 / (Real.exp x - 1)) := by
    have h := (hasSum_nat_add_iff 1).mp hh
    simpa only [Finset.sum_range_one, ArithmeticFunction.map_zero, add_zero] using h
  rw [hfull.tsum_eq]
  have hE : 2 ≤ Real.exp x := by
    have h1 := Real.add_one_le_exp (1 : ℝ)
    have h2 := Real.exp_le_exp.mpr hx
    linarith
  have hb : 1 / (Real.exp x - 1) ≤ 2 / Real.exp x :=
    (div_le_div_iff₀ (by linarith : 0 < Real.exp x - 1) (Real.exp_pos x)).mpr (by linarith)
  simpa only [Real.exp_neg, div_eq_mul_inv] using hb

/-- The explicit tail allowance retains both original factor lengths and the complex-power decay. -/
def productTailAllowance (rho : NontrivialZetaZero) (A : ℝ) (W V : ℕ) : ℝ :=
  64 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 2 / ((W : ℝ) * V) *
    ((W : ℝ) * V) ^ (-rho.1.re) * Real.exp (-((W : ℝ) * V) / (2 * A))

/-- Keeping both factor cutoffs gives a direct exponential bound for the entire omitted cofactor. -/
theorem norm_evaluate_mixed_factor_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    (f g : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    {W V : ℕ} (hf0 : ∀ n ≤ W, f n = 0) (hg0 : ∀ n ≤ V, g n = 0)
    (hWV : 2 * A ≤ (W : ℝ) * V) :
    ‖evaluate rho A (mixedCofactor f g)‖ ≤ productTailAllowance rho A W V := by
  unfold productTailAllowance
  have hWVp : 0 < (W : ℝ) * V := (by positivity : 0 < 2 * A).trans_le hWV
  have hW : (0 : ℝ) < W := by nlinarith [(Nat.cast_nonneg V : (0 : ℝ) ≤ V)]
  have hV : (0 : ℝ) < V := by nlinarith [(Nat.cast_nonneg W : (0 : ℝ) ≤ W)]
  let F := expWeight f ((V : ℝ) / (2 * A))
  let G := expWeight g ((W : ℝ) / (2 * A))
  let Z := expWeight (ArithmeticFunction.zeta : ArithmeticFunction ℂ) ((W : ℝ) * V / (2 * A))
  have hF := summable_expWeight f hf (div_pos hV (by positivity : 0 < 2 * A))
  have hG := summable_expWeight g hg (div_pos hW (by positivity : 0 < 2 * A))
  have hZ := summable_expWeight (ArithmeticFunction.zeta : ArithmeticFunction ℂ) norm_zeta_le_one
    (div_pos hWVp (by positivity : 0 < 2 * A))
  have hH : HasSum (factorMajorant f g A W V)
      ((∑' n, Z n) * ((∑' n, F n) * (∑' n, G n))) :=
    hasSum_mul Z (F * G) hZ.hasSum (hasSum_mul F G hF.hasSum hG.hasSum)
  have hmajor : HasSum (fun n : ℕ ↦
      factorConstant rho A W V * factorMajorant f g A W V (n + 1))
      (factorConstant rho A W V * ((∑' n, Z n) * ((∑' n, F n) * (∑' n, G n)))) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ ↦
      factorConstant rho A W V * factorMajorant f g A W V n) 1).mpr
    simpa only [Finset.sum_range_one, ArithmeticFunction.map_zero, mul_zero, add_zero] using
      hH.mul_left (factorConstant rho A W V)
  have hnorm := (summable_norm_mixed_gamma rho hA f g hf hg).of_norm.hasSum.norm_le_of_bounded
    hmajor (fun n ↦ norm_mixed_le_majorant rho hA f g hf0 hg0 hWV (n + 1))
  change ‖evaluate rho A (mixedCofactor f g)‖ ≤ _ at hnorm
  have hFb := tsum_expWeight_le f hf (div_pos hV (by positivity : 0 < 2 * A)) W hf0
  have hGb := tsum_expWeight_le g hg (div_pos hW (by positivity : 0 < 2 * A)) V hg0
  have hZb := tsum_expWeight_zeta_le (x := (W : ℝ) * V / (2 * A))
    ((le_div_iff₀ (by positivity : 0 < 2 * A)).mpr (by simpa only [one_mul] using hWV))
  have hFn : 0 ≤ ∑' n, F n := tsum_nonneg (expWeight_nonneg f _)
  have hGn : 0 ≤ ∑' n, G n := tsum_nonneg (expWeight_nonneg g _)
  apply hnorm.trans
  have hFG := mul_le_mul hFb hGb hGn (by positivity)
  have hZFG := mul_le_mul hZb hFG (mul_nonneg hFn hGn) (by positivity)
  apply (mul_le_mul_of_nonneg_left hZFG (factorConstant_nonneg rho A W V)).trans_eq
  have he : Real.exp ((W : ℝ) * V / A) *
      (Real.exp (-((W : ℝ) * V) / (2 * A))) ^ 3 =
        Real.exp (-((W : ℝ) * V) / (2 * A)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = 64 * ‖pairedEtaXiCompletionFactor rho.1‖ * A ^ 2 / ((W : ℝ) * V) *
        ((W : ℝ) * V) ^ (-rho.1.re) *
          (Real.exp ((W : ℝ) * V / A) * (Real.exp (-((W : ℝ) * V) / (2 * A))) ^ 3) := by
      unfold factorConstant
      rw [show -(W : ℝ) * ((V : ℝ) / (2 * A)) = -((W : ℝ) * V) / (2 * A) by ring,
        show -(V : ℝ) * ((W : ℝ) / (2 * A)) = -((W : ℝ) * V) / (2 * A) by ring,
        show -((W : ℝ) * V / (2 * A)) = -((W : ℝ) * V) / (2 * A) by ring]
      field_simp
      ring
    _ = _ := by rw [he]

/-- The actual omitted square satisfies the sharper factor estimate at every admissible scale. -/
theorem norm_smoothError_factor_le (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {U : ℕ} (hU : 2 * A ≤ (U : ℝ) ^ 2) :
    ‖smoothError rho A U‖ ≤ productTailAllowance rho A U U := by
  have he : smoothError rho A U =
      evaluate rho A (mixedCofactor (longMoebius U) (longMoebius U)) := by
    simp only [smoothError, evaluate, mixedCofactor, cofactor, pow_two]
  rw [he]
  exact norm_evaluate_mixed_factor_le rho hA (longMoebius U) (longMoebius U)
    (norm_longMoebius_le_one U) (norm_longMoebius_le_one U)
    (fun _ hn ↦ longMoebius_apply_of_le hn) (fun _ hn ↦ longMoebius_apply_of_le hn)
    (by simpa only [pow_two] using hU)

/-- The full source comparison keeps both short sums and the sharper complete cofactor allowance. -/
theorem norm_smoothRectangle_sub_source_factor_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) (L V : ℕ) (hLV : 2 * A ≤ (L : ℝ) * V) :
    ‖smoothRectangle rho A L V - gammaMoebiusSource rho A‖ ≤
      gammaMoebiusConstant rho / A ^ 3 * (L : ℝ) ^ (4 - rho.1.re) +
        gammaMoebiusConstant rho / A ^ 3 * (V : ℝ) ^ (4 - rho.1.re) +
          productTailAllowance rho A L V := by
  have hi : smoothRectangle rho A L V - gammaMoebiusSource rho A =
      -(gammaMoebiusSelected rho (Finset.Icc 1 L) A +
          gammaMoebiusSelected rho (Finset.Icc 1 V) A +
            evaluate rho A (mixedCofactor (longMoebius L) (longMoebius V))) := by
    rw [source_eq_shorts_add_rectangle_add_error rho hA L V]
    ring
  rw [hi, norm_neg]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    exact add_le_add (norm_gammaMoebiusSelected_le rho hA (fun _ h ↦ h))
      (norm_gammaMoebiusSelected_le rho hA (fun _ h ↦ h))
  · exact norm_evaluate_mixed_factor_le rho hA (longMoebius L) (longMoebius V)
      (norm_longMoebius_le_one L) (norm_longMoebius_le_one V)
      (fun _ hn ↦ longMoebius_apply_of_le hn) (fun _ hn ↦ longMoebius_apply_of_le hn) hLV

open EtaGammaBalancedOuter in
/-- All balanced source costs remain explicit, with the full improved cofactor allowance paid five times. -/
theorem norm_balancedRectangle_sub_source_factor_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) {L : ℕ} (hL : 1 ≤ L) (V : ℕ) (hLV : 2 * A ≤ (L : ℝ) * V) :
    ‖balancedRectangle rho A L V - pairedEtaCompletedMoebiusSource rho‖ ≤
      gammaMoebiusConstant rho / A ^ 3 * (L : ℝ) ^ (4 - rho.1.re) +
        gammaMoebiusConstant rho / A ^ 3 * (V : ℝ) ^ (4 - rho.1.re) +
          32 * gammaMoebiusConstant rho / A ^ 3 * (L : ℝ) ^ 4 +
            5 * productTailAllowance rho A L V +
              ‖pairedEtaXiCompletionFactor rho.1‖ * (1 + 16 * (2 : ℝ) ^ (-rho.1.re)) / (6 * A ^ 3) := by
  have hband : ‖evaluate rho A (mixedCofactor (unitBand L) (shortMoebius V))‖ ≤
      8 * gammaMoebiusConstant rho / A ^ 3 * (L : ℝ) ^ 4 + productTailAllowance rho A L V := by
    rw [evaluate_unitBand_short_eq rho hA]
    exact (norm_sub_le _ _).trans (add_le_add (norm_unitBandLow_le rho hA L)
      (norm_evaluate_mixed_factor_le rho hA (unitBand L) (longMoebius V)
        (norm_unitBand_le_one L) (norm_longMoebius_le_one V)
        (fun _ hn ↦ unitBand_apply_of_le hn) (fun _ hn ↦ longMoebius_apply_of_le hn) hLV))
  have hchange : ‖balancedRectangle rho A L V - smoothRectangle rho A L V‖ ≤
      4 * (8 * gammaMoebiusConstant rho / A ^ 3 * (L : ℝ) ^ 4 + productTailAllowance rho A L V) := by
    rw [balancedRectangle_eq_original_sub rho hA, sub_sub_cancel_left, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (abs_balancingConstant_le_four hL) hband (norm_nonneg _) (by norm_num)
  have he : balancedRectangle rho A L V - pairedEtaCompletedMoebiusSource rho =
      (balancedRectangle rho A L V - smoothRectangle rho A L V) +
        (smoothRectangle rho A L V - gammaMoebiusSource rho A) +
          (gammaMoebiusSource rho A - pairedEtaCompletedMoebiusSource rho) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  apply (add_le_add (add_le_add hchange (norm_smoothRectangle_sub_source_factor_le rho hA L V hLV))
    (norm_gammaMoebiusSource_sub_le rho hA)).trans_eq
  ring

/-- On the square schedule, the entire omitted cofactor is at most `64 norm(chi) exp(-u^2/2)` right of the critical line. -/
theorem norm_smoothError_sixth_factor_le (rho : NontrivialZetaZero)
    (hrho : (1 : ℝ) / 2 ≤ rho.1.re) {u : ℕ} (hu : 2 ≤ u) :
    ‖smoothError rho ((u : ℝ) ^ 6) (u ^ 4)‖ ≤
      64 * ‖pairedEtaXiCompletionFactor rho.1‖ * Real.exp (-(u : ℝ) ^ 2 / 2) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
  have hU1 : (1 : ℝ) ≤ (u : ℝ) ^ 4 := one_le_pow₀ hu1
  have hAU : 2 * (u : ℝ) ^ 6 ≤ ((u ^ 4 : ℕ) : ℝ) ^ 2 := by
    push_cast
    have h2 : (2 : ℝ) ≤ (u : ℝ) ^ 2 := by
      have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hu
      nlinarith
    nlinarith [mul_nonneg (show 0 ≤ (u : ℝ) ^ 2 - 2 by linarith)
      (show 0 ≤ (u : ℝ) ^ 6 by positivity)]
  apply (norm_smoothError_factor_le rho (pow_pos huR 6) hAU).trans
  unfold productTailAllowance
  push_cast
  have hp : ((u : ℝ) ^ 4 * (u : ℝ) ^ 4) ^ (-rho.1.re) ≤ ((u : ℝ) ^ 4)⁻¹ := by
    rw [← pow_two, ← Real.rpow_natCast_mul (by positivity : 0 ≤ (u : ℝ) ^ 4)]
    have hh := Real.rpow_le_rpow_of_exponent_le hU1 (show (2 : ℝ) * -rho.1.re ≤ -1 by linarith)
    simpa only [Nat.cast_ofNat, Real.rpow_neg_one] using hh
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity))
    (Real.exp_pos _).le).trans_eq
  have he : -((u : ℝ) ^ 4 * (u : ℝ) ^ 4) / (2 * (u : ℝ) ^ 6) = -(u : ℝ) ^ 2 / 2 := by
    field_simp
  rw [he]
  field_simp

/-- Both short copies, the sharper square tail, and both physical source endpoints are paid in full. -/
theorem norm_smoothQuadratic_sixth_sub_source_factor_le (rho : NontrivialZetaZero)
    (hrho : (1 : ℝ) / 2 ≤ rho.1.re) {u : ℕ} (hu : 2 ≤ u) :
    ‖smoothQuadratic rho ((u : ℝ) ^ 6) (u ^ 4) - pairedEtaCompletedMoebiusSource rho‖ ≤
      2 * gammaMoebiusConstant rho * (u : ℝ) ^ (-2 - 4 * rho.1.re) +
        64 * ‖pairedEtaXiCompletionFactor rho.1‖ * Real.exp (-(u : ℝ) ^ 2 / 2) +
          ‖pairedEtaXiCompletionFactor rho.1‖ * (1 + 16 * (2 : ℝ) ^ (-rho.1.re)) /
            (6 * ((u : ℝ) ^ 6) ^ 3) := by
  have hA : 0 < (u : ℝ) ^ 6 := pow_pos (by exact_mod_cast (show 0 < u by omega)) 6
  have he : smoothQuadratic rho ((u : ℝ) ^ 6) (u ^ 4) - pairedEtaCompletedMoebiusSource rho =
      -(gammaMoebiusSelected rho (Finset.Icc 1 (u ^ 4)) ((u : ℝ) ^ 6) +
          gammaMoebiusSelected rho (Finset.Icc 1 (u ^ 4)) ((u : ℝ) ^ 6) +
            smoothError rho ((u : ℝ) ^ 6) (u ^ 4)) +
        (gammaMoebiusSource rho ((u : ℝ) ^ 6) - pairedEtaCompletedMoebiusSource rho) := by
    rw [source_eq_short_add_quadratic_add_error rho hA (u ^ 4)]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_neg]
  apply add_le_add _ (norm_gammaMoebiusSource_sub_le rho hA)
  apply (norm_add_le _ _).trans
  apply add_le_add _ (norm_smoothError_sixth_factor_le rho hrho hu)
  apply (norm_add_le _ _).trans
  have hs := norm_short_sixth_fourth_le rho (show 1 ≤ u by omega)
  linarith

end

end RiemannGaussian.EtaGammaFactorTail

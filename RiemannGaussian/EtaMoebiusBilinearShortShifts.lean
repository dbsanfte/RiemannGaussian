import RiemannGaussian.EtaMoebiusBilinearDiagonal
import Mathlib.Data.Nat.Dist

/-!
# Eliminating a growing band of short product shifts

The summable collision mass controls more than the diagonal: a band of
radius `H` has at most `2H+1` entries in each row. Applying the finite
quadratic estimate to the actual phased coefficients bounds all these
interactions together. The complementary signed complex form is retained
exactly. Its long product shifts still require an arithmetic estimate.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

private theorem card_short_product_band_le (N H n : ℕ) :
    ((Finset.Icc 1 N).filter (fun m ↦ Nat.dist n m ≤ H)).card ≤ 2 * H + 1 := by
  have hs : (Finset.Icc 1 N).filter (fun m ↦ Nat.dist n m ≤ H) ⊆
      Finset.Icc (n - H) (n + H) := by
    intro m hm
    have hd := (Finset.mem_filter.mp hm).2
    simp only [Nat.dist] at hd
    apply Finset.mem_Icc.mpr
    omega
  have hc := Finset.card_le_card hs
  rw [Nat.card_Icc] at hc
  omega

private theorem norm_window_pair_le (A L n m : ℕ) (a b : ℂ) :
    ‖(pairedEtaBilinearPrefixWindowKernel A L n m : ℂ) * a * starRingEnd ℂ b‖ ≤
      (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
  obtain ⟨hK0, hK1⟩ := pairedEtaBilinearPrefixWindowKernel_bounds A L n m
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK0, norm_conj]
  have hp := mul_le_mul_of_nonneg_right hK1 (mul_nonneg (norm_nonneg a) (norm_nonneg b))
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

private theorem norm_short_product_form_le (A L H : ℕ) (v : ℕ → ℂ) :
    ‖∑ n ∈ Finset.Icc 1 (A + L), ∑ m ∈ (Finset.Icc 1 (A + L)).filter (fun m ↦ Nat.dist n m ≤ H),
        (pairedEtaBilinearPrefixWindowKernel A L n m : ℂ) * v n * starRingEnd ℂ (v m)‖ ≤
      (2 * (H : ℝ) + 1) * ∑ n ∈ Finset.Icc 1 (A + L), ‖v n‖ ^ 2 := by
  let I := Finset.Icc 1 (A + L)
  have hswap : (∑ n ∈ I, ∑ m ∈ I.filter (fun m ↦ Nat.dist n m ≤ H), ‖v m‖ ^ 2) =
      ∑ n ∈ I, ∑ m ∈ I.filter (fun m ↦ Nat.dist n m ≤ H), ‖v n‖ ^ 2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    rw [Nat.dist_comm m n]
  calc
    _ ≤ ∑ n ∈ I, ∑ m ∈ I.filter (fun m ↦ Nat.dist n m ≤ H),
        (‖v n‖ ^ 2 + ‖v m‖ ^ 2) / 2 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ ↦ norm_window_pair_le A L n m (v n) (v m)))
    _ = ∑ n ∈ I, ((I.filter (fun m ↦ Nat.dist n m ≤ H)).card : ℝ) * ‖v n‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_div]
      rw [hswap]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ n ∈ I, (2 * (H : ℝ) + 1) * ‖v n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast card_short_product_band_le (A + L) H n
    _ = _ := by rw [Finset.mul_sum]

private theorem norm_product_term_sq (rho : NontrivialZetaZero) (D : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖(pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1)‖ ^ 2 =
      (pairedEtaMoebiusHighProductCoefficient D n : ℝ) ^ 2 * (n : ℝ) ^ (-(2 * rho.1.re)) := by
  rw [norm_mul, mul_pow, Complex.norm_intCast, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
  simp only [sq_abs]
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  congr 1
  congr 1
  norm_num
  ring

/-- The completed contribution from the diagonal and all product pairs within the specified additive distance; all original coefficients, phases and window weights remain present. -/
def pairedEtaCompletedMoebiusBilinearNearForm (rho : NontrivialZetaZero) (A L D H : ℕ) : ℂ :=
  (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 *
    ∑ n ∈ Finset.Icc 1 (A + L),
      ∑ m ∈ (Finset.Icc 1 (A + L)).filter (fun m ↦ Nat.dist n m ≤ H),
        (pairedEtaBilinearPrefixWindowKernel A L n m : ℂ) *
          (pairedEtaMoebiusHighProductCoefficient D n : ℂ) *
          (pairedEtaMoebiusHighProductCoefficient D m : ℂ) *
          (n : ℂ) ^ (-rho.1) * starRingEnd ℂ ((m : ℂ) ^ (-rho.1))

/-- The signed complex contribution of every complementary long product shift in the original physical matrix. -/
def pairedEtaCompletedMoebiusBilinearFarForm (rho : NontrivialZetaZero) (A L D H : ℕ) : ℂ :=
  (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 *
    ∑ n ∈ Finset.Icc 1 (A + L),
      ∑ m ∈ (Finset.Icc 1 (A + L)).filter (fun m ↦ H < Nat.dist n m),
        (pairedEtaBilinearPrefixWindowKernel A L n m : ℂ) *
          (pairedEtaMoebiusHighProductCoefficient D n : ℂ) *
          (pairedEtaMoebiusHighProductCoefficient D m : ℂ) *
          (n : ℂ) ^ (-rho.1) * starRingEnd ℂ ((m : ℂ) ^ (-rho.1))

/-- The original full high energy is exactly the sum of its short and long product-shift forms, before taking real parts or estimating either term. -/
theorem pairedEtaCompletedMoebiusLargeMeanSquare_eq_near_add_far
    (rho : NontrivialZetaZero) (A L D H : ℕ) :
    (pairedEtaCompletedMoebiusLargeMeanSquare rho A L D : ℂ) =
      pairedEtaCompletedMoebiusBilinearNearForm rho A L D H +
        pairedEtaCompletedMoebiusBilinearFarForm rho A L D H := by
  rw [pairedEtaCompletedMoebiusLargeMeanSquare_eq_bilinear_window,
    pairedEtaCompletedMoebiusBilinearNearForm, pairedEtaCompletedMoebiusBilinearFarForm, ← mul_add]
  apply congrArg (fun z : ℂ ↦ (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 * z)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : Nat.dist n m ≤ H
  · simp [h, not_lt.mpr h]
  · simp [h, Nat.lt_of_not_ge h]

/-- The entire short-shift form has a uniform power bound with only its actual row-count cost. Both positive and negative cross terms are covered by the same proved estimate. -/
theorem norm_pairedEtaCompletedMoebiusBilinearNearForm_le_power
    (rho : NontrivialZetaZero) {p : ℝ} (hp : 1 < p) (hpr : p ≤ 2 * rho.1.re)
    {D : ℕ} (hD : 1 ≤ D) (A L H : ℕ) :
    ‖pairedEtaCompletedMoebiusBilinearNearForm rho A L D H‖ ≤
      (2 * (H : ℝ) + 1) * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 *
        divisorSquareDirichletMass p * (D : ℝ) ^ (p - 2 * rho.1.re) := by
  have he : pairedEtaCompletedMoebiusBilinearNearForm rho A L D H =
      (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 *
        ∑ n ∈ Finset.Icc 1 (A + L),
          ∑ m ∈ (Finset.Icc 1 (A + L)).filter (fun m ↦ Nat.dist n m ≤ H),
            (pairedEtaBilinearPrefixWindowKernel A L n m : ℂ) *
              ((pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1)) *
              starRingEnd ℂ ((pairedEtaMoebiusHighProductCoefficient D m : ℂ) * (m : ℂ) ^ (-rho.1)) := by
    simp only [pairedEtaCompletedMoebiusBilinearNearForm, map_mul, map_intCast]
    apply congrArg (fun z : ℂ ↦ (‖pairedEtaXiCompletionFactor rho.1‖ : ℂ) ^ 2 * z)
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [he, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  have hb := norm_short_product_form_le A L H
    (fun n ↦ (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1))
  have hs : (∑ n ∈ Finset.Icc 1 (A + L),
      ‖(pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1)‖ ^ 2) ≤
        divisorSquareDirichletMass p * (D : ℝ) ^ (p - 2 * rho.1.re) := by
    convert sum_sq_pairedEtaMoebiusHighProductCoefficient_mul_rpow_neg_le hp hpr hD (A + L) using 1
    apply Finset.sum_congr rfl
    intro n hn
    exact norm_product_term_sq rho D (Finset.mem_Icc.mp hn).1
  calc
    _ ≤ ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 *
        ((2 * (H : ℝ) + 1) * (divisorSquareDirichletMass p * (D : ℝ) ^ (p - 2 * rho.1.re))) :=
      mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hs (by positivity))) (sq_nonneg _)
    _ = _ := by ring

/-- The exact growing short-shift radius used with the original squared divisor cutoff. -/
def pairedEtaMoebiusBilinearNearRadius (rho : NontrivialZetaZero) (u : ℕ) : ℕ :=
  ⌊(u : ℝ) ^ (rho.1.re - 1 / 2)⌋₊

/-- For a hypothetical right-half zero, the eliminated product-shift band grows without bound. -/
theorem pairedEtaMoebiusBilinearNearRadius_tendsto_atTop
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (pairedEtaMoebiusBilinearNearRadius rho) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (sub_pos.mpr hrho)).comp (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- Every original squared-cutoff window satisfies a negative-power bound for the diagonal and an unbounded number of neighbouring product shifts together. -/
theorem norm_pairedEtaCompletedMoebiusBilinearNearForm_twoThirds_le
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re)
    {u : ℕ} (hu : 1 ≤ u) (A L : ℕ) :
    ‖pairedEtaCompletedMoebiusBilinearNearForm rho A L (u ^ 2)
      (pairedEtaMoebiusBilinearNearRadius rho u)‖ ≤
        3 * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * divisorSquareDirichletMass (rho.1.re + 1 / 2) *
          (u : ℝ) ^ (1 / 2 - rho.1.re) := by
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hup : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one huR
  have hrad : (pairedEtaMoebiusBilinearNearRadius rho u : ℝ) ≤
      (u : ℝ) ^ (rho.1.re - 1 / 2) := Nat.floor_le (Real.rpow_nonneg hup.le _)
  have hrpow : 1 ≤ (u : ℝ) ^ (rho.1.re - 1 / 2) :=
    Real.one_le_rpow huR (sub_nonneg.mpr hrho.le)
  have hrow : 2 * (pairedEtaMoebiusBilinearNearRadius rho u : ℝ) + 1 ≤
      3 * (u : ℝ) ^ (rho.1.re - 1 / 2) := by linarith
  have he : ((u ^ 2 : ℕ) : ℝ) ^ (rho.1.re + 1 / 2 - 2 * rho.1.re) =
      (u : ℝ) ^ (1 - 2 * rho.1.re) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hup.le]
    congr 1
    norm_num
    ring
  have h := norm_pairedEtaCompletedMoebiusBilinearNearForm_le_power rho
    (by linarith : 1 < rho.1.re + 1 / 2) (by linarith : rho.1.re + 1 / 2 ≤ 2 * rho.1.re)
    (by nlinarith : 1 ≤ u ^ 2) A L (pairedEtaMoebiusBilinearNearRadius rho u)
  rw [he] at h
  have hmass := divisorSquareDirichletMass_nonneg (rho.1.re + 1 / 2)
  apply h.trans
  calc
    _ ≤ (3 * (u : ℝ) ^ (rho.1.re - 1 / 2)) * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 *
        divisorSquareDirichletMass (rho.1.re + 1 / 2) * (u : ℝ) ^ (1 - 2 * rho.1.re) := by
      gcongr
    _ = 3 * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * divisorSquareDirichletMass (rho.1.re + 1 / 2) *
        ((u : ℝ) ^ (rho.1.re - 1 / 2) * (u : ℝ) ^ (1 - 2 * rho.1.re)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hup]
      congr 2
      ring

/-- The exact complex short-shift contribution tends to zero uniformly over arbitrary physical-window sequences while its shift radius tends to infinity. -/
theorem pairedEtaCompletedMoebiusBilinearNearForm_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) (A L : ℕ → ℕ) :
    Tendsto (fun u : ℕ ↦ pairedEtaCompletedMoebiusBilinearNearForm rho (A u) (L u) (u ^ 2)
      (pairedEtaMoebiusBilinearNearRadius rho u)) atTop (𝓝 0) := by
  have hd : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (1 / 2 - rho.1.re)) atTop (𝓝 0) := by
    have hr := tendsto_rpow_neg_atTop (sub_pos.mpr hrho)
    convert hr.comp (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext u
    simp only [Function.comp_apply]
    congr 1
    ring
  have hb := hd.const_mul (3 * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 *
    divisorSquareDirichletMass (rho.1.re + 1 / 2))
  rw [mul_zero] at hb
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  exact squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _))
    ((eventually_ge_atTop 1).mono fun u hu ↦
      norm_pairedEtaCompletedMoebiusBilinearNearForm_twoThirds_le rho hrho hu (A u) (L u)) hb

/-- The entire source square survives in the signed long-shift form after removing the proved vanishing growing band on the original cubic windows. Bounding this remaining form is still the open arithmetic step. -/
theorem pairedEtaCompletedMoebiusBilinearFarForm_twoThirds_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun u : ℕ ↦ (pairedEtaCompletedMoebiusBilinearFarForm rho (u ^ 3) (u ^ 3) (u ^ 2)
      (pairedEtaMoebiusBilinearNearRadius rho u)).re) atTop
        (𝓝 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)) := by
  have hh := pairedEtaCompletedMoebiusLargeMeanSquare_twoThirds_tendsto_source rho hrho
  have hn := Complex.continuous_re.continuousAt.tendsto.comp
    (pairedEtaCompletedMoebiusBilinearNearForm_tendsto_zero rho hrho
      (fun u ↦ u ^ 3) (fun u ↦ u ^ 3))
  have he (u : ℕ) : (pairedEtaCompletedMoebiusBilinearFarForm rho (u ^ 3) (u ^ 3) (u ^ 2)
      (pairedEtaMoebiusBilinearNearRadius rho u)).re =
        pairedEtaCompletedMoebiusLargeMeanSquare rho (u ^ 3) (u ^ 3) (u ^ 2) -
          (pairedEtaCompletedMoebiusBilinearNearForm rho (u ^ 3) (u ^ 3) (u ^ 2)
            (pairedEtaMoebiusBilinearNearRadius rho u)).re := by
    have h := congrArg Complex.re (pairedEtaCompletedMoebiusLargeMeanSquare_eq_near_add_far rho
      (u ^ 3) (u ^ 3) (u ^ 2) (pairedEtaMoebiusBilinearNearRadius rho u))
    simp only [Complex.add_re, Complex.ofReal_re] at h
    linarith
  simpa only [Function.comp_apply, he, Complex.zero_re, sub_zero] using hh.sub hn

end

end RiemannGaussian

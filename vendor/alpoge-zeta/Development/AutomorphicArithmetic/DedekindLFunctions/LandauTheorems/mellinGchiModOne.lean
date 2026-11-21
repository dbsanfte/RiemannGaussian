import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.MellinRamp

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem mellin_Gchi_modOne_sum {μ : Measure ℝ} (T : ℕ → ℝ → ℂ) (E : ℝ → ℂ)
    (hT : ∀ n, Integrable (T n) μ) (hE : Integrable E μ)
    (hs : Summable fun n => ∫ a, ‖T n a‖ ∂μ) (hp : ∀ a, Summable fun n => T n a) :
    ∫ a, (E a + ∑' n, T n a) ∂μ = ∫ a, E a ∂μ + ∑' n, ∫ a, T n a ∂μ := by
  let F : ℕ → ℝ → ℂ := fun n => Nat.casesOn n E T
  have hF : ∀ n, Integrable (F n) μ := fun n => by
    cases n with
    | zero => exact hE
    | succ n => exact hT n
  have hFs : Summable fun n => ∫ a, ‖F n a‖ ∂μ := (summable_nat_add_iff 1).mp hs
  have h := hasSum_integral_of_summable_integral_norm hF hFs
  have h2 : ∀ a, ∑' n, F n a = E a + ∑' n, T n a := fun a =>
    ((summable_nat_add_iff (f := fun n => F n a) 1).mp (hp a)).tsum_eq_zero_add
  simp_rw [h2] at h
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  rfl

theorem mellin_Gchi_modOne_int (n : ℕ) (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have ha : (-s).re < -1 := by simp; linarith
  have hb : (-s - 1).re < -1 := by simp; linarith
  refine Integrable.mono' (integrableOn_Ioi_norm_cpow_of_lt ha zero_lt_one) ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ (integrableOn_Ioi_cpow_of_lt hb zero_lt_one).1
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
    have hy1 : (1 : ℝ) < y := hy
    have hy0 : (0 : ℝ) < y := by linarith
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have h1 : y / n ≤ y := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using hy0.le
      · exact div_le_self hy0.le (by exact_mod_cast hn)
    have h2 : max (y / n - 1) 0 ≤ y := max_le (by linarith) hy0.le
    rw [norm_mul, cpow_sub _ _ hyC, cpow_one, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (le_max_right _ _), Real.norm_of_nonneg hy0.le]
    calc _ ≤ y * (‖(y : ℂ) ^ (-s)‖ / y) := by gcongr
      _ = _ := by field_simp

theorem mellin_Gchi_modOne_term (n : ℕ) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) =
      LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n / (s * (s - 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [integral_const_mul, mellin_ramp n hn s hs, LSeries.term_of_ne_zero hn.ne', cpow_neg]
  ring

theorem mellin_Gchi_modOne_log_int (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) (Ioi 1) ∧
    Tendsto (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s + 1)) atTop (𝓝 0) := by
  have ha : (-s).re < -1 := by simp; linarith
  set e : ℝ := (s.re - 1) / 2 with he
  have he0 : 0 < e := by linarith
  have key : ∀ (c : ℂ) (y : ℝ), 1 < y →
      ‖((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ c‖ ≤ y ^ (e + c.re) / e := by
    intro c y hy
    have hy0 : (0 : ℝ) < y := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hy.le),
      Complex.norm_cpow_eq_rpow_re_of_pos hy0, Real.rpow_add hy0]
    calc _ ≤ y ^ e / e * y ^ c.re := by
          gcongr
          exact Real.log_le_rpow_div hy0.le he0
      _ = _ := by ring
  constructor
  · have hc : e + (-s).re < -1 := by simp; linarith
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hc zero_lt_one).div_const e) ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ (integrableOn_Ioi_cpow_of_lt ha zero_lt_one).1
      exact (Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => key _ y hy
  · have hc : 0 < -(e + (-s + 1).re) := by simp; linarith
    have h := (tendsto_rpow_neg_atTop hc).div_const e
    rw [neg_neg, zero_div] at h
    refine squeeze_zero_norm' ?_ h
    filter_upwards [eventually_gt_atTop 1] with y hy using key _ y hy

theorem mellin_Gchi_modOne_log (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s) = 1 / (s - 1) ^ 2 := by
  have ha : (-s).re < -1 := by simp; linarith
  have hs1 : -s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  obtain ⟨hi, ht⟩ := mellin_Gchi_modOne_log_int s hs
  have hd : ∀ y ∈ Ici (1 : ℝ), HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s + 1))
      ((-s + 1) * (((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) + (y : ℂ) ^ (-s)) y := by
    intro y hy
    have hy0 : y ≠ 0 := (zero_lt_one.trans_le hy).ne'
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
    refine ((Real.hasDerivAt_log hy0).ofReal_comp.mul
      (hasDerivAt_ofReal_cpow_const hy0 hs1)).congr_deriv ?_
    rw [add_sub_cancel_right, cpow_add _ _ hyC, cpow_one]
    push_cast
    field_simp
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    ((hi.const_mul _).add (integrableOn_Ioi_cpow_of_lt ha zero_lt_one)) ht
  rw [integral_add (hi.const_mul _) (integrableOn_Ioi_cpow_of_lt ha zero_lt_one),
    integral_const_mul, integral_Ioi_cpow_of_lt ha zero_lt_one] at h
  simp only [ofReal_one, one_cpow, Real.log_one, ofReal_zero, zero_mul, sub_zero] at h
  have e2 : (s - 1) ^ 2 = (-s + 1) ^ 2 := by ring
  rw [e2]
  field_simp at h ⊢
  linear_combination h

theorem mellin_Gchi_modOne (χ : DirichletCharacter ℂ 1) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1) =
      -(deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1 - (1 + Real.eulerMascheroniConstant) * s) /
        (s * (s - 1)) := by
  have h1 : χ = 1 := DirichletCharacter.level_one χ
  have h2 : ∀ n : ℕ, χ n = 1 := fun n => by
    rw [h1]; exact MulChar.one_apply (isUnit_of_subsingleton _)
  have ha : (-s).re < -1 := by simp; linarith
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  let T : ℕ → ℝ → ℂ := fun n y => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1))
  let E : ℝ → ℂ := fun y => (1 + Real.eulerMascheroniConstant) * (y : ℂ) ^ (-s) -
    ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)
  have hz : ∀ y : ℝ, ∀ n ∉ Finset.range (⌊y⌋₊ + 1), T n y = 0 := by
    intro y n hn
    have hn' : ⌊y⌋₊ + 1 ≤ n := by simpa using hn
    have hpos : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hlt : y < n := by
      have h1 := Nat.lt_floor_add_one y
      have h2 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
      push_cast at h2
      linarith
    have : max (y / n - 1) 0 = 0 := by
      apply max_eq_right
      have := (div_lt_one hpos).mpr hlt
      linarith
    simp [T, this]
  have hc : EqOn (fun y : ℝ => Gchi χ y * (y : ℂ) ^ (-s - 1))
      (fun y => E y + ∑' n, T n y) (Ioi 1) := by
    intro y hy
    have hy1 : (1 : ℝ) < y := hy
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hy1).ne'
    have h3 : (y : ℂ) ^ (-s) = y * (y : ℂ) ^ (-s - 1) := by
      rw [cpow_sub _ _ hyC, cpow_one]
      field_simp
    beta_reduce
    rw [tsum_eq_sum (hz y)]
    simp only [Gchi, if_pos h1, h2, ramp, T, E, h3, mul_one, ← mul_assoc,
      ← Finset.sum_mul]
    push_cast
    ring
  have hi := (mellin_Gchi_modOne_log_int s hs).1
  have hi2 := integrableOn_Ioi_cpow_of_lt ha zero_lt_one
  have hsum : Summable fun n => ∫ y in Ioi (1 : ℝ), ‖T n y‖ := by
    have hσ : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
    rw [← Complex.summable_ofReal]
    refine ((ArithmeticFunction.LSeriesSummable_vonMangoldt hσ).div_const
      ((s.re : ℂ) * (s.re - 1))).congr fun n => ?_
    rw [← mellin_Gchi_modOne_term n _ hσ, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := zero_lt_one.trans hy
    simp only [T]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.norm_of_nonneg (le_max_right _ _), Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have : (y : ℂ) ^ (-(s.re : ℂ) - 1) = ((y ^ (-s - 1).re : ℝ) : ℂ) := by
      rw [ofReal_cpow hy0.le]
      simp
    rw [this]
    simp
  rw [setIntegral_congr_fun measurableSet_Ioi hc,
    mellin_Gchi_modOne_sum T E (fun n => (mellin_Gchi_modOne_int n s hs).const_mul _)
      ((hi2.const_mul _).sub hi) hsum (fun y => summable_of_ne_finset_zero (hz y))]
  simp only [T, E, mellin_Gchi_modOne_term _ s hs]
  rw [tsum_div_const, integral_sub (hi2.const_mul _) hi, integral_const_mul,
    integral_Ioi_cpow_of_lt ha zero_lt_one, mellin_Gchi_modOne_log s hs]
  have h4 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [LSeries] at h4
  rw [h4, neg_div (riemannZeta s)]
  have e2 : -s + 1 = -(s - 1) := by ring
  rw [e2]
  generalize deriv riemannZeta s / riemannZeta s = D
  simp only [ofReal_one, one_cpow]
  field_simp
  ring

end Deduction

end

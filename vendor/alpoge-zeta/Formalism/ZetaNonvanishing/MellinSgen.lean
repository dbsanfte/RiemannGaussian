import Formalism.DefsOC
import Formalism.ZetaNonvanishing.MellinSAux

open Complex MeasureTheory Set Filter Topology ArithmeticFunction

noncomputable section

namespace Formalism

section
variable (a : ℕ → ℝ)

lemma Sa_measurable : Measurable (Sa a) := by
  have hk : ∀ k : ℕ, Measurable fun x : ℝ => ∑ n ∈ Finset.Icc 1 k, a n * (x / n - 1) :=
    fun k => Finset.measurable_sum _ fun n _ => by fun_prop
  unfold Sa
  first
    | (have hg : Measurable (fun p : ℝ × ℕ => ∑ n ∈ Finset.Icc 1 p.2, a n * (p.1 / n - 1)) := by
        first
          | exact measurable_from_prod_countable_right hk
          | exact measurable_from_prod_countable_left hk
          | exact measurable_from_prod_countable hk
       exact hg.comp (measurable_id.prodMk Nat.measurable_floor))
    | (have hg : Measurable (fun p : ℕ × ℝ => ∑ n ∈ Finset.Icc 1 p.1, a n * (p.2 / n - 1)) := by
        first
          | exact measurable_from_prod_countable_left hk
          | exact measurable_from_prod_countable_right hk
       exact hg.comp (Nat.measurable_floor.prodMk measurable_id))

lemma a_mxS_eq_zero (ha0 : a 0 = 0) (x : ℝ) (n : ℕ) (hn : n ∉ Finset.Icc 1 ⌊x⌋₊) :
    a n * mxS n x = 0 := by
  unfold mxS
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  rcases hn with hn | hn
  · have h0 : n = 0 := by omega
    subst h0
    simp [ha0]
  · have hx : x < n := Nat.lt_of_floor_lt hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hle : x / n - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hn0]
      exact hx.le
    rw [max_eq_right hle, mul_zero]

lemma Sa_eq_tsum (ha0 : a 0 = 0) (x : ℝ) : Sa a x = ∑' n, a n * mxS n x := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => a_mxS_eq_zero a ha0 x n hn)]
  unfold Sa
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hx : (n : ℝ) ≤ x := by
    have hx0 : 0 ≤ x := by
      by_contra hneg
      push_neg at hneg
      rw [Nat.floor_eq_zero.mpr (by linarith)] at hn
      omega
    exact (Nat.le_floor_iff hx0).mp hn.2
  have hnn : 0 ≤ x / n - 1 := by
    rw [sub_nonneg, le_div_iff₀ hn0]
    linarith
  unfold mxS
  rw [max_eq_left hnn]

lemma summable_a_mxS (ha0 : a 0 = 0) (x : ℝ) : Summable (fun n => a n * mxS n x) :=
  summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => a_mxS_eq_zero a ha0 x n hn)

lemma abs_Sa_le (ha0 : a 0 = 0) (x : ℝ) : |Sa a x| ≤ ∑' n, |a n| * mxS n x := by
  have hm : ∀ n, 0 ≤ mxS n x := fun n => by
    unfold mxS
    exact le_max_right _ _
  rw [Sa_eq_tsum a ha0 x, tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => a_mxS_eq_zero a ha0 x n hn),
    tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => by
      have h := a_mxS_eq_zero a ha0 x n hn
      rcases mul_eq_zero.mp h with h | h <;> simp [h])]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
  rw [abs_mul, abs_of_nonneg (hm n)]

lemma summable_abs_a (K : ℝ) (hK : ∀ n : ℕ, |a n| ≤ K * vonMangoldt n) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => |a n| * (n : ℝ) ^ (-σ)) := by
  have hs : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun n => ?_) (hs.norm.mul_left |K|)
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
  · have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [LSeries.norm_term_eq, if_neg hn.ne']
    simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg hΛ]
    rw [div_eq_mul_inv, ← Real.rpow_neg hnpos.le]
    have hK' : |a n| ≤ |K| * ArithmeticFunction.vonMangoldt n :=
      (hK n).trans (mul_le_mul_of_nonneg_right (le_abs_self K) hΛ)
    calc |a n| * (n : ℝ) ^ (-σ) ≤ |K| * ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hK' (Real.rpow_nonneg hnpos.le _)
      _ = |K| * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) := by ring

end

theorem mellinSgen : MellinSgen := by
  intro a K hK
  have ha0 : a 0 = 0 := by
    have h := hK 0
    rw [ArithmeticFunction.map_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  refine ⟨Sa_measurable a, fun σ hσ => ?_, fun s hs => ?_⟩
  · have key := integrable_tsum_of_nonneg (μ := volume.restrict (Ioi (1 : ℝ)))
      (φ := fun n x => |a n| * (mxS n x * x ^ (-σ - 1))) (fun n => ?_) (fun n => ?_)
      (fun x => ?_) ?_
    · have hmeas : Measurable (fun x : ℝ => |Sa a x| * x ^ (-σ - 1)) := by
        have := Sa_measurable a
        fun_prop
      refine key.mono' hmeas.aestronglyMeasurable ?_
      refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
      have hxp : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hx0.le _
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hxp)]
      calc |Sa a x| * x ^ (-σ - 1) ≤ (∑' n, |a n| * mxS n x) * x ^ (-σ - 1) :=
            mul_le_mul_of_nonneg_right (abs_Sa_le a ha0 x) hxp
        _ = ∑' n, |a n| * (mxS n x * x ^ (-σ - 1)) := by
            rw [← tsum_mul_right]; congr 1; funext n; ring
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [ha0]
      · exact ((mxS_mellin_real hn hσ).1).const_mul _
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      exact mul_nonneg (abs_nonneg _) (mul_nonneg (mxS_nonneg n x)
        (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hx)) _))
    · have ha0' : |a 0| = 0 := by simp [ha0]
      simpa only [mul_assoc] using
        (summable_a_mxS (fun n => |a n|) ha0' x).mul_right (x ^ (-σ - 1))
    · have : (fun n => ∫ x in Ioi (1 : ℝ), |a n| * (mxS n x * x ^ (-σ - 1))) =
          fun n : ℕ => |a n| * (n : ℝ) ^ (-σ) / (σ * (σ - 1)) := by
        funext n
        rw [integral_const_mul]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [ha0]
        · rw [(mxS_mellin_real hn hσ).2]; ring
      rw [this]; exact (summable_abs_a a K hK hσ).div_const _
  · set F : ℕ → ℝ → ℂ := fun n x => (a n : ℂ) * ((mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) with hFdef
    have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi (1 : ℝ))) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [F, ha0]
      · exact ((mxS_mellin hn hs).1).const_mul _
    have hnorm : ∀ n, ∫ x in Ioi (1 : ℝ), ‖F n x‖ =
        |a n| * (n : ℝ) ^ (-s.re) / (s.re * (s.re - 1)) := by
      intro n
      rw [setIntegral_congr_fun measurableSet_Ioi
        (g := fun x => |a n| * (mxS n x * x ^ (-s.re - 1))) (fun x hx => ?_)]
      · rw [integral_const_mul]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [ha0]
        · rw [(mxS_mellin_real hn hs).2]; ring
      · have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
        simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mxS_nonneg n x), norm_cpow_eq_rpow_re_of_pos hx0]
        congr 3
    have hsum : Summable (fun n => ∫ x in Ioi (1 : ℝ), ‖F n x‖) := by
      simp_rw [hnorm]; exact (summable_abs_a a K hK hs).div_const _
    have hpt : ∀ x ∈ Ioi (1 : ℝ), (Sa a x : ℂ) * (x : ℂ) ^ (-s - 1) = ∑' n, F n x := by
      intro x hx
      rw [Sa_eq_tsum a ha0, ofReal_tsum, ← tsum_mul_right]
      congr 1; funext n; simp only [F]; push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      ← integral_tsum_of_summable_integral_norm hint hsum, LSeries, ← tsum_div_const]
    congr 1; funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F, ha0]
    · simp only [F]
      rw [integral_const_mul, (mxS_mellin hn hs).2, LSeries.term_of_ne_zero (by omega), cpow_neg]
      ring

end Formalism

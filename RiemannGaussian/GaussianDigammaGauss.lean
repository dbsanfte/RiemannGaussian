import RiemannGaussian.GaussianDigammaTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Gauss's digamma integral and the unconditional Gaussian--Suzuki bridge

This file proves the quarter-line instance of Gauss's integral representation
that remained as the final analytic hypothesis in `GaussianDigammaTransform`.
The proof is built from Mathlib's Gamma integral and Euler approximation:

* differentiate the compactly supported Euler approximants via the Mellin
  transform and justify their limit by dominated convergence;
* compute their finite logarithmic derivatives and obtain Euler's convergent
  series for `Complex.digamma` on the right half-plane;
* take the real vertical difference, express every nonnegative series term as
  a damped-cosine Laplace integral, and exchange sum and integral;
* sum the geometric kernel and specialize `a = 1/4`, `b = r/2`.

Consequently `QuarterLineDigammaGaussDifferenceFormula` and
`GaussianDigammaScrewTransform` are both discharged without axioms.
-/

noncomputable section

open Filter Set Real Asymptotics MeasureTheory
open scoped Topology

namespace Complex

theorem integrableOn_gammaIntegral_log_kernel {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        (Real.log t * Real.exp (-t))) (Ioi 0) := by
  have hconv :=
    (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ)
      (f := fun x : ℝ => (Real.exp (-x) : ℂ))
      (a := s.re + 1) (b := 0)
      (by
        refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
        exact continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg))
      (by
        rw [← isBigO_norm_left]
        simp_rw [norm_real, isBigO_norm_left]
        simpa only [neg_one_mul] using
          (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-(s.re + 1))).isBigO)
      (lt_add_one _)
      (by
        simp_rw [neg_zero, rpow_zero]
        refine isBigO_const_of_tendsto
          (?_ : Tendsto _ _ (𝓝 (1 : ℂ))) one_ne_zero
        rw [(by simp : (1 : ℂ) = Real.exp (-0))]
        exact (continuous_ofReal.comp
          (Real.continuous_exp.comp continuous_neg)).continuousWithinAt)
      hs).1
  rw [MellinConvergent] at hconv
  simpa [smul_eq_mul, real_smul] using hconv

end Complex

namespace Complex

/-- Compactly supported Euler weight for the finite Gamma approximation. -/
def gammaApproxWeight (n : ℕ) (x : ℝ) : ℂ :=
  indicator (Ioc 0 (n : ℝ))
    (fun y : ℝ => (((1 - y / n) ^ n : ℝ) : ℂ)) x

theorem mellin_gammaApproxWeight (n : ℕ) (z : ℂ) :
    mellin (gammaApproxWeight n) z =
      ∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (z - 1) := by
  unfold mellin gammaApproxWeight
  calc
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (z - 1) •
          indicator (Ioc 0 (n : ℝ))
            (fun y : ℝ => (((1 - y / n) ^ n : ℝ) : ℂ)) x) =
      ∫ x : ℝ in Ioi 0,
        indicator (Ioc 0 (n : ℝ))
          (fun y : ℝ =>
            (((1 - y / n) ^ n : ℝ) : ℂ) *
              (y : ℂ) ^ (z - 1)) x := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ Ioc (0 : ℝ) n
        · rw [indicator_of_mem hx, indicator_of_mem hx]
          simp only [smul_eq_mul]
          ring
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]
    _ = ∫ x : ℝ in Ioc 0 (n : ℝ),
          (((1 - x / n) ^ n : ℝ) : ℂ) *
            (x : ℂ) ^ (z - 1) := by
        rw [MeasureTheory.integral_indicator measurableSet_Ioc,
          Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
    _ = _ := by
      rw [intervalIntegral.integral_of_le (by positivity : 0 ≤ (n : ℝ))]

theorem mellin_log_gammaApproxWeight (n : ℕ) (z : ℂ) :
    mellin (fun x : ℝ => Real.log x • gammaApproxWeight n x) z =
      ∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
          ((x : ℂ) ^ (z - 1) * Real.log x) := by
  unfold mellin gammaApproxWeight
  calc
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (z - 1) •
          (Real.log x •
            indicator (Ioc 0 (n : ℝ))
              (fun y : ℝ => (((1 - y / n) ^ n : ℝ) : ℂ)) x)) =
      ∫ x : ℝ in Ioi 0,
        indicator (Ioc 0 (n : ℝ))
          (fun y : ℝ =>
            (((1 - y / n) ^ n : ℝ) : ℂ) *
              ((y : ℂ) ^ (z - 1) * Real.log y)) x := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ Ioc (0 : ℝ) n
        · rw [indicator_of_mem hx, indicator_of_mem hx]
          simp only [smul_eq_mul, real_smul]
          ring
        · rw [indicator_of_notMem hx, indicator_of_notMem hx,
            smul_zero, smul_zero]
    _ = ∫ x : ℝ in Ioc 0 (n : ℝ),
          (((1 - x / n) ^ n : ℝ) : ℂ) *
            ((x : ℂ) ^ (z - 1) * Real.log x) := by
        rw [MeasureTheory.integral_indicator measurableSet_Ioc,
          Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
    _ = _ := by
      rw [intervalIntegral.integral_of_le (by positivity : 0 ≤ (n : ℝ))]

theorem hasDerivAt_mellin_gammaApproxWeight
    {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    HasDerivAt (mellin (gammaApproxWeight n))
      (mellin (fun x : ℝ =>
        Real.log x • gammaApproxWeight n x) s) s := by
  have hw_int : IntegrableOn (gammaApproxWeight n) (Ioi 0) := by
    unfold gammaApproxWeight
    change IntegrableOn
      (indicator (Ioc 0 (n : ℝ))
        (fun y : ℝ => (((1 - y / n) ^ n : ℝ) : ℂ))) (Ioi 0)
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioc,
      IntegrableOn,
      Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self,
      ← IntegrableOn,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le
        (by positivity : (0 : ℝ) ≤ n)]
    exact Continuous.intervalIntegrable (μ := volume) (by fun_prop : Continuous
      (fun y : ℝ => (((1 - y / n) ^ n : ℝ) : ℂ))) 0 (n : ℝ)
  have hw_top : gammaApproxWeight n =O[atTop]
      (fun x : ℝ => x ^ (-(s.re + 1))) := by
    have hzero : gammaApproxWeight n =ᶠ[atTop]
        (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [eventually_gt_atTop (n : ℝ)] with x hx
      unfold gammaApproxWeight
      rw [indicator_of_notMem (notMem_Ioc_of_gt hx)]
    exact (isBigO_zero (fun x : ℝ => x ^ (-(s.re + 1))) atTop).congr'
      hzero.symm EventuallyEq.rfl
  have hw_tend : Tendsto (gammaApproxWeight n)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
    let p : ℝ → ℂ := fun x : ℝ => (((1 - x / n) ^ n : ℝ) : ℂ)
    have hp : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
      have hp' : Tendsto p (𝓝 (0 : ℝ)) (𝓝 (1 : ℂ)) := by
        have hc : ContinuousAt p 0 := by fun_prop
        change Tendsto p (𝓝 (0 : ℝ)) (𝓝 (p 0)) at hc
        have hp0 : p 0 = 1 := by simp [p]
        rw [hp0] at hc
        exact hc
      exact hp'.mono_left nhdsWithin_le_nhds
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have heq : gammaApproxWeight n =ᶠ[𝓝[>] (0 : ℝ)] p := by
      filter_upwards [eventually_mem_nhdsWithin,
        (eventually_lt_nhds hnpos).filter_mono nhdsWithin_le_nhds] with x hx hxn
      have hxmem : x ∈ Ioc (0 : ℝ) (n : ℝ) := ⟨hx, hxn.le⟩
      unfold gammaApproxWeight p
      rw [indicator_of_mem hxmem]
    exact hp.congr' heq.symm
  have hw_bot : gammaApproxWeight n =O[𝓝[>] (0 : ℝ)]
      (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    simp_rw [neg_zero, rpow_zero]
    exact isBigO_const_of_tendsto hw_tend one_ne_zero
  exact (mellin_hasDerivAt_of_isBigO_rpow
    hw_int.locallyIntegrableOn hw_top (lt_add_one _)
    hw_bot hs).2

theorem hasDerivAt_approx_Gamma_integral
    {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    HasDerivAt
      (fun z : ℂ => ∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
          (x : ℂ) ^ (z - 1))
      (∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
          ((x : ℂ) ^ (s - 1) * Real.log x)) s := by
  have h := hasDerivAt_mellin_gammaApproxWeight hs hn
  rw [mellin_log_gammaApproxWeight] at h
  exact h.congr_of_eventuallyEq
    (Eventually.of_forall fun z => (mellin_gammaApproxWeight n z).symm)

end Complex

namespace Complex

lemma add_natCast_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    s + j ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have hjre : ((j : ℂ).re) = (j : ℝ) := by norm_num
  rw [add_re, hjre, zero_re] at hre
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  linarith

theorem GammaSeq_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re)
    {n : ℕ} (hn : n ≠ 0) : GammaSeq s n ≠ 0 := by
  unfold GammaSeq
  apply div_ne_zero
  · apply mul_ne_zero
    · exact cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn))
    · exact_mod_cast Nat.factorial_ne_zero n
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact add_natCast_ne_zero_of_re_pos hs j

theorem logDeriv_GammaSeq {s : ℂ} (hs : 0 < s.re)
    {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun z : ℂ => GammaSeq z n) s =
      Complex.log (n : ℂ) -
        ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹ := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hfacC : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hfactor : ∀ j ∈ Finset.range (n + 1), s + (j : ℂ) ≠ 0 := by
    intro j hj
    exact add_natCast_ne_zero_of_re_pos hs j
  unfold GammaSeq
  rw [logDeriv_div s]
  · rw [logDeriv_mul s]
    · rw [logDeriv_prod hfactor]
      · simp only [logDeriv_apply]
        rw [((hasStrictDerivAt_const_cpow (x := (n : ℂ)) (y := s)
          (Or.inl hnC)).hasDerivAt.deriv)]
        simp only [deriv_const, zero_div, deriv_add_const, deriv_id'']
        rw [mul_div_cancel_left₀ _ (cpow_ne_zero_iff.mpr (Or.inl hnC))]
        simp only [add_zero, inv_eq_one_div]
      · intro j hj
        fun_prop
    · exact cpow_ne_zero_iff.mpr (Or.inl hnC)
    · exact hfacC
    · exact (hasStrictDerivAt_const_cpow (x := (n : ℂ)) (y := s)
        (Or.inl hnC)).hasDerivAt.differentiableAt
    · fun_prop
  · exact mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hnC)) hfacC
  · exact Finset.prod_ne_zero_iff.mpr hfactor
  · exact ((hasStrictDerivAt_const_cpow (x := (n : ℂ)) (y := s)
      (Or.inl hnC)).hasDerivAt.differentiableAt.mul
        (by fun_prop : DifferentiableAt ℂ
          (fun _ : ℂ => ((Nat.factorial n : ℕ) : ℂ)) s))
  · fun_prop

end Complex

namespace Complex

theorem hasDerivAt_GammaSeq_log_integral
    {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    HasDerivAt (fun z : ℂ => GammaSeq z n)
      (∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
          ((x : ℂ) ^ (s - 1) * Real.log x)) s := by
  have h := hasDerivAt_approx_Gamma_integral hs hn
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  apply h.congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hs] with z hz
  exact GammaSeq_eq_approx_Gamma_integral hz hn

theorem approx_Gamma_log_integral_eq_GammaSeq_mul
    {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    (∫ x : ℝ in 0..n,
      (((1 - x / n) ^ n : ℝ) : ℂ) *
        ((x : ℂ) ^ (s - 1) * Real.log x)) =
      GammaSeq s n *
        (Complex.log (n : ℂ) -
          ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹) := by
  let F : ℂ → ℂ := fun z => GammaSeq z n
  have hderiv := hasDerivAt_GammaSeq_log_integral hs hn
  have hne : F s ≠ 0 := GammaSeq_ne_zero_of_re_pos hs hn
  have hlog := logDeriv_GammaSeq hs hn
  change logDeriv F s = _ at hlog
  calc
    (∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
          ((x : ℂ) ^ (s - 1) * Real.log x)) = deriv F s := hderiv.deriv.symm
    _ = F s * logDeriv F s := by
      rw [logDeriv_apply]
      field_simp
    _ = GammaSeq s n *
        (Complex.log (n : ℂ) -
          ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹) := by
      rw [hlog]

theorem hasDerivAt_Gamma_integral_log_kernel
    {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt Gamma
      (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) *
          (Real.log x * Real.exp (-x))) s := by
  have h := hasDerivAt_GammaIntegral hs
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  exact h.congr_of_eventuallyEq (by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact Gamma_eq_integral hz)

end Complex

namespace Complex

theorem approx_Gamma_integral_log_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ => ∫ x : ℝ in 0..n,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
          ((x : ℂ) ^ (s - 1) * Real.log x))
      atTop
      (𝓝 <| ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) *
          (Real.log x * Real.exp (-x))) := by
  let f : ℕ → ℝ → ℂ := fun n =>
    indicator (Ioc 0 (n : ℝ)) fun x : ℝ =>
      (((1 - x / n) ^ n : ℝ) : ℂ) *
        ((x : ℂ) ^ (s - 1) * Real.log x)
  let g : ℝ → ℝ := fun x =>
    ‖(x : ℂ) ^ (s - 1) *
      (Real.log x * Real.exp (-x))‖
  have f_meas : ∀ n : ℕ,
      AEStronglyMeasurable (f n) (volume.restrict (Ioi 0)) := by
    intro n
    apply Measurable.aestronglyMeasurable
    unfold f
    apply Measurable.indicator
    · fun_prop
    · exact measurableSet_Ioc
  have g_ible : Integrable g (volume.restrict (Ioi 0)) := by
    exact (integrableOn_gammaIntegral_log_kernel hs).norm
  have f_tends : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) →
      Tendsto (fun n : ℕ => f n x) atTop
        (𝓝 <| (x : ℂ) ^ (s - 1) *
          (Real.log x * Real.exp (-x))) := by
    intro x hx
    apply Tendsto.congr'
    · change ∀ᶠ n : ℕ in atTop,
        (((1 - x / n) ^ n : ℝ) : ℂ) *
              ((x : ℂ) ^ (s - 1) * Real.log x) = f n x
      filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
      rw [Nat.ceil_le] at hn
      dsimp only [f]
      rw [indicator_of_mem]
      exact ⟨hx, hn⟩
    · have hreal : Tendsto (fun n : ℕ => (1 - x / n) ^ n)
          atTop (𝓝 (Real.exp (-x))) := by
        convert Real.tendsto_one_add_div_pow_exp (-x) using 1
        ext n
        rw [neg_div, ← sub_eq_add_neg]
      have hcomplex : Tendsto
          (fun n : ℕ => (((1 - x / n) ^ n : ℝ) : ℂ))
          atTop (𝓝 (Real.exp (-x) : ℂ)) :=
        (continuous_ofReal.tendsto _).comp hreal
      convert hcomplex.mul_const
        ((x : ℂ) ^ (s - 1) * Real.log x) using 1
      congr 1
      ring
  have f_bound : ∀ n : ℕ,
      ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0), ‖f n x‖ ≤ g x := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    simp only [mem_Ioi, f] at hx ⊢
    rcases lt_or_ge (n : ℝ) x with hxn | hxn
    · rw [indicator_of_notMem (notMem_Ioc_of_gt hxn), norm_zero]
      exact norm_nonneg _
    · rw [indicator_of_mem (mem_Ioc.mpr ⟨mem_Ioi.mp hx, hxn⟩)]
      unfold g
      have hbase : 0 ≤ 1 - x / (n : ℝ) :=
        sub_nonneg.mpr (div_le_one_of_le₀ hxn (by positivity))
      have hcoeff : 0 ≤ (1 - x / (n : ℝ)) ^ n := pow_nonneg hbase _
      have hfactor : 0 ≤ ‖(x : ℂ) ^ (s - 1)‖ * |Real.log x| :=
        mul_nonneg (norm_nonneg _) (abs_nonneg _)
      have hpow := one_sub_div_pow_le_exp_neg hxn
      calc
        ‖(((1 - x / n) ^ n : ℝ) : ℂ) *
            ((x : ℂ) ^ (s - 1) * Real.log x)‖ =
            (1 - x / n) ^ n *
              (‖(x : ℂ) ^ (s - 1)‖ * |Real.log x|) := by
          rw [norm_mul, Complex.norm_of_nonneg hcoeff, norm_mul]
          simp only [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ Real.exp (-x) *
              (‖(x : ℂ) ^ (s - 1)‖ * |Real.log x|) :=
          mul_le_mul_of_nonneg_right hpow hfactor
        _ = ‖(x : ℂ) ^ (s - 1) *
              (Real.log x * Real.exp (-x))‖ := by
          rw [norm_mul, norm_mul]
          simp only [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)]
          ring
  convert!
    tendsto_integral_of_dominated_convergence g f_meas g_ible f_bound
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ f_tends)) using 1
  ext n
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le (by positivity : 0 ≤ (n : ℝ)),
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]

end Complex

namespace Complex

theorem digamma_tendsto_euler {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ => Complex.log (n : ℂ) -
        ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹)
      atTop (𝓝 (digamma s)) := by
  let I : ℕ → ℂ := fun n => ∫ x : ℝ in 0..n,
    (((1 - x / n) ^ n : ℝ) : ℂ) *
      ((x : ℂ) ^ (s - 1) * Real.log x)
  have hI : Tendsto I atTop (𝓝 (deriv Gamma s)) := by
    have hlim := approx_Gamma_integral_log_tendsto hs
    have hderiv := hasDerivAt_Gamma_integral_log_kernel hs
    change Tendsto I atTop
      (𝓝 <| ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) *
          (Real.log x * Real.exp (-x))) at hlim
    rw [← hderiv.deriv] at hlim
    exact hlim
  have hquot := hI.div (GammaSeq_tendsto_Gamma s)
    (Gamma_ne_zero_of_re_pos hs)
  have htarget : deriv Gamma s / Gamma s = digamma s := by
    rw [digamma_def, logDeriv_apply]
  rw [htarget] at hquot
  apply hquot.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hne := GammaSeq_ne_zero_of_re_pos hs hn
  have hprod := approx_Gamma_log_integral_eq_GammaSeq_mul hs hn
  change I n / GammaSeq s n =
    Complex.log (n : ℂ) -
      ∑ j ∈ Finset.range (n + 1), (s + j)⁻¹
  dsimp only [I]
  rw [hprod]
  field_simp

/-- The nonnegative real term in the Euler series for a vertical digamma
difference. -/
def digammaRealDifferenceTerm (a b : ℝ) (j : ℕ) : ℝ :=
  1 / (a + j) - (a + j) / ((a + j) ^ 2 + b ^ 2)

lemma re_inv_ofReal {x : ℝ} (_hx : x ≠ 0) :
    (((x : ℂ)⁻¹).re) = 1 / x := by
  rw [Complex.inv_re, Complex.normSq_apply]
  norm_num

lemma re_inv_add_mul_I (x y : ℝ) :
    ((((x : ℂ) + (y : ℂ) * I)⁻¹).re) =
      x / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_add_mul_I]
  simp

lemma digammaRealDifferenceTerm_nonneg
    {a : ℝ} (ha : 0 < a) (b : ℝ) (j : ℕ) :
    0 ≤ digammaRealDifferenceTerm a b j := by
  have hx : 0 < a + (j : ℝ) := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)
  have hsum : 0 < (a + (j : ℝ)) ^ 2 + b ^ 2 := by positivity
  unfold digammaRealDifferenceTerm
  rw [show 1 / (a + (j : ℝ)) -
      (a + j) / ((a + j) ^ 2 + b ^ 2) =
      b ^ 2 / ((a + j) * ((a + j) ^ 2 + b ^ 2)) by
    field_simp [hx.ne', hsum.ne']
    ring]
  positivity

/-- A complex exponential whose real part is a damped cosine. -/
def dampedComplexOscillation (x b t : ℝ) : ℂ :=
  Complex.exp (((-x : ℝ) : ℂ) * t +
    Complex.I * (b * t))

lemma dampedComplexOscillation_re (x b t : ℝ) :
    (dampedComplexOscillation x b t).re =
      Real.exp (-x * t) * Real.cos (b * t) := by
  unfold dampedComplexOscillation
  rw [Complex.exp_add]
  have hreal : ((-x : ℝ) : ℂ) * (t : ℂ) =
      ((-x * t : ℝ) : ℂ) := by push_cast; rfl
  have himag : (b : ℂ) * (t : ℂ) = ((b * t : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hreal, himag, ← Complex.ofReal_exp]
  rw [mul_comm Complex.I]
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    add_zero, sub_zero, mul_one]

theorem integrableOn_exp_neg_mul_cos
    {x : ℝ} (hx : 0 < x) (b : ℝ) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-x * t) * Real.cos (b * t)) (Ioi 0) := by
  let c : ℂ := (-x : ℂ) + (b : ℂ) * I
  have hc : c.re < 0 := by simp [c, hx]
  have hcomplex : IntegrableOn
      (fun t : ℝ => Complex.exp (c * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hc 0
  have hre := hcomplex.re
  apply hre.congr
  filter_upwards with t
  have heq : Complex.exp (c * (t : ℂ)) =
      dampedComplexOscillation x b t := by
    unfold c dampedComplexOscillation
    congr 1
    push_cast
    ring
  rw [heq]
  change (dampedComplexOscillation x b t).re = _
  exact dampedComplexOscillation_re x b t

theorem integral_exp_neg_mul_cos
    {x : ℝ} (hx : 0 < x) (b : ℝ) :
    (∫ t : ℝ in Ioi 0,
      Real.exp (-x * t) * Real.cos (b * t)) =
      x / (x ^ 2 + b ^ 2) := by
  let c : ℂ := (-x : ℂ) + (b : ℂ) * I
  have hc : c.re < 0 := by simp [c, hx]
  have hcomplex : IntegrableOn
      (fun t : ℝ => Complex.exp (c * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hc 0
  have hre := integral_re hcomplex
  rw [integral_exp_mul_complex_Ioi hc 0] at hre
  change
    (∫ t : ℝ in Ioi 0, (Complex.exp (c * t)).re) =
      (-Complex.exp (c * (0 : ℝ)) / c).re at hre
  have hleft :
      (∫ t : ℝ in Ioi 0, (Complex.exp (c * t)).re) =
        ∫ t : ℝ in Ioi 0,
          Real.exp (-x * t) * Real.cos (b * t) := by
    apply integral_congr_ae
    filter_upwards with t
    have heq : Complex.exp (c * (t : ℂ)) =
        dampedComplexOscillation x b t := by
      unfold c dampedComplexOscillation
      congr 1
      push_cast
      ring
    rw [heq]
    change (dampedComplexOscillation x b t).re = _
    exact dampedComplexOscillation_re x b t
  rw [hleft] at hre
  have hright : (-Complex.exp (c * (0 : ℝ)) / c).re =
      x / (x ^ 2 + b ^ 2) := by
    norm_num only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [neg_div, one_div,
      Complex.neg_re, Complex.inv_re]
    unfold c
    have hcform : -(x : ℂ) + (b : ℂ) * I =
        ((-x : ℝ) : ℂ) + (b : ℂ) * I := by
      push_cast
      rfl
    rw [hcform]
    rw [Complex.normSq_add_mul_I]
    simp
    ring
  rw [hright] at hre
  exact hre

theorem integral_exp_neg_mul_one_sub_cos
    {x : ℝ} (hx : 0 < x) (b : ℝ) :
    (∫ t : ℝ in Ioi 0,
      Real.exp (-x * t) * (1 - Real.cos (b * t))) =
      1 / x - x / (x ^ 2 + b ^ 2) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-x * t)) (Ioi 0) := by
    simpa only [neg_mul] using
      integrableOn_exp_mul_Ioi (a := -x) (neg_lt_zero.mpr hx) 0
  have hcos := integrableOn_exp_neg_mul_cos hx b
  rw [show (fun t : ℝ =>
      Real.exp (-x * t) * (1 - Real.cos (b * t))) =
      fun t : ℝ => Real.exp (-x * t) -
        Real.exp (-x * t) * Real.cos (b * t) by
    funext t
    ring]
  rw [integral_sub hexp hcos,
    integral_exp_neg_mul_cos hx b]
  have hexpValue := integral_exp_mul_Ioi (a := -x)
    (neg_lt_zero.mpr hx) 0
  simp only [mul_zero, Real.exp_zero, neg_div] at hexpValue
  rw [hexpValue]
  field_simp [hx.ne']

theorem integrableOn_exp_neg_mul_one_sub_cos
    {x : ℝ} (hx : 0 < x) (b : ℝ) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-x * t) * (1 - Real.cos (b * t))) (Ioi 0) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-x * t)) (Ioi 0) := by
    simpa only [neg_mul] using
      integrableOn_exp_mul_Ioi (a := -x) (neg_lt_zero.mpr hx) 0
  have hcos := integrableOn_exp_neg_mul_cos hx b
  apply (hexp.sub hcos).congr
  filter_upwards with t
  change Real.exp (-x * t) -
      Real.exp (-x * t) * Real.cos (b * t) =
    Real.exp (-x * t) * (1 - Real.cos (b * t))
  ring

theorem digammaRealDifferenceTerm_eq_integral
    {a : ℝ} (ha : 0 < a) (b : ℝ) (j : ℕ) :
    digammaRealDifferenceTerm a b j =
      ∫ t : ℝ in Ioi 0,
        Real.exp (-(a + j) * t) * (1 - Real.cos (b * t)) := by
  have hx : 0 < a + (j : ℝ) :=
    add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)
  rw [integral_exp_neg_mul_one_sub_cos hx b]
  rfl

theorem hasSum_digammaRealDifferenceTerm
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    HasSum (digammaRealDifferenceTerm a b)
      ((digamma ((a : ℂ) + (b : ℂ) * I)).re -
        (digamma (a : ℂ)).re) := by
  let z : ℂ := (a : ℂ) + (b : ℂ) * I
  let w : ℂ := (a : ℂ)
  have hz : 0 < z.re := by simp [z, ha]
  have hw : 0 < w.re := by simpa [w] using ha
  have hdiff := (digamma_tendsto_euler hz).sub
    (digamma_tendsto_euler hw)
  have hre := (Complex.continuous_re.tendsto
    (digamma z - digamma w)).comp hdiff
  have hshift : Tendsto
      (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
        digammaRealDifferenceTerm a b j)
      atTop
      (𝓝 ((digamma z).re - (digamma w).re)) := by
    apply hre.congr'
    filter_upwards with n
    simp only [Function.comp_apply, sub_re]
    rw [sub_sub_sub_cancel_left]
    rw [Complex.re_sum, Complex.re_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hx : 0 < a + (j : ℝ) :=
      add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)
    dsimp only [z, w]
    unfold digammaRealDifferenceTerm
    have hwj : (a : ℂ) + (j : ℂ) = ((a + j : ℝ) : ℂ) := by
      push_cast
      rfl
    have hzj : ((a : ℂ) + (b : ℂ) * I) + (j : ℂ) =
        ((a + j : ℝ) : ℂ) + (b : ℂ) * I := by
      push_cast
      ring
    rw [hwj, hzj, re_inv_ofReal hx.ne',
      re_inv_add_mul_I]
  have hpartial : Tendsto
      (fun n : ℕ => ∑ j ∈ Finset.range n,
        digammaRealDifferenceTerm a b j)
      atTop
      (𝓝 ((digamma z).re - (digamma w).re)) := by
    exact (tendsto_add_atTop_iff_nat 1).mp (by simpa [Nat.add_comm] using hshift)
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (digammaRealDifferenceTerm_nonneg ha b)]
  simpa [z, w] using hpartial

theorem tsum_exp_neg_add_nat_mul_one_sub_cos
    (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    (∑' j : ℕ,
      Real.exp (-(a + j) * t) * (1 - Real.cos (b * t))) =
      Real.exp (-a * t) / (1 - Real.exp (-t)) *
        (1 - Real.cos (b * t)) := by
  let q : ℝ := Real.exp (-t)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    unfold q
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  let C : ℝ := Real.exp (-a * t) * (1 - Real.cos (b * t))
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left C
  have hsum : HasSum
      (fun j : ℕ =>
        Real.exp (-(a + j) * t) * (1 - Real.cos (b * t)))
      (C * (1 - q)⁻¹) := by
    apply HasSum.congr_fun hgeo
    intro j
    have hexp : Real.exp (-(a + (j : ℝ)) * t) =
        Real.exp (-a * t) * q ^ j := by
      unfold q
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    unfold C
    ring
  rw [hsum.tsum_eq]
  unfold C q
  rw [div_eq_mul_inv]
  ring

theorem digamma_real_vertical_difference_eq_gauss_integral
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (digamma ((a : ℂ) + (b : ℂ) * I)).re -
        (digamma (a : ℂ)).re =
      ∫ t : ℝ in Ioi 0,
        Real.exp (-a * t) / (1 - Real.exp (-t)) *
          (1 - Real.cos (b * t)) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F : ℕ → ℝ → ℝ := fun j t =>
    Real.exp (-(a + j) * t) * (1 - Real.cos (b * t))
  have hterms := hasSum_digammaRealDifferenceTerm ha b
  have hFint : ∀ j : ℕ, Integrable (F j) μ := by
    intro j
    dsimp only [F, μ]
    exact integrableOn_exp_neg_mul_one_sub_cos
      (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)) b
  have hInt (j : ℕ) :
      (∫ t : ℝ, F j t ∂μ) =
        digammaRealDifferenceTerm a b j := by
    dsimp only [F, μ]
    exact (digammaRealDifferenceTerm_eq_integral ha b j).symm
  have hnormInt (j : ℕ) :
      (∫ t : ℝ, ‖F j t‖ ∂μ) =
        digammaRealDifferenceTerm a b j := by
    calc
      (∫ t : ℝ, ‖F j t‖ ∂μ) = ∫ t : ℝ, F j t ∂μ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg (Real.exp_pos _).le
          (sub_nonneg.mpr (Real.cos_le_one _))
      _ = _ := hInt j
  have hsumNorm : Summable (fun j : ℕ => ∫ t : ℝ, ‖F j t‖ ∂μ) := by
    exact hterms.summable.congr (fun j => (hnormInt j).symm)
  have hexchange := integral_tsum_of_summable_integral_norm hFint hsumNorm
  calc
    (digamma ((a : ℂ) + (b : ℂ) * I)).re -
        (digamma (a : ℂ)).re =
        ∑' j : ℕ, digammaRealDifferenceTerm a b j :=
      hterms.tsum_eq.symm
    _ = ∑' j : ℕ, ∫ t : ℝ, F j t ∂μ := by
      apply tsum_congr
      intro j
      exact (hInt j).symm
    _ = ∫ t : ℝ, ∑' j : ℕ, F j t ∂μ := hexchange
    _ = ∫ t : ℝ in Ioi 0,
        Real.exp (-a * t) / (1 - Real.exp (-t)) *
          (1 - Real.cos (b * t)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      dsimp only [F, μ]
      exact tsum_exp_neg_add_nat_mul_one_sub_cos a b ht

end Complex

namespace RiemannGaussian

open Filter MeasureTheory Topology Set
open scoped BigOperators Topology

theorem quarterLineGauss_change_variables (r : ℝ) :
    (∫ t : ℝ in Ioi 0,
      Real.exp (-(1 / 4 : ℝ) * t) /
          (1 - Real.exp (-t)) *
        (1 - Real.cos ((r / 2) * t))) =
      2 * ∫ u : ℝ in Ioi 0,
        gaussianSuzukiDigammaOscillationIntegrand r u := by
  let g : ℝ → ℝ := fun t =>
    Real.exp (-(1 / 4 : ℝ) * t) /
        (1 - Real.exp (-t)) *
      (1 - Real.cos ((r / 2) * t))
  have hchange := integral_comp_mul_left_Ioi' g 0
    (by norm_num : (0 : ℝ) < 2)
  have hpoint (u : ℝ) :
      g (2 * u) = gaussianSuzukiDigammaOscillationIntegrand r u := by
    unfold g gaussianSuzukiDigammaOscillationIntegrand
      gaussianSuzukiDigammaDensity
    have h₁ : -(1 / 4 : ℝ) * (2 * u) = -u / 2 := by ring
    have h₂ : -(2 * u) = -2 * u := by ring
    have h₃ : (r / 2) * (2 * u) = r * u := by ring
    rw [h₁, h₂, h₃]
  have hintegral :
      (∫ u : ℝ in Ioi 0, g (2 * u)) =
        ∫ u : ℝ in Ioi 0,
          gaussianSuzukiDigammaOscillationIntegrand r u := by
    apply integral_congr_ae
    filter_upwards with u
    exact hpoint u
  have hchange' : 2 * (∫ u : ℝ in Ioi 0, g (2 * u)) =
      ∫ t : ℝ in Ioi 0, g t := by
    simpa only [smul_eq_mul, mul_zero] using hchange
  rw [hintegral] at hchange'
  exact hchange'.symm

theorem quarterLineDigammaGaussDifferenceFormula :
    QuarterLineDigammaGaussDifferenceFormula := by
  intro r
  have hgauss :=
    Complex.digamma_real_vertical_difference_eq_gauss_integral
      (a := (1 / 4 : ℝ)) (by norm_num) (r / 2)
  have hleft :
      riemannArchimedeanDensity r - riemannArchimedeanDensity 0 =
        (Complex.digamma
          (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I)).re -
        (Complex.digamma (((1 / 4 : ℝ) : ℂ))).re := by
    have hz :
        (1 / 4 + Complex.I * ((r : ℂ) / 2) : ℂ) =
          (((1 / 4 : ℝ) : ℂ) +
            ((r / 2 : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    unfold riemannArchimedeanDensity
    rw [hz]
    norm_num
  rw [hleft, hgauss, quarterLineGauss_change_variables]

/-- Gauss's integral representation discharges the formerly conditional
digamma/missing-curvature transform. -/
theorem gaussianDigammaScrewTransform : GaussianDigammaScrewTransform :=
  gaussianDigammaScrewTransform_of_quarterLineGaussDifference
    quarterLineDigammaGaussDifferenceFormula

/-- The exact arithmetic Suzuki-curvature formula, now with no analytic
hypothesis. -/
theorem
    gaussianArithmeticExplicitFormula_eq_endpoint_add_primeEnergy_sub_suzukiSmooth_unconditional
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianArithmeticExplicitFormula ε t =
      gaussianArithmeticExplicitFormula ε 0 +
        gaussianPrimeOscillationEnergy ε t -
          gaussianSuzukiSmoothCurvatureEnergy ε t :=
  gaussianArithmeticExplicitFormula_eq_endpoint_add_primeEnergy_sub_suzukiSmooth
    gaussianDigammaScrewTransform hε t

/-- At every width, the exact Suzuki energy budget is unconditionally the
same proposition as arithmetic Gaussian positivity. -/
theorem gaussianSuzukiEnergyGoodWidth_iff_gaussianArithmeticGoodWidth_unconditional
    (ε : ℝ) :
    GaussianSuzukiEnergyGoodWidth ε ↔ GaussianArithmeticGoodWidth ε :=
  gaussianSuzukiEnergyGoodWidth_iff_gaussianArithmeticGoodWidth
    gaussianDigammaScrewTransform ε

/-- Cofinal exact Suzuki energy budgets are unconditionally equivalent to
the Riemann hypothesis.  This identifies the remaining frontier; it does not
prove that the budgets hold. -/
theorem gaussianSuzukiEnergyGoodWidthsUnbounded_iff_riemannHypothesis_unconditional :
    GaussianSuzukiEnergyGoodWidthsUnbounded ↔ RiemannHypothesis :=
  gaussianSuzukiEnergyGoodWidthsUnbounded_iff_riemannHypothesis
    gaussianDigammaScrewTransform

end RiemannGaussian

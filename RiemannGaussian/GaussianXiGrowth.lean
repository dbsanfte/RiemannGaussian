import RiemannGaussian.GaussianZetaCounting

/-!
# Quantitative growth of the pole-cleared zeta xi function

This file develops the remaining analytic estimate used by
`GaussianZetaCounting`.  The first step upgrades Mathlib's asymptotic
exponential decay of the modified theta kernel to a uniform bound on the
whole ray `[1, ∞)`.
-/

namespace RiemannGaussian

noncomputable section

open Asymptotics Filter MeasureTheory Set Topology

/-- The nonconstant part of the Riemann theta kernel, complexified. -/
def riemannThetaTail (x : ℝ) : ℂ :=
  (HurwitzZeta.evenKernel 0 x : ℂ) - 1

theorem continuousOn_riemannThetaTail :
    ContinuousOn riemannThetaTail (Ioi 0) := by
  unfold riemannThetaTail
  exact (Complex.continuous_ofReal.comp_continuousOn
    (HurwitzZeta.continuousOn_evenKernel 0)).sub continuousOn_const

/-- Exponential decay of the theta tail, uniformly from `x = 1` onward.
The constants are not optimized; only their existence and positivity matter
for the quadratic xi-growth estimate. -/
theorem exists_riemannThetaTail_exp_bound :
    ∃ (C p : ℝ), 1 ≤ C ∧ 0 < p ∧ ∀ x : ℝ, 1 ≤ x →
      ‖riemannThetaTail x‖ ≤ C * Real.exp (-p * x) := by
  obtain ⟨p, hp, hbigO⟩ :=
    HurwitzZeta.isBigO_atTop_evenKernel_sub (0 : UnitAddCircle)
  have hbigO' :
      riemannThetaTail =O[atTop] fun x : ℝ => Real.exp (-p * x) := by
    change (fun x : ℝ =>
      (HurwitzZeta.evenKernel 0 x : ℂ) - 1) =O[atTop]
        fun x : ℝ => Real.exp (-p * x)
    simpa using Complex.isBigO_ofReal_left.mpr hbigO
  obtain ⟨Ctop, hCtop⟩ := hbigO'.bound
  rw [eventually_atTop] at hCtop
  obtain ⟨a, ha⟩ := hCtop
  let M : ℝ := max 1 a
  have hM1 : 1 ≤ M := le_max_left _ _
  have haM : a ≤ M := le_max_right _ _
  have hcontinuous : ContinuousOn (fun x => ‖riemannThetaTail x‖)
      (Icc 1 M) := by
    exact (continuousOn_riemannThetaTail.mono
      (fun x hx => by exact hx.1.trans_lt' zero_lt_one)).norm
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_Icc.bddAbove_image hcontinuous)
  let C : ℝ := max 1 (max Ctop (C₀ * Real.exp (p * M)))
  refine ⟨C, p, le_max_left _ _, hp, ?_⟩
  intro x hx
  by_cases hMx : M ≤ x
  · have hbound := ha x (haM.trans hMx)
    have hbound' :
        ‖riemannThetaTail x‖ ≤ Ctop * Real.exp (-p * x) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        using hbound
    have hCtopC : Ctop ≤ C :=
      (le_max_left Ctop (C₀ * Real.exp (p * M))).trans
        (le_max_right 1 _)
    exact hbound'.trans
      (mul_le_mul_of_nonneg_right hCtopC (Real.exp_nonneg _))
  · have hxM : x ≤ M := le_of_not_ge hMx
    have hnormC₀ : ‖riemannThetaTail x‖ ≤ C₀ := by
      apply hC₀
      exact ⟨x, ⟨hx, hxM⟩, rfl⟩
    have hC₀nonneg : 0 ≤ C₀ :=
      (norm_nonneg (riemannThetaTail x)).trans hnormC₀
    have hratio :
        C₀ ≤ (C₀ * Real.exp (p * M)) * Real.exp (-p * x) := by
      rw [mul_assoc, ← Real.exp_add]
      have hexp : 1 ≤ Real.exp (p * M + -p * x) := by
        rw [Real.one_le_exp_iff]
        nlinarith
      simpa using mul_le_mul_of_nonneg_left hexp hC₀nonneg
    have hcompactC : C₀ * Real.exp (p * M) ≤ C :=
      (le_max_right Ctop (C₀ * Real.exp (p * M))).trans
        (le_max_right 1 _)
    exact hnormC₀.trans <| hratio.trans <|
      mul_le_mul_of_nonneg_right hcompactC (Real.exp_nonneg _)

/-- The upper-half theta tail used in the split Mellin representation. -/
def riemannThetaUpper : ℝ → ℂ :=
  (Ioi 1).indicator riemannThetaTail

theorem riemannThetaUpper_eq_tail {x : ℝ} (hx : 1 < x) :
    riemannThetaUpper x = riemannThetaTail x := by
  simp [riemannThetaUpper, hx]

theorem riemannThetaUpper_eq_zero {x : ℝ} (hx : x ≤ 1) :
    riemannThetaUpper x = 0 := by
  simp [riemannThetaUpper, hx]

/-- The modified theta kernel is the sum of its upper tail and the
functional-equation reflection of that tail. -/
theorem riemann_f_modif_eq_upper_add_reflection (x : ℝ) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x =
      riemannThetaUpper x +
        (x : ℂ) ^ (-(1 / 2 : ℂ)) • riemannThetaUpper (1 / x) := by
  by_cases hx : 0 < x
  · rcases lt_trichotomy x 1 with hx1 | rfl | hx1
    · have hinv : 1 < 1 / x := by
        exact (one_lt_div hx).mpr hx1
      rw [riemannThetaUpper_eq_zero hx1.le,
        riemannThetaUpper_eq_tail hinv, zero_add]
      rw [WeakFEPair.f_modif, Pi.add_apply,
        Set.indicator_of_notMem (notMem_Ioi.mpr hx1.le), zero_add,
        Set.indicator_of_mem (mem_Ioo.mpr ⟨hx, hx1⟩)]
      simp only [HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply,
        if_pos, one_mul, one_smul]
      rw [HurwitzZeta.evenKernel_functional_equation]
      push_cast
      rw [Complex.ofReal_cpow hx.le, Complex.ofReal_div,
        Complex.ofReal_one]
      field_simp [hx.ne']
      rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
      unfold riemannThetaTail
      simp only [smul_eq_mul, mul_one]
      have hreal :
          x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [← Real.rpow_add hx]
        norm_num
      have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
        norm_num
      have hcomplex :
          (x : ℂ) ^ (1 / 2 : ℂ) *
              ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
        rw [hhalf, ← Complex.ofReal_cpow hx.le, ← Complex.ofReal_mul,
          hreal, Complex.ofReal_one]
      have hcpow :
          (x : ℂ) ^ (1 / 2 : ℂ) *
              (x : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
        rw [← Complex.cpow_add _ _
          (Complex.ofReal_ne_zero.mpr hx.ne')]
        norm_num
      change (HurwitzZeta.evenKernel 0 (1 / x) : ℂ) -
          (x : ℂ) ^ (1 / 2 : ℂ) *
            ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        (x : ℂ) ^ (1 / 2 : ℂ) *
          ((x : ℂ) ^ (-(1 / 2 : ℂ)) *
            ((HurwitzZeta.evenKernel 0 (1 / x) : ℂ) - 1))
      rw [hcomplex, ← mul_assoc, hcpow, one_mul]
    · simp [WeakFEPair.f_modif, riemannThetaUpper]
    · have hinv : 1 / x ≤ 1 := by
        exact (div_le_one hx).mpr hx1.le
      rw [riemannThetaUpper_eq_tail hx1,
        riemannThetaUpper_eq_zero hinv, smul_zero, add_zero]
      simp [WeakFEPair.f_modif, riemannThetaUpper, hx1,
        notMem_Ioo_of_ge hx1.le, riemannThetaTail,
        HurwitzZeta.hurwitzEvenFEPair]
  · have hxle : x ≤ 0 := le_of_not_gt hx
    have hinv : 1 / x ≤ 1 := by
      by_cases hxzero : x = 0
      · simp [hxzero]
      · have hxneg : x < 0 := lt_of_le_of_ne hxle hxzero
        exact (div_nonpos_of_nonneg_of_nonpos zero_le_one hxle).trans
          zero_le_one
    rw [riemannThetaUpper_eq_zero (hxle.trans zero_le_one),
      riemannThetaUpper_eq_zero hinv, smul_zero, add_zero]
    rw [WeakFEPair.f_modif, Pi.add_apply,
      Set.indicator_of_notMem
        (notMem_Ioi.mpr (hxle.trans zero_le_one)),
      Set.indicator_of_notMem (notMem_Ioo_of_le hxle)]
    simp

/-- The upper theta tail is locally integrable on the positive reals. -/
theorem locallyIntegrableOn_riemannThetaUpper :
    LocallyIntegrableOn riemannThetaUpper (Ioi 0) := by
  have htail : LocallyIntegrableOn riemannThetaTail (Ioi 0) :=
    continuousOn_riemannThetaTail.locallyIntegrableOn measurableSet_Ioi
  intro x hx
  obtain ⟨U, hU, hInt⟩ := htail x hx
  refine ⟨U, hU, ?_⟩
  simpa [riemannThetaUpper] using hInt.indicator measurableSet_Ioi

/-- Exponential decay of the upper tail in `IsBigO` form. -/
theorem exists_isBigO_riemannThetaUpper_exp :
    ∃ p : ℝ, 0 < p ∧
      riemannThetaUpper =O[atTop]
        fun x : ℝ => Real.exp (-p * x) := by
  obtain ⟨C, p, hC, hp, hbound⟩ :=
    exists_riemannThetaTail_exp_bound
  refine ⟨p, hp, IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_gt_atTop 1] with x hx
  rw [riemannThetaUpper_eq_tail hx]
  have h := hbound x hx.le
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using h

/-- The upper theta tail vanishes near zero, so it has any power bound
there. -/
theorem isBigO_riemannThetaUpper_nhdsGT_zero (b : ℝ) :
    riemannThetaUpper =O[𝓝[>] 0] fun x : ℝ => x ^ (-b) := by
  apply IsBigO.of_bound 0
  filter_upwards [(eventually_le_nhds zero_lt_one).filter_mono
    nhdsWithin_le_nhds] with x hx
  rw [riemannThetaUpper_eq_zero hx]
  simp

/-- The upper-tail Mellin transform converges for every complex exponent. -/
theorem mellinConvergent_riemannThetaUpper (s : ℂ) :
    MellinConvergent riemannThetaUpper s := by
  obtain ⟨p, hp, htop⟩ := exists_isBigO_riemannThetaUpper_exp
  apply mellinConvergent_of_isBigO_rpow_exp hp
    locallyIntegrableOn_riemannThetaUpper htop
    (isBigO_riemannThetaUpper_nhdsGT_zero (s.re - 1))
  linarith

/-- Reflected lower-half theta tail. -/
def riemannThetaReflection (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-(1 / 2 : ℂ)) • riemannThetaUpper (1 / x)

theorem riemann_f_modif_eq_upper_add_reflection_fun :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif =
      riemannThetaUpper + riemannThetaReflection := by
  funext x
  exact riemann_f_modif_eq_upper_add_reflection x

/-- The reflected tail also has a globally convergent Mellin transform. -/
theorem mellinConvergent_riemannThetaReflection (s : ℂ) :
    MellinConvergent riemannThetaReflection s := by
  let P := HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)
  have hfmodif : MellinConvergent P.f_modif s := by
    exact (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  have hupper := mellinConvergent_riemannThetaUpper s
  have hdifference :
      MellinConvergent (fun x => P.f_modif x - riemannThetaUpper x) s :=
    (hasMellin_sub hfmodif hupper).1
  have hreflection :
      riemannThetaReflection =
        fun x => P.f_modif x - riemannThetaUpper x := by
    funext x
    have hdecomp := riemann_f_modif_eq_upper_add_reflection x
    dsimp [P] at hdecomp ⊢
    rw [hdecomp]
    abel
  rw [hreflection]
  exact hdifference

/-- Mellin transformation of the reflected theta tail. -/
theorem mellin_riemannThetaReflection (s : ℂ) :
    mellin riemannThetaReflection s =
      mellin riemannThetaUpper (1 / 2 - s) := by
  unfold riemannThetaReflection
  calc
    mellin
        (fun x : ℝ =>
          (x : ℂ) ^ (-(1 / 2 : ℂ)) •
            riemannThetaUpper (1 / x)) s =
        mellin (fun x : ℝ => riemannThetaUpper (1 / x))
          (s + -(1 / 2 : ℂ)) :=
      mellin_cpow_smul
        (fun x : ℝ => riemannThetaUpper (1 / x)) s
          (-(1 / 2 : ℂ))
    _ = mellin riemannThetaUpper (-(s + -(1 / 2 : ℂ))) := by
      simpa [one_div] using
        mellin_comp_inv riemannThetaUpper (s + -(1 / 2 : ℂ))
    _ = mellin riemannThetaUpper (1 / 2 - s) := by
      congr 2
      ring

/-- Split Mellin representation of Mathlib's entire modified completed-zeta
kernel. -/
theorem mellin_riemann_f_modif_eq_upper_add_reflected (s : ℂ) :
    mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif s =
      mellin riemannThetaUpper s +
        mellin riemannThetaUpper (1 / 2 - s) := by
  rw [riemann_f_modif_eq_upper_add_reflection_fun]
  change mellin
      (fun x => riemannThetaUpper x + riemannThetaReflection x) s = _
  rw [(hasMellin_add
    (mellinConvergent_riemannThetaUpper s)
    (mellinConvergent_riemannThetaReflection s)).2]
  rw [mellin_riemannThetaReflection]

/-- Exact two-upper-tail Mellin formula for `completedRiemannZeta₀`. -/
theorem completedRiemannZeta₀_eq_upperMellin (s : ℂ) :
    completedRiemannZeta₀ s =
      (mellin riemannThetaUpper (s / 2) +
        mellin riemannThetaUpper ((1 - s) / 2)) / 2 := by
  change mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (s / 2) / 2 = _
  rw [mellin_riemann_f_modif_eq_upper_add_reflected]
  congr 2
  ring

/-- A power of `x` can be absorbed into half of an exponential tail, at
quadratic cost in the exponent.  This deliberately coarse estimate is the
quantitative core of the xi-growth argument. -/
theorem rpow_mul_exp_neg_le_exp_sq_mul_exp_neg_half
    {p x u : ℝ} (hp : 0 < p) (hx : 1 ≤ x) :
    x ^ u * Real.exp (-p * x) ≤
      Real.exp (2 * u ^ 2 / p) * Real.exp (-(p / 2) * x) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    calc
      Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
        Real.log_le_rpow_div hx0 (by positivity)
      _ = 2 * Real.sqrt x := by
        rw [← Real.sqrt_eq_rpow]
        ring
  have hlog_mul : u * Real.log x ≤ 2 * |u| * Real.sqrt x := by
    calc
      u * Real.log x ≤ |u| * Real.log x :=
        mul_le_mul_of_nonneg_right (le_abs_self u) hlog_nonneg
      _ ≤ |u| * (2 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hlog (abs_nonneg u)
      _ = 2 * |u| * Real.sqrt x := by ring
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
  have hyoung : 2 * |u| * Real.sqrt x ≤
      2 * u ^ 2 / p + p * x / 2 := by
    have hden : 0 < 2 * p := mul_pos (by positivity) hp
    rw [show 2 * u ^ 2 / p + p * x / 2 =
        (4 * u ^ 2 + p ^ 2 * x) / (2 * p) by
      field_simp [hp.ne']
      <;> ring]
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg (2 * |u| - p * Real.sqrt x), sq_abs u]
  have hexponent : Real.log x * u + (-p * x) ≤
      2 * u ^ 2 / p + (-(p / 2) * x) := by
    nlinarith [hlog_mul.trans hyoung]
  rw [Real.rpow_def_of_pos hxpos, ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hexponent

/-- Quantitative bound for the entire upper-tail Mellin transform. -/
theorem norm_mellin_riemannThetaUpper_le
    {C p : ℝ} (hC : 1 ≤ C) (hp : 0 < p)
    (hbound : ∀ x : ℝ, 1 ≤ x →
      ‖riemannThetaTail x‖ ≤ C * Real.exp (-p * x))
    (s : ℂ) :
    ‖mellin riemannThetaUpper s‖ ≤
      (2 * C / p) * Real.exp (2 * (s.re - 1) ^ 2 / p) := by
  let Q : ℝ := 2 * (s.re - 1) ^ 2 / p
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hhalf : 0 < p / 2 := by positivity
  have hmajorant : IntegrableOn
      (fun x : ℝ => (C * Real.exp Q) * Real.exp (-(p / 2) * x))
      (Ioi 0) := by
    change Integrable
      (fun x : ℝ => (C * Real.exp Q) * Real.exp (-(p / 2) * x))
      (volume.restrict (Ioi 0))
    exact (exp_neg_integrableOn_Ioi 0 hhalf).const_mul
      (C * Real.exp Q)
  rw [mellin]
  calc
    ‖∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) • riemannThetaUpper x‖ ≤
        ∫ x : ℝ in Ioi 0,
          (C * Real.exp Q) * Real.exp (-(p / 2) * x) := by
      apply norm_integral_le_of_norm_le hmajorant
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx0
      by_cases hx1 : x ≤ 1
      · rw [riemannThetaUpper_eq_zero hx1, smul_zero, norm_zero]
        positivity
      · have hx1' : 1 < x := lt_of_not_ge hx1
        rw [riemannThetaUpper_eq_tail hx1', norm_smul,
          Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re,
          Complex.one_re]
        calc
          x ^ (s.re - 1) * ‖riemannThetaTail x‖ ≤
              x ^ (s.re - 1) * (C * Real.exp (-p * x)) :=
            mul_le_mul_of_nonneg_left (hbound x hx1'.le)
              (Real.rpow_nonneg hx0.le _)
          _ = C * (x ^ (s.re - 1) * Real.exp (-p * x)) := by ring
          _ ≤ C *
              (Real.exp (2 * (s.re - 1) ^ 2 / p) *
                Real.exp (-(p / 2) * x)) :=
            mul_le_mul_of_nonneg_left
              (rpow_mul_exp_neg_le_exp_sq_mul_exp_neg_half hp hx1'.le)
              hC0
          _ = (C * Real.exp Q) * Real.exp (-(p / 2) * x) := by
            simp only [Q]
            ring
    _ = (C * Real.exp Q) * (2 / p) := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (a := -(p / 2)) (by linarith) 0]
      simp [hp.ne']
    _ = (2 * C / p) * Real.exp (2 * (s.re - 1) ^ 2 / p) := by
      simp only [Q]
      field_simp [hp.ne']

/-- The split Mellin formula gives a global quadratic bound for the entire
completed-zeta regularization. -/
theorem norm_completedRiemannZeta₀_le
    {C p : ℝ} (hC : 1 ≤ C) (hp : 0 < p)
    (hbound : ∀ x : ℝ, 1 ≤ x →
      ‖riemannThetaTail x‖ ≤ C * Real.exp (-p * x))
    (s : ℂ) :
    ‖completedRiemannZeta₀ s‖ ≤
      (2 * C / p) * Real.exp ((2 / p) * (‖s‖ + 1) ^ 2) := by
  let K : ℝ := 2 * C / p
  let E : ℝ := Real.exp ((2 / p) * (‖s‖ + 1) ^ 2)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hR0 : 0 ≤ ‖s‖ + 1 := by positivity
  have hre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hfirst_abs : |(s / 2).re - 1| ≤ ‖s‖ + 1 := by
    calc
      |(s / 2).re - 1| = |(s.re - 2) / 2| := by
        congr 1
        norm_num
        ring
      _ = |s.re - 2| / 2 := by norm_num [abs_div]
      _ ≤ (|s.re| + 2) / 2 := by
        gcongr
        simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
          abs_sub s.re 2
      _ ≤ ‖s‖ + 1 := by nlinarith [norm_nonneg s]
  have hsecond_abs : |((1 - s) / 2).re - 1| ≤ ‖s‖ + 1 := by
    calc
      |((1 - s) / 2).re - 1| = |-(s.re + 1) / 2| := by
        congr 1
        norm_num
        ring
      _ = |-(s.re + 1)| / 2 := by
        rw [abs_div]
        norm_num
      _ = |s.re + 1| / 2 := by rw [abs_neg]
      _ ≤ (|s.re| + 1) / 2 := by
        gcongr
        simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] using
          abs_add_le s.re 1
      _ ≤ ‖s‖ + 1 := by nlinarith [norm_nonneg s]
  have hfirst_sq : ((s / 2).re - 1) ^ 2 ≤ (‖s‖ + 1) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hR0]
    exact hfirst_abs
  have hsecond_sq : (((1 - s) / 2).re - 1) ^ 2 ≤
      (‖s‖ + 1) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hR0]
    exact hsecond_abs
  have hcoeff : 0 ≤ 2 / p := by positivity
  have hfirst_exp :
      Real.exp (2 * ((s / 2).re - 1) ^ 2 / p) ≤ E := by
    apply Real.exp_le_exp.mpr
    change 2 * ((s / 2).re - 1) ^ 2 / p ≤
      (2 / p) * (‖s‖ + 1) ^ 2
    calc
      2 * ((s / 2).re - 1) ^ 2 / p =
          (2 / p) * ((s / 2).re - 1) ^ 2 := by ring
      _ ≤ (2 / p) * (‖s‖ + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hfirst_sq hcoeff
  have hsecond_exp :
      Real.exp (2 * (((1 - s) / 2).re - 1) ^ 2 / p) ≤ E := by
    apply Real.exp_le_exp.mpr
    change 2 * (((1 - s) / 2).re - 1) ^ 2 / p ≤
      (2 / p) * (‖s‖ + 1) ^ 2
    calc
      2 * (((1 - s) / 2).re - 1) ^ 2 / p =
          (2 / p) * (((1 - s) / 2).re - 1) ^ 2 := by ring
      _ ≤ (2 / p) * (‖s‖ + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hsecond_sq hcoeff
  have hfirst : ‖mellin riemannThetaUpper (s / 2)‖ ≤ K * E :=
    (norm_mellin_riemannThetaUpper_le hC hp hbound (s / 2)).trans
      (mul_le_mul_of_nonneg_left hfirst_exp hK0)
  have hsecond : ‖mellin riemannThetaUpper ((1 - s) / 2)‖ ≤ K * E :=
    (norm_mellin_riemannThetaUpper_le hC hp hbound ((1 - s) / 2)).trans
      (mul_le_mul_of_nonneg_left hsecond_exp hK0)
  rw [completedRiemannZeta₀_eq_upperMellin, norm_div]
  norm_num
  calc
    ‖mellin riemannThetaUpper (s / 2) +
        mellin riemannThetaUpper ((1 - s) / 2)‖ / 2 ≤
        (‖mellin riemannThetaUpper (s / 2)‖ +
          ‖mellin riemannThetaUpper ((1 - s) / 2)‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (K * E + K * E) / 2 := by gcongr
    _ = (2 * C / p) * Real.exp ((2 / p) * (‖s‖ + 1) ^ 2) := by
      simp only [K, E]
      ring

/-- Mathlib's theta-kernel estimates imply the isolated global growth
hypothesis used by the Jensen zero-counting argument. -/
theorem riemannXi_quadraticGrowth : RiemannXiQuadraticGrowth := by
  obtain ⟨C, p, hC, hp, htail⟩ := exists_riemannThetaTail_exp_bound
  let K : ℝ := max 1 (2 * C / p)
  let B : ℝ := 2 / p
  let A : ℝ := K + B + 2
  have hrawK0 : 0 ≤ 2 * C / p := by positivity
  have hK1 : 1 ≤ K := le_max_left _ _
  have hrawK_le : 2 * C / p ≤ K := le_max_right _ _
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hA1 : 1 ≤ A := by
    dsimp [A]
    linarith
  refine ⟨A, hA1, ?_⟩
  intro z
  let R : ℝ := ‖z‖ + 1
  let T : ℝ := R ^ 2
  let E : ℝ := Real.exp (B * T)
  have hR1 : 1 ≤ R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hT1 : 1 ≤ T := by
    dsimp [T]
    nlinarith [sq_nonneg (R - 1)]
  have hE1 : 1 ≤ E := by
    dsimp [E]
    rw [Real.one_le_exp_iff]
    exact mul_nonneg hB0 (zero_le_one.trans hT1)
  have hcompleted : ‖completedRiemannZeta₀ z‖ ≤ K * E := by
    calc
      ‖completedRiemannZeta₀ z‖ ≤
          (2 * C / p) * Real.exp ((2 / p) * (‖z‖ + 1) ^ 2) :=
        norm_completedRiemannZeta₀_le hC hp htail z
      _ = (2 * C / p) * E := by simp only [B, E, T, R]
      _ ≤ K * E :=
        mul_le_mul_of_nonneg_right hrawK_le (Real.exp_nonneg _)
  have hone_sub : ‖1 - z‖ ≤ R := by
    calc
      ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = R := by simp [R, add_comm]
  have hzR : ‖z‖ ≤ R := by
    dsimp [R]
    linarith
  have hpoly : ‖z‖ * ‖1 - z‖ ≤ T := by
    calc
      ‖z‖ * ‖1 - z‖ ≤ R * R :=
        mul_le_mul hzR hone_sub (norm_nonneg _) (zero_le_one.trans hR1)
      _ = T := by simp [T, pow_two]
  have hmain :
      ‖z * (1 - z) * completedRiemannZeta₀ z‖ ≤ K * T * E := by
    rw [norm_mul, norm_mul]
    calc
      ‖z‖ * ‖1 - z‖ * ‖completedRiemannZeta₀ z‖ ≤
          T * (K * E) :=
        mul_le_mul hpoly hcompleted (norm_nonneg _)
          (zero_le_one.trans hT1)
      _ = K * T * E := by ring
  have hKTE1 : 1 ≤ K * T * E := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hK1 hT1) hE1
  have htwo_exp : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp 1]
  have hK_exp : K ≤ Real.exp K := by
    linarith [Real.add_one_le_exp K]
  have hT_exp : T ≤ Real.exp T := by
    linarith [Real.add_one_le_exp T]
  have hexponent : 1 + K + T + B * T ≤ A * T := by
    have hnonneg : 0 ≤ (K + 1) * (T - 1) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp [A]
    nlinarith
  have habsorb : 2 * (K * T * E) ≤ Real.exp (A * T) := by
    calc
      2 * (K * T * E) = 2 * K * T * E := by ring
      _ ≤ Real.exp 1 * Real.exp K * Real.exp T * E := by
        gcongr
      _ = Real.exp (1 + K + T + B * T) := by
        simp only [E, ← Real.exp_add]
      _ ≤ Real.exp (A * T) := Real.exp_le_exp.mpr hexponent
  unfold riemannXi
  calc
    ‖z * (1 - z) * completedRiemannZeta₀ z - 1‖ ≤
        ‖z * (1 - z) * completedRiemannZeta₀ z‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ K * T * E + 1 := by simpa using add_le_add_right hmain 1
    _ ≤ 2 * (K * T * E) := by linarith
    _ ≤ Real.exp (A * T) := habsorb
    _ = Real.exp (A * (‖z‖ + 1) ^ 2) := by rfl

/-- Consequently the multiplicity-aware Gaussian zero sum converges, with
no separate zero-counting assumption. -/
theorem zetaZeroGaussianOrdinateSummable :
    ZetaZeroGaussianOrdinateSummable :=
  zetaZeroGaussianOrdinateSummable_of_riemannXiQuadraticGrowth
    riemannXi_quadraticGrowth

/-- The occurrence enumeration therefore represents the canonical
multiplicity-weighted Gaussian sum unconditionally. -/
theorem representsCanonicalZetaGaussianZeroSum_unconditional :
    RepresentsZetaGaussianZeroSum analyticZetaZeroMultiplicity
      canonicalZetaGaussianZeroSum :=
  representsCanonicalZetaGaussianZeroSum zetaZeroGaussianOrdinateSummable

/-- With convergence discharged, positivity of the canonical symmetric
Gaussian zero sum is unconditionally equivalent to RH. -/
theorem canonicalZetaSymmetricGaussianZeroSum_nonnegative_iff_RH :
    ZetaSymmetricGaussianZeroSumNonnegative
        canonicalZetaSymmetricGaussianZeroSum ↔
      RiemannHypothesis :=
  canonicalZetaSymmetricGaussianZeroSum_nonnegative_iff_riemannHypothesis
    zetaZeroGaussianOrdinateSummable

end

end RiemannGaussian

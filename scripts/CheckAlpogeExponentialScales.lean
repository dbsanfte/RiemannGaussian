import CheckAlpogeZetaWindows
import RiemannGaussian.PrimeMassFromZeroBound

/-! # Absolute zeta control at the exponential scales of Alpöge's size construction -/

namespace RiemannGaussian.AlpogeWindow
noncomputable section
open Real Set Filter MeasureTheory

private theorem psi_power :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 4 ≤ t → |Chebyshev.psi t-t| ≤ K*t^(15/16:ℝ) := by
  let A := 289+Real.pi^2/6+log (2*Real.pi)
  let L := 1+32/log 2
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity [log_nonneg (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three])]
  refine ⟨A*L^2,mul_nonneg hA (sq_nonneg _),fun t ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith
  have ht0 := zero_lt_one.trans_le ht1
  have hlog := Real.log_le_rpow_div ht0.le (by norm_num : 0 < (1/32:ℝ))
  have hL : 1+log t/log 2 ≤ L*t^(1/32:ℝ) := by
    dsimp [L]
    have h := div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    apply (add_le_add (Real.one_le_rpow ht1 (by norm_num : 0 ≤ (1/32:ℝ))) h).trans_eq
    ring
  have hpos : 0 ≤ 1+log t/log 2 := by positivity [log_nonneg ht1]
  have h := PrimeMassFromZeroBound.psi_error (B := 7/8) (by norm_num) (by norm_num)
    suzukiLocalZero_re_le_seven_eighths ht
  apply h.trans
  change A*(t^(7/8:ℝ)*(1+log t/log 2)^2) ≤ _
  calc _ ≤ A*(t^(7/8:ℝ)*(L*t^(1/32:ℝ))^2) := by gcongr
       _ = _ := by
         rw [mul_pow,← Real.rpow_mul_natCast ht0.le,
           show A*(t^(7/8:ℝ)*(L^2*t^((1/32:ℝ)*(2:ℕ)))) = A*L^2*(t^(7/8:ℝ)*t^((1/32:ℝ)*(2:ℕ))) by ring,
           ← Real.rpow_add ht0]
         norm_num

private theorem normalized_increment_abs {K a b : ℝ} (hK : 0 ≤ K)
    (h : ∀ t : ℝ, 4 ≤ t → |Chebyshev.psi t-t| ≤ K*t^(15/16:ℝ)) (ha : 4 ≤ a) (hab : a ≤ b) :
    |Deduction.G a/a - Deduction.G b/b| ≤ 16*K*a^(-1/16:ℝ) := by
  have ha0 : 0 < a := by linarith
  rw [G_native,G_native,AlpogeZetaSamples.G_normalized_increment ha0 hab,← Real.norm_eq_abs]
  have hi : IntegrableOn (fun t : ℝ => K*t^(-17/16:ℝ)) (Ioi a) := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-17/16:ℝ) < -1) ha0).const_mul K
  have hsub : Ioc a b ⊆ Ioi a := fun _ ht => ht.1
  calc _ ≤ ∫ t in Ioc a b, K*t^(-17/16:ℝ) := by
         apply MeasureTheory.norm_integral_le_of_norm_le (hi.mono_set hsub)
         filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
         have ht0 := ha0.trans ht.1
         rw [Real.norm_eq_abs,abs_div,abs_of_pos (pow_pos ht0 2),abs_sub_comm]
         apply (div_le_iff₀ (pow_pos ht0 2)).mpr
         rw [mul_assoc,← Real.rpow_natCast t 2,← Real.rpow_add ht0]
         rw [show (-17/16:ℝ)+(2:ℕ) = 15/16 by norm_num]
         exact h t (ha.trans ht.1.le)
       _ ≤ ∫ t in Ioi a, K*t^(-17/16:ℝ) := by
         apply setIntegral_mono_set hi _ (ae_of_all _ hsub)
         filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
         exact mul_nonneg hK (Real.rpow_nonneg (ha0.trans ht).le _)
       _ = _ := by
         rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) ha0]
         norm_num
         ring

/-- The normalized modulus-one remainder is absolutely bounded by a negative power.
The cofinal observations of both signs fix its integration constant. -/
theorem abs_G_div_power :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 4 ≤ a → |Deduction.G a/a| ≤ C*a^(-1/16:ℝ) := by
  obtain ⟨K,hK,h⟩ := psi_power
  refine ⟨16*K,by positivity,fun a ha => ?_⟩
  obtain ⟨Y,hy,hpos,hneg⟩ := ((eventually_ge_atTop a).and
    (eventually_G_excursions (θ := 1/4) (δ := 1) (by norm_num) (by norm_num) (by norm_num) 0)).exists
  obtain ⟨b,hb,hplus⟩ := hpos
  obtain ⟨c,hc,hminus⟩ := hneg
  have hbp : 0 ≤ Deduction.G b / b := div_nonneg (by simpa using hplus.le) (by linarith [hb.1])
  have hcn : Deduction.G c / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by simpa using hminus.le) (by linarith [hc.1])
  exact abs_le.mpr ⟨by linarith only [(abs_le.mp (normalized_increment_abs hK h ha (hy.trans hb.1))).1,hbp],
    by linarith only [(abs_le.mp (normalized_increment_abs hK h ha (hy.trans hc.1))).2,hcn]⟩

/-- The actual zeta function supplies the principal-character part of ThinScales
with the exponential threshold and tolerance from PChain.ModelText. -/
theorem exponential_zeta_thin_scales {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, exp (x^(ε/3))/3 ≤ y →
      |Deduction.G y| ≤ y * exp (-(x^(ε/8))) := by
  obtain ⟨C,hC,h⟩ := abs_G_div_power
  have ha : 0 < ε/3-ε/8 := by linarith
  have hb : 0 < ε/8 := by linarith
  filter_upwards [eventually_gt_atTop (0:ℝ), (tendsto_rpow_atTop ha).eventually_ge_atTop 32,
    (tendsto_rpow_atTop hb).eventually_ge_atTop (C+log 12+log 3+1)] with x hx h32 hscale
  intro y hy
  have hp := mul_le_mul_of_nonneg_right h32 (Real.rpow_nonneg hx.le (ε/8))
  rw [← Real.rpow_add hx,sub_add_cancel] at hp
  have h3 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
  have h12 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 12)
  have h4 : 4 ≤ y := by
    have hh : exp (log 12) ≤ exp (x^(ε/3)) := exp_le_exp.mpr (by linarith)
    rw [Real.exp_log (by norm_num : (0:ℝ)<12)] at hh
    linarith
  have hy0 : 0 < y := by linarith
  have hl := Real.log_le_log (div_pos (exp_pos _) (by norm_num : (0:ℝ)<3)) hy
  rw [Real.log_div (exp_pos _).ne' (by norm_num),Real.log_exp] at hl
  have hh := h y h4
  rw [abs_div,abs_of_pos hy0,Real.rpow_def_of_pos hy0] at hh
  rw [mul_comm y]
  apply (div_le_iff₀ hy0).mp
  calc
    _ ≤ C*exp (log y * (-1/16)) := hh
    _ ≤ exp C * exp (log y * (-1/16)) :=
      mul_le_mul_of_nonneg_right (by linarith only [Real.add_one_le_exp C]) (exp_pos _).le
    _ ≤ exp (-(x^(ε/8))) := by rw [← exp_add]; apply exp_le_exp.mpr; linarith only [hp,hl,hscale,h12,h3]

end
end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  for ax in ← Lean.collectAxioms ``RiemannGaussian.AlpogeWindow.exponential_zeta_thin_scales do
    unless [``propext,``Classical.choice,``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax}"

import CheckAlpogeFixedPrimeBand
import RiemannGaussian.AlpogeZetaPowerWindows

/-! # Quantitative bounds on the fixed prime band from a zero half-plane -/

noncomputable section
namespace RiemannGaussian.AlpogeMined
open Real Set MeasureTheory Filter DyadicPrime

private theorem normalized_step {a b x B : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hba : b ≤ 2*a)
    (hbx : b ≤ x) (hB : 0 ≤ B) (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) :
    |a*(Deduction.G a/a-Deduction.G b/b)| ≤ 40*x^B := by
  have ha₀ := zero_lt_one.trans_le ha
  obtain ⟨v,hv,he⟩ := exists_real_primitive_increment ha hab
  rw [fixedBand_G_eq_native,fixedBand_G_eq_native,AlpogeZetaSamples.G_normalized_increment ha₀ hab,
    he,mul_div_cancel₀ _ ha₀.ne']
  have H := primeError_dyadic_variation_of_re_le hB hz ha hv.1 0
  norm_num only [Nat.cast_zero,zero_add,zero_pow,one_pow,pow_one] at H
  have hv₀ := ha₀.trans_le hv.1
  have hlog := log_le_log hv₀ (hv.2.trans hba)
  rw [log_mul (by norm_num : (2:ℝ) ≠ 0) ha₀.ne'] at hlog
  have hx := ha.trans (hab.trans hbx)
  have hpow := rpow_le_rpow hv₀.le (hv.2.trans hbx) hB
  have hl₂ : log 2 ≤ 1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hp : Real.pi^2 ≤ 16 := by nlinarith only [sq_le_sq' (by linarith [Real.pi_pos] : -(4:ℝ) ≤ Real.pi) Real.pi_lt_four.le]
  have hcost : (log v-log a)*(8*((0:ℝ)+1)^2) + (8+2*log 2)/2 ≤ 13 := by linarith only [hl₂,hlog]
  have hscaled := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 2*v^B by positivity)
  have hC : 0 ≤ log (2*Real.pi) := log_nonneg (by linarith only [Real.pi_gt_three])
  have hC₁ : log (2*Real.pi) ≤ 7 := by linarith only [Real.pi_lt_four,log_le_sub_one_of_pos (by positivity : 0 < 2*Real.pi)]
  have hΔ := log_le_log ha₀ hv.1
  have heq : primePrimitiveDeficit v-primePrimitiveDeficit a =
      QuasiRHPrimeWindowBounds.primeError v-QuasiRHPrimeWindowBounds.primeError a+
      log (2*Real.pi)*(log v-log a) := by
    unfold QuasiRHPrimeWindowBounds.primeError primePrimitiveDeficit; ring
  rw [heq]
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg (mul_nonneg hC (sub_nonneg.mpr hΔ))]
  nlinarith only [H,hscaled,hpow,hp,Real.one_le_rpow hx hB,
    mul_le_mul hC₁ (show log v-log a ≤ 1 by linarith) (sub_nonneg.mpr hΔ) (by norm_num : (0:ℝ) ≤ 7)]

/-- Smoothing the doubling interval keeps the *exact* zero exponent, without
logarithmic loss, on every individual ordinary-prime band. -/
theorem fixedBand_abs_of_zero_bound {B : ℝ} (hB : 1/2 ≤ B)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 4 ≤ x → |dyadicPrimeDeficit x| ≤ C*x^B := by
  obtain ⟨K,hK,hpow⟩ := dyadicPrimeDeficit_power_cost
  refine ⟨160+K,by positivity,fun x hx => ?_⟩
  have hx₀ : 0 < x := by linarith
  have hc := normalized_step (x := x) (by linarith : 1 ≤ x/2) (by linarith : x/2 ≤ x)
    (by linarith) le_rfl (by linarith) hz
  have hd := normalized_step (x := x) (by linarith : 1 ≤ x/4) (by linarith : x/4 ≤ x/2)
    (by linarith) (by linarith) (by linarith) hz
  have hsum : dyadicContrast x =
      2*((x/2)*(Deduction.G (x/2)/(x/2)-Deduction.G x/x)) -
      2*((x/4)*(Deduction.G (x/4)/(x/4)-Deduction.G (x/2)/(x/2))) := by
    unfold dyadicContrast; field_simp; ring
  have hs : |dyadicContrast x| ≤ 160*x^B := by
    rw [hsum]
    apply (abs_sub _ _).trans
    simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hc hd ⊢
    linarith
  have hh := hpow hx₀
  have hroot : Real.sqrt x ≤ x^B := by rw [sqrt_eq_rpow]; exact rpow_le_rpow_of_exponent_le (by linarith) hB
  apply abs_le.mpr
  constructor <;> nlinarith only [(abs_le.mp hs).1,(abs_le.mp hs).2,hh.1,hh.2,
    mul_le_mul_of_nonneg_left hroot hK,mul_nonneg hK (Real.rpow_nonneg hx₀.le B)]

theorem fixedBand_seven_eighths :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 4 ≤ x → |dyadicPrimeDeficit x| ≤ C*x^(7/8:ℝ) :=
  fixedBand_abs_of_zero_bound (by norm_num) suzukiLocalZero_re_le_seven_eighths

/-- The full positive mass bound at an arbitrary zero exponent. -/
theorem fixedBandMass_upper_of_zero_bound {B : ℝ} (hB : 1/2 ≤ B)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m b : ℕ}, 2 ≤ m →
      fixedBandMass m b ≤ C*(b:ℝ)^(4*B-2)*(1+log b) := by
  obtain ⟨C,hC,h⟩ := fixedBand_abs_of_zero_bound hB hz
  refine ⟨C,hC,fun {m b} hm => ?_⟩
  have hi := harmonic_le_one_add_log b
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at hi
  calc
    _ ≤ ∑ n ∈ Finset.Icc m b, (C*(b:ℝ)^(4*B-2))*(n:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn2 : (2:ℝ) ≤ n := by exact_mod_cast (hm.trans (Finset.mem_Icc.mp hn).1)
      have hn₀ : 0 < (n:ℝ) := by linarith
      have hs := h ((n:ℝ)^4) (by linarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hn2 4])
      have hp := Real.rpow_le_rpow hn₀.le (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2 : (n:ℝ) ≤ b)
        (show 0 ≤ 4*B-2 by linarith)
      have hscale : ((n:ℝ)^4)^B/(n:ℝ)^3=(n:ℝ)^(4*B-2)*(n:ℝ)⁻¹ := by
        rw [← Real.rpow_natCast_mul hn₀.le,Real.rpow_sub hn₀,Real.rpow_two]
        norm_num only [Nat.cast_ofNat]
        field_simp
      unfold fixedBandSample
      calc
        _ ≤ C*((n:ℝ)^4)^B/(n:ℝ)^3 := div_le_div_of_nonneg_right
          (max_le ((le_abs_self _).trans hs) (by positivity)) (by positivity)
        _ = (C*(n:ℝ)^(4*B-2))*(n:ℝ)⁻¹ := by rw [mul_div_assoc,hscale]; ring
        _ ≤ _ := by gcongr
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_left (show 1 ≤ m by omega)) (fun n _ _ => inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) n))).trans hi) (by positivity)

/-- Every mass exponent above 4B−2 is already paid on all sufficiently late
windows of a suitable fixed positive width. -/
theorem fixedBandMass_eventually_le_of_zero_bound {B α : ℝ} (hB : 1/2 ≤ B)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) (hα : 4*B-2 < α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ᶠ m : ℕ in atTop,
      fixedBandMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α := by
  obtain ⟨C,hC,h⟩ := fixedBandMass_upper_of_zero_bound hB hz
  let S := 4*B-2
  have hS : 0 ≤ S := by dsimp [S]; linarith
  have hgap : 0 < α-S := by dsimp [S]; linarith
  let δ := min 1 ((α-S)/(2*(1+S)))
  have hδ : 0 < δ := lt_min one_pos (div_pos hgap (by linarith))
  have hδ₁ : δ ≤ 1 := min_le_left _ _
  have hδS := (le_div_iff₀ (show 0 < 2*(1+S) by linarith)).mp (min_le_right 1 ((α-S)/(2*(1+S))))
  change δ*(2*(1+S)) ≤ α-S at hδS
  let e := (α-(1+δ)*S)/2
  have he : 0 < e := by dsimp [e]; nlinarith only [hδS,hgap,hδ]
  let K := C*(2:ℝ)^S*(2+2/e)
  obtain ⟨T,hT⟩ := eventually_atTop.mp ((tendsto_rpow_atTop he).eventually_ge_atTop K)
  refine ⟨δ,hδ,hδ₁,?_⟩
  filter_upwards [eventually_ge_atTop (max 2 ⌈T⌉₊)] with m hm
  have hm2 : 2 ≤ m := by omega
  have hmR : 1 ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hm₀ := zero_lt_one.trans_le hmR
  let b := ⌈(m:ℝ)^(1+δ)⌉₊
  let y := (m:ℝ)^(1+δ)
  have hy : 1 ≤ y := Real.one_le_rpow hmR (by linarith)
  have hb : (b:ℝ) ≤ 2*y := by
    have ht := Nat.ceil_lt_add_one (show 0 ≤ y by linarith)
    change (b:ℝ) < y+1 at ht
    linarith
  have hb₀ : 0 < (b:ℝ) := (zero_lt_one.trans_le hy).trans_le (Nat.le_ceil y)
  have hpow := Real.rpow_le_rpow hb₀.le hb hS
  dsimp only [y] at hpow
  rw [Real.mul_rpow (by norm_num) (by positivity),← Real.rpow_mul hm₀.le] at hpow
  have hl := Real.log_le_log hb₀ hb
  dsimp only [y] at hl
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_rpow hm₀] at hl
  have hlog : 1+log b ≤ (2+2/e)*(m:ℝ)^e := by
    have hh := Real.log_le_rpow_div hm₀.le he
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have hr := Real.one_le_rpow hmR he.le
    rw [show (2+2/e)*(m:ℝ)^e = 2*(m:ℝ)^e+2*((m:ℝ)^e/e) by ring]
    nlinarith only [hh,h2,hl,hr,mul_le_mul_of_nonneg_right hδ₁ (Real.log_nonneg hmR)]
  have hK := hT (m:ℝ) (Nat.ceil_le.mp ((le_max_right _ _).trans hm))
  apply (h (b := b) hm2).trans
  change C*(b:ℝ)^S*(1+log b) ≤ _
  calc
    _ ≤ C*((2:ℝ)^S*(m:ℝ)^((1+δ)*S))*((2+2/e)*(m:ℝ)^e) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) hlog (by positivity [log_natCast_nonneg b]) (by positivity)
    _ = K*((m:ℝ)^((1+δ)*S)*(m:ℝ)^e) := by dsimp [K]; ring
    _ ≤ (m:ℝ)^e*((m:ℝ)^((1+δ)*S)*(m:ℝ)^e) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = _ := by rw [← rpow_add hm₀,← rpow_add hm₀]; congr 1; dsimp [e]; ring

/-- Under RH the raw positive mass on any window is only logarithmic in its last index. -/
theorem fixedBandMass_le_log_of_rh (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m b : ℕ}, 2 ≤ m → fixedBandMass m b ≤ C*(1+log b) := by
  obtain ⟨C,hC,h⟩ := fixedBandMass_upper_of_zero_bound (B := 1/2) le_rfl
    (fun ρ => (hRH ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2).le)
  refine ⟨C,hC,fun {m b} hm => ?_⟩
  simpa only [show 4*(1/2:ℝ)-2 = 0 by norm_num, Real.rpow_zero, mul_one] using h (b := b) hm

/-- The core implication has a converse without importing the principal RH proof. -/
theorem rh_iff_fixedBandMass : RiemannHypothesis ↔
    ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α := by
  refine ⟨fun hr α hα => ?_,rh_of_fixedBandMass_powerWindows⟩
  obtain ⟨δ,hδ,hδ₁,hw⟩ := fixedBandMass_eventually_le_of_zero_bound (B := 1/2) le_rfl
    (fun ρ => (hr ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2).le) (by linarith : 4*(1/2:ℝ)-2 < α)
  exact ⟨δ,hδ,hδ₁,fun A => ((eventually_ge_atTop A).and hw).exists⟩

/-- Subpower slack above the threshold 4B−2 characterizes the entire zero half-plane. -/
theorem zero_bound_iff_fixedBandMass {B : ℝ} (hB : 1/2 ≤ B) :
    (∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) ↔
    ∀ α : ℝ, 4*B-2 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α := by
  constructor
  · intro hz α hα
    obtain ⟨δ,hδ,hδ₁,hw⟩ := fixedBandMass_eventually_le_of_zero_bound hB hz hα
    exact ⟨δ,hδ,hδ₁,fun A => ((eventually_ge_atTop A).and hw).exists⟩
  · intro h ρ
    by_contra! hρ
    let α := 2*(B+ρ.1.re)-2
    obtain ⟨δ,hδ,hδ₁,hw⟩ := h α (by dsimp [α]; linarith)
    exact zeta_ne_zero_of_fixedBandMass (by dsimp [α]; linarith) hδ hδ₁ hw
      (by dsimp [α]; linarith : 1/2+α/4 < ρ.1.re) ρ.2.1

/-- A single constant on arbitrarily late square windows gives an arithmetic criterion
with neither a variable width nor a variable exponent. -/
theorem rh_iff_fixedBandMass_log_squareWindows : RiemannHypothesis ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, fixedBandMass m (m^2) ≤ C*(1+2*log m) := by
  constructor
  · intro hr
    obtain ⟨C,hC,h⟩ := fixedBandMass_le_log_of_rh hr
    refine ⟨C,hC,fun A => ⟨max 2 A,le_max_right _ _,?_⟩⟩
    let m := max 2 A
    have hm := h (b := m^2) (le_max_left 2 A)
    have hpow : (((m^2 : ℕ) : ℝ)) = (m:ℝ)^2 := Nat.cast_pow m 2
    rw [hpow,Real.log_pow] at hm
    exact hm
  · exact rh_of_fixedBandMass_log_squareWindows

/-- A common arithmetic weight on integers and primes suffices on cofinal square windows. -/
theorem rh_iff_fixedBandIntegerMass_log_squareWindows : RiemannHypothesis ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, fixedBandIntegerMass m (m^2) ≤ C*(1+2*log m) := by
  rw [rh_iff_fixedBandMass_log_squareWindows]
  constructor <;> rintro ⟨C,hC,h⟩ <;> refine ⟨C+1,by positivity,fun A => ?_⟩ <;>
    obtain ⟨m,hm,hw⟩ := h (max 2 A) <;>
    have hm2 : 2 ≤ m := (le_max_left _ _).trans hm <;>
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  all_goals
    have he := abs_le.mp (fixedBandIntegerMass_error hm2 (Nat.le_self_pow (by norm_num : 2 ≠ 0) m))
    have hcost : 1/(m:ℝ)^2 ≤ 1 := div_le_self zero_le_one (one_le_pow₀ hm1)
    exact ⟨m,(le_max_right _ _).trans hm,by nlinarith only [he.1,he.2,hw,hcost,Real.log_nonneg hm1]⟩

end RiemannGaussian.AlpogeMined
end

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.fixedBand_abs_of_zero_bound,
      ``RiemannGaussian.AlpogeMined.fixedBand_seven_eighths,
      ``RiemannGaussian.AlpogeMined.fixedBandMass_le_log_of_rh,
      ``RiemannGaussian.AlpogeMined.fixedBandMass_eventually_le_of_zero_bound,
      ``RiemannGaussian.AlpogeMined.zero_bound_iff_fixedBandMass,
      ``RiemannGaussian.AlpogeMined.rh_iff_fixedBandMass_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.rh_iff_fixedBandIntegerMass_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.rh_iff_fixedBandMass] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"

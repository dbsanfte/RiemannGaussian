import RiemannGaussian.AlpogeZetaSampleBounds
import RiemannGaussian.DyadicPrimeSquareVariation

/-! # Bounds on the modulus-one ramp throughout real power windows -/

namespace RiemannGaussian.AlpogeZetaSamples
noncomputable section
open Finset Filter Set MeasureTheory DyadicPrime
open scoped ArithmeticFunction.vonMangoldt Interval

private def harmonicPrefix (x : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n/(n:ℝ)

private theorem ramp_eq {a : ℝ} (ha : 0 ≤ a) :
    ramp a = a*harmonicPrefix a - Chebyshev.psi a := by
  unfold ramp harmonicPrefix Chebyshev.psi
  rw [Nat.range_succ_eq_Icc_zero,← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
  simp only [show Λ 0 = 0 by simp,zero_mul,zero_add,Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0,hna⟩ := Finset.mem_Ioc.mp hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn0
  have hh : (n:ℝ) ≤ a := (Nat.le_floor_iff ha).mp hna
  rw [max_eq_left (sub_nonneg.mpr ((one_le_div hn').mpr hh))]
  ring

/-- The exact change of the normalized modulus-one ramp on an arbitrary real interval. -/
theorem G_normalized_increment {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    G a/a - G b/b = ∫ t in Ioc a b, (t-Chebyshev.psi t)/t^2 := by
  have hb := ha.trans_le hab
  have hd : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Icc a b) := by
    rw [deriv_inv']
    exact ((continuousOn_id.pow 2).inv₀ fun _ ht => pow_ne_zero _ (ha.trans_le ht.1).ne').neg.integrableOn_Icc
  have hsum := sum_mul_eq_sub_sub_integral_mul (fun k : ℕ => Λ k) ha.le hab
    (fun t ht => (hasDerivAt_inv (ha.trans_le ht.1).ne').differentiableAt) hd
  simp_rw [← Chebyshev.psi_eq_sum_Icc,deriv_inv'] at hsum
  have hh : harmonicPrefix b-harmonicPrefix a =
      ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (k:ℝ)⁻¹*Λ k := by
    have h := Finset.sum_Ioc_consecutive (fun k : ℕ => Λ k/(k:ℝ)) (Nat.zero_le ⌊a⌋₊) (Nat.floor_mono hab)
    unfold harmonicPrefix
    rw [← h,add_sub_cancel_left]
    simp_rw [div_eq_mul_inv,mul_comm (Λ _) (_:ℝ)⁻¹]
  rw [← hh] at hsum
  have hi := integrableOn_mul_sum_Icc (fun k : ℕ => Λ k) (m := 0) ha.le hd
  simp_rw [← Chebyshev.psi_eq_sum_Icc,deriv_inv'] at hi
  have hlog : (∫ t in Ioc a b, t⁻¹) = Real.log b-Real.log a := by
    rw [← intervalIntegral.integral_of_le hab,integral_inv_of_pos ha hb,Real.log_div hb.ne' ha.ne']
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc a b) :=
    continuousOn_id.inv₀ fun _ ht => (ha.trans_le ht.1).ne'
  have hker : (∫ t in Ioc a b, (t-Chebyshev.psi t)/t^2) =
      (Real.log b-Real.log a) + ∫ t in Ioc a b, -(t^2)⁻¹*Chebyshev.psi t := by
    rw [← hlog,← integral_add (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hi.mono_set Ioc_subset_Icc_self)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    field_simp [ne_of_gt (ha.trans ht.1)]
    ring
  rw [hker,G,G,ramp_eq ha.le,ramp_eq hb.le]
  linear_combination (norm := skip) -hsum
  field_simp
  ring

private def stepCost : ℝ := Real.log (2*Real.pi)*Real.log 2+1

private theorem stepCost_nonneg : 0 ≤ stepCost := by
  have hL := Real.log_nonneg (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three])
  dsimp [stepCost]
  positivity [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]

private theorem comparable_upper {B a b : ℝ} (hB : 0 ≤ B) (hB1 : B ≤ 1)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) (ha : 1 ≤ a) (hab : a ≤ b) (hba : b ≤ 2*a) :
    G a/a-G b/b ≤ stepCost*a^(B-1) := by
  have ha0 := zero_lt_one.trans_le ha
  obtain ⟨v,hv,he⟩ := exists_real_primitive_increment ha hab
  rw [G_normalized_increment ha0 hab,he,Real.rpow_sub_one ha0.ne',← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ ha0.le
  have hb := centered_increment_le_of_zero_bound ha hv.1 (hv.2.trans hba) hB hz
  have hlog := Real.log_le_log (ha0.trans_le hv.1) (hv.2.trans hba)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) ha0.ne'] at hlog
  have hL := Real.log_nonneg (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three])
  have hp : (2:ℝ)^B ≤ 2 := (Real.rpow_le_rpow_of_exponent_le (by norm_num) hB1).trans_eq (Real.rpow_one _)
  rw [Real.mul_rpow (by norm_num) ha0.le] at hb
  dsimp [stepCost]
  have hl2 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  nlinarith only [hb,mul_le_mul_of_nonneg_left (show Real.log v-Real.log a ≤ Real.log 2 by linarith) hL,
    mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg ha0.le B),
    mul_le_mul_of_nonneg_left (Real.one_le_rpow ha hB) (mul_nonneg hL hl2),Real.rpow_nonneg ha0.le B]

/-- A cofinal supply of actual nonpositive observations fixes the integration constant. An
all-height zero half-plane then bounds the original ramp at every real cutoff. -/
theorem G_upper_of_cofinal_nonpositive {B : ℝ} (hB : 0 ≤ B) (hB1 : B < 1)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) (hneg : ∀ A : ℝ, ∃ b ≥ A, G b ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 1 ≤ a → G a ≤ C*a^B := by
  let q := (2:ℝ)^(B-1)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨stepCost*(1-q)⁻¹,mul_nonneg stepCost_nonneg (inv_nonneg.mpr (by linarith)),fun a ha => ?_⟩
  have ha0 := zero_lt_one.trans_le ha
  obtain ⟨b,hab,hb⟩ := hneg a
  have hb0 := ha0.trans_le hab
  obtain ⟨j,hj,hend⟩ := exists_nat_pow_near ((one_le_div ha0).mpr hab) (by norm_num : (1:ℝ) < 2)
  let z (i : ℕ) := (2:ℝ)^i*a
  let K := stepCost*a^(B-1)
  have hK : 0 ≤ K := mul_nonneg stepCost_nonneg (Real.rpow_nonneg ha0.le _)
  have hbase (i : ℕ) : 1 ≤ z i := ha.trans (le_mul_of_one_le_left ha0.le (one_le_pow₀ (by norm_num) (n := i)))
  have hsucc (i : ℕ) : z (i+1) = 2*z i := by dsimp [z]; rw [pow_succ]; ring
  have hstep (i : ℕ) {y : ℝ} (hlo : z i ≤ y) (hhi : y ≤ 2*z i) :
      G (z i)/z i-G y/y ≤ K*q^i := by
    apply (comparable_upper hB hB1.le hz (hbase i) hlo hhi).trans_eq
    dsimp [z,q,K]
    rw [Real.mul_rpow (by positivity) ha0.le,← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
      mul_comm (i:ℝ) (B-1), Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
    ring
  have hind (i : ℕ) : G a/a-G (z i)/z i ≤ K*∑ n ∈ Finset.range i, q^n := by
    induction i with
    | zero => simp [z]
    | succ i ih =>
      have hh := hstep i (y := z (i+1)) (by rw [hsucc]; linarith [hbase i]) (hsucc i).le
      rw [Finset.sum_range_succ,mul_add]
      linarith
  have hlo : z j ≤ b := (le_div_iff₀ ha0).mp hj
  have hhi : b ≤ 2*z j := (hsucc j) ▸ ((div_lt_iff₀ ha0).mp hend).le
  have hh := hstep j hlo hhi
  have hsum := (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum (Finset.range (j+1))
    (fun n _ => pow_nonneg hq0 n)
  rw [tsum_geometric_of_lt_one hq0 hq1,Finset.sum_range_succ] at hsum
  have hfinal : G a/a ≤ K*(1-q)⁻¹ := by
    nlinarith only [hind j,hh,div_nonpos_of_nonpos_of_nonneg hb hb0.le,mul_le_mul_of_nonneg_left hsum hK]
  apply ((div_le_iff₀ ha0).mp hfinal).trans_eq
  dsimp [K]
  rw [Real.rpow_sub_one ha0.ne']
  field_simp

/-- The explicit formula bounds increments of the centered logarithmic prime primitive
on a dyadic interval under any all-height zero bound. -/
theorem primeError_increment_le_of_zero_bound {a v B : ℝ} (ha : 1 ≤ a) (hav : a ≤ v) (hva : v ≤ 2*a)
    (hB : 0 ≤ B) (hB1 : B ≤ 1) (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) :
    |QuasiRHPrimeWindowBounds.primeError v-QuasiRHPrimeWindowBounds.primeError a| ≤
      Real.pi^2/12 + 72*((v-a+1)/a)*a^B*(1+Real.log a/Real.log 2)^2 := by
  have ha0 := zero_lt_one.trans_le ha
  obtain ⟨J,hlo,hhi⟩ := exists_nat_pow_near ha (by norm_num : (1:ℝ) < 2)
  let T : ℝ := 2^(J+1)
  let L : ℝ := 1+Real.log a/Real.log 2
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hL : 1 ≤ L := by dsimp [L]; linarith [div_nonneg (Real.log_nonneg ha) hl2.le]
  have hJ : (J:ℝ)+1 ≤ L := by
    have hl := Real.log_le_log (by positivity : 0 < (2:ℝ)^J) hlo
    rw [Real.log_pow] at hl
    dsimp [L]
    linarith [(le_div_iff₀ hl2).mpr hl]
  have ht : Real.log T ≤ L := by
    dsimp [T]
    rw [Real.log_pow,Nat.cast_succ]
    nlinarith only [hJ,mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2))
      (show 0 ≤ (J:ℝ)+1 by positivity)]
  have htail : (8+2*Real.log T)/T ≤ 10*L^2/a := by
    calc _ ≤ 10*L^2/T := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (L-1)]) (by dsimp [T]; positivity)
         _ ≤ _ := div_le_div_of_nonneg_left (by positivity) ha0 hhi.le
  have hlog := Real.log_le_sub_one_of_pos (div_pos (ha0.trans_le hav) ha0)
  rw [Real.log_div (ha0.trans_le hav).ne' ha0.ne'] at hlog
  have hgap : Real.log v-Real.log a ≤ (v-a)/a := by rwa [sub_div,div_self ha0.ne']
  have hlow := mul_le_mul hgap (show 8*((J:ℝ)+1)^2 ≤ 8*L^2 by
    nlinarith [sq_le_sq' (by linarith : -L ≤ (J:ℝ)+1) hJ]) (by positivity) (div_nonneg (sub_nonneg.mpr hav) ha0.le)
  have hsum := add_le_add hlow htail
  have hv : v^B ≤ 2*a^B := by
    calc _ ≤ (2*a)^B := Real.rpow_le_rpow (ha0.le.trans hav) hva hB
         _ = (2:ℝ)^B*a^B := Real.mul_rpow (by norm_num) ha0.le
         _ ≤ _ := mul_le_mul_of_nonneg_right ((Real.rpow_le_rpow_of_exponent_le (by norm_num) hB1).trans_eq
           (Real.rpow_one _)) (Real.rpow_nonneg ha0.le _)
  have hh := primeError_dyadic_variation_of_re_le hB hz ha hav J
  have hcost : 0 ≤ (v-a)/a*(8*L^2)+10*L^2/a := by positivity [sub_nonneg.mpr hav]
  apply hh.trans
  apply add_le_add_right
  change _ ≤ 72*((v-a+1)/a)*a^B*L^2
  calc
    _ ≤ (2*v^B)*((v-a)/a*(8*L^2)+10*L^2/a) := mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) (Real.rpow_nonneg (ha0.le.trans hav) _))
    _ ≤ (4*a^B)*((v-a)/a*(8*L^2)+10*L^2/a) :=
      mul_le_mul_of_nonneg_right (by linarith only [hv]) hcost
    _ ≤ _ := by
      field_simp
      linarith only [hav]

/-- A sufficiently deep negative observation controls the whole following short interval.
The required depth uses the actual zero half-plane and the requested interval length. -/
theorem negative_interval_of_sample {B α θ : ℝ} (hB : 0 ≤ B) (hB1 : B ≤ 1)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hθ : 0 ≤ θ) (hgap : B+α-1 < θ) :
    ∃ C : ℝ, ∀ᶠ a : ℝ in atTop, G a < -(C*a^θ) → ∀ y ∈ Icc a (a+a^α), G y < 0 := by
  let s := θ-(B+α-1)
  let D := 1+1/Real.log 2
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨Real.pi^2/12+144*D^2,?_⟩
  have hlog := (isLittleO_log_rpow_rpow_atTop 2 (show 0 < s from sub_pos.mpr hgap)).bound (by norm_num : (0:ℝ) < 1)
  filter_upwards [hlog,Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1:ℝ)]
    with a hla hlog1 ha hg y hy
  have ha0 := zero_lt_one.trans_le ha
  have hy0 := ha0.trans_le hy.1
  have hla' : (Real.log a)^2 ≤ a^s := by
    simpa only [Real.rpow_two,Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg ha0.le _),one_mul] using hla
  have hl : 1+Real.log a/Real.log 2 ≤ D*Real.log a := by
    calc _ ≤ Real.log a+Real.log a/Real.log 2 := by linarith
         _ = _ := by dsimp [D]; ring
  have hsq : (1+Real.log a/Real.log 2)^2 ≤ D^2*a^s := by
    calc _ ≤ (D*Real.log a)^2 := pow_le_pow_left₀ (by positivity [Real.log_nonneg ha]) hl _
         _ = D^2*(Real.log a)^2 := mul_pow _ _ _
         _ ≤ _ := mul_le_mul_of_nonneg_left hla' (sq_nonneg _)
  have hpa := Real.one_le_rpow ha hα
  have hpa' : a^α ≤ a := (Real.rpow_le_rpow_of_exponent_le ha hα1).trans_eq (Real.rpow_one _)
  obtain ⟨v,hv,he⟩ := exists_real_primitive_increment ha hy.1
  have hbound := primeError_increment_le_of_zero_bound ha hv.1 (by linarith [hv.2,hy.2]) hB hB1 hz
  have hnum : v-a+1 ≤ 2*a^α := by linarith [hv.2,hy.2]
  have hc : 72*((v-a+1)/a)*a^B*(1+Real.log a/Real.log 2)^2 ≤
      72*((2*a^α)/a)*a^B*(D^2*a^s) := by
    apply mul_le_mul _ hsq (sq_nonneg _) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ha0.le B)
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum ha0.le) (by norm_num)
  have heq : 72*((2*a^α)/a)*a^B*(D^2*a^s) = 144*D^2*a^θ := by
    calc _ = 144*D^2*((a^α/a)*a^B*a^s) := by ring
         _ = _ := by rw [← Real.rpow_sub_one ha0.ne',← Real.rpow_add ha0,← Real.rpow_add ha0,
           show α-1+B+s = θ by dsimp [s]; ring]
  rw [heq] at hc
  have hneg : G a < QuasiRHPrimeWindowBounds.primeError v-QuasiRHPrimeWindowBounds.primeError a := by
    nlinarith only [hg,(abs_le.mp hbound).1,hc,mul_le_mul_of_nonneg_left (Real.one_le_rpow ha hθ)
      (by positivity : 0 ≤ Real.pi^2/12)]
  have hL := Real.log_nonneg (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three])
  have hh : G a < primePrimitiveDeficit v-primePrimitiveDeficit a := by
    unfold primePrimitiveDeficit QuasiRHPrimeWindowBounds.primeError at *
    linarith [mul_le_mul_of_nonneg_left (Real.log_le_log ha0 hv.1) hL]
  rw [← G_normalized_increment ha0 hy.1] at he
  have hgy : G y/y < 0 := by linarith [div_lt_div_of_pos_right hh ha0]
  simpa using (div_lt_iff₀ hy0).mp hgy

end
end RiemannGaussian.AlpogeZetaSamples

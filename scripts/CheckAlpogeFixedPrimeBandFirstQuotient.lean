import CheckAlpogeFixedPrimeBandCentered

/-! # Removing the first quotient block from the linear Möbius tail

A difference of lattice weights has exactly zero complete Möbius sum and
decays like the reciprocal of its argument. A weighted integral of its
dilates matches the centered kernel throughout the first quotient block.
-/

noncomputable section
namespace RiemannGaussian.AlpogeMined
open Real Finset MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius

private def latticeDifference (y : ℝ) := fixedBandLattice y-2*fixedBandLattice (y/2)

private theorem latticeDifference_decay {y : ℝ} (hy : 0 < y) :
    |latticeDifference y| ≤ 300/y := by
  have he : latticeDifference y = (fixedBandLattice y-fixedBandMain y)-
      2*(fixedBandLattice (y/2)-fixedBandMain (y/2)) := by
    dsimp [latticeDifference,fixedBandMain]; ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h := add_le_add (fixedBandLattice_error_inv hy)
    (mul_le_mul_of_nonneg_left (fixedBandLattice_error_inv (half_pos hy)) (by norm_num : (0:ℝ) ≤ 2))
  exact h.trans_eq (by ring)

private theorem latticeDifference_first {y : ℝ} (hy : 0 ≤ y) (h2 : y ≤ 2) :
    latticeDifference y = max (y-1) 0 := by
  rw [latticeDifference,fixedBandLattice_first hy h2,
    fixedBandLattice_first (by positivity : 0 ≤ y/2) (by linarith),max_eq_right (by linarith : y/2-1 ≤ 0)]
  ring

private theorem latticeDifference_zero {x : ℝ} {N : ℕ} (hx : 8 ≤ x) (hN : x ≤ N) :
    (∑ d ∈ Ioc 0 N, (μ d:ℝ)*latticeDifference (x/d)) = 0 := by
  simp only [latticeDifference,mul_sub,sum_sub_distrib,div_right_comm x (_:ℝ) 2,
    show ∀ d : ℕ, (μ d:ℝ)*(2*fixedBandLattice (x/2/d)) = 2*((μ d:ℝ)*fixedBandLattice (x/2/d)) by intro d; ring,
    ← mul_sum,fixedBandLattice_moebius_zero (by linarith : 4 ≤ x) hN,
    fixedBandLattice_moebius_zero (by linarith : 4 ≤ x/2) (by linarith : x/2 ≤ N),mul_zero,sub_zero]

private theorem lattice_continuousOn (Y : ℝ) : ContinuousOn fixedBandLattice (Set.Icc 0 Y) := by
  have hr (a : ℝ) (ha : 1 ≤ a) :
      ContinuousOn (fun y => fixedBandUnitRamp (y/a)) (Set.Icc 0 Y) := by
    apply (continuousOn_finsetSum (Ioc (0:ℕ) ⌊Y⌋₊) (f := fun (k:ℕ) (y:ℝ) => max (y/a/k-1) 0)
      (fun _ _ => by fun_prop)).congr
    intro y hy
    exact (fixedBandUnitRamp_sum (div_nonneg hy.1 (by linarith))
      ((div_le_self hy.1 ha).trans hy.2)).symm
  apply ((hr 1 le_rfl).sub ((continuousOn_const (c := (3:ℝ))).mul (hr 2 (by norm_num))) |>.add
    ((continuousOn_const (c := (2:ℝ))).mul (hr 4 (by norm_num)))).congr
  intro y hy
  simp [fixedBandLattice_ramps hy.1]

private def integrand (y t : ℝ) := (1+1/t)*latticeDifference (y/t)

private theorem integrand_continuous {y : ℝ} (hy : 0 ≤ y) :
    ContinuousOn (integrand y) (Set.Icc 1 2) := by
  have hc (a : ℝ) (ha : 1 ≤ a) :
      ContinuousOn (fun t : ℝ => fixedBandLattice (y/t/a)) (Set.Icc 1 2) := by
    apply (lattice_continuousOn y).comp ?_ ?_
    · exact ((continuousOn_const.div continuousOn_id fun t ht => by have := ht.1; dsimp; linarith).div_const a)
    · intro t ht
      have ht₀ : 0 ≤ t := zero_le_one.trans ht.1
      exact ⟨by positivity,(div_le_self (div_nonneg hy ht₀) ha).trans (div_le_self hy ht.1)⟩
  have hw : ContinuousOn (fun t : ℝ => 1+1/t) (Set.Icc 1 2) :=
    continuousOn_const.add (continuousOn_const.div continuousOn_id fun t ht => by have := ht.1; dsimp; linarith)
  change ContinuousOn (fun t : ℝ => (1+1/t)*(fixedBandLattice (y/t)-2*fixedBandLattice (y/t/2))) _
  apply (hw.mul ((hc 1 le_rfl).sub ((continuousOn_const (c := (2:ℝ))).mul (hc 2 (by norm_num))))).congr
  intro t _
  simp only [Pi.mul_apply,Pi.sub_apply,div_one]

/-- This correction agrees with the centered kernel on [1,2] and its complete
Möbius sum vanishes at all integer scales N ≥ 16. -/
def fixedBandFirstCorrection (y : ℝ) : ℝ :=
  (1-eulerMascheroniConstant)*latticeDifference y - ∫ t in (1:ℝ)..2, integrand y t

theorem fixedBandFirstCorrection_decay {y : ℝ} (hy : 0 < y) :
    |fixedBandFirstCorrection y| ≤ 1500/y := by
  have hw : |1-eulerMascheroniConstant| ≤ 1 := abs_le.mpr
    ⟨by linarith only [eulerMascheroniConstant_lt_two_thirds],by linarith only [one_half_lt_eulerMascheroniConstant]⟩
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1:ℝ)) (b := 2)
    (f := integrand y) (C := 1200/y) (by
      intro t ht
      rw [Set.uIoc_of_le (by norm_num)] at ht
      have h1 := ht.1.le
      have h2 := ht.2
      have ht₀ := zero_lt_one.trans ht.1
      rw [Real.norm_eq_abs,integrand,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1+1/t)]
      have hwt : 1+1/t ≤ 2 := by have := (div_le_one ht₀).mpr h1; linarith
      apply (mul_le_mul hwt (latticeDifference_decay (div_pos hy ht₀)) (abs_nonneg _) (by norm_num)).trans
      calc
        _ = (600/y)*t := by field_simp; ring
        _ ≤ (600/y)*2 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring)
  rw [Real.norm_eq_abs] at hi
  norm_num at hi
  rw [fixedBandFirstCorrection]
  apply (abs_sub _ _).trans
  rw [abs_mul]
  have hh := add_le_add (mul_le_mul hw (latticeDifference_decay hy) (abs_nonneg _) (by norm_num)) hi
  exact hh.trans_eq (by ring)

theorem fixedBandFirstCorrection_zero {N : ℕ} (hN : 16 ≤ N) :
    (∑ d ∈ Ioc 0 N, (μ d:ℝ)*fixedBandFirstCorrection ((N:ℝ)/d)) = 0 := by
  have hR : (16:ℝ) ≤ N := by exact_mod_cast hN
  let S := Ioc 0 N
  let f (d : ℕ) (t : ℝ) := (μ d:ℝ)*integrand ((N:ℝ)/d) t
  have hi (d : ℕ) (_ : d ∈ S) : IntervalIntegrable (f d) volume 1 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    exact continuousOn_const.mul (integrand_continuous (by positivity))
  have hz (t : ℝ) (ht : t ∈ Set.uIcc 1 2) : (∑ d ∈ S, f d t) = 0 := by
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have ht₀ := zero_lt_one.trans_le ht.1
    have hlo : 8 ≤ (N:ℝ)/t := (le_div_iff₀ ht₀).mpr (by linarith [ht.2])
    have he := latticeDifference_zero hlo (div_le_self (Nat.cast_nonneg N) ht.1)
    calc
      _ = (1+1/t)*∑ d ∈ S, (μ d:ℝ)*latticeDifference (((N:ℝ)/t)/d) := by
        rw [mul_sum]; apply sum_congr rfl; intro d _
        dsimp only [f,integrand]; rw [div_right_comm]; ring
      _ = 0 := by rw [show (∑ d ∈ S, (μ d:ℝ)*latticeDifference (((N:ℝ)/t)/d)) = 0 from he,mul_zero]
  calc
    _ = (1-eulerMascheroniConstant)*(∑ d ∈ S, (μ d:ℝ)*latticeDifference ((N:ℝ)/d)) -
        ∑ d ∈ S, ∫ t in (1:ℝ)..2, f d t := by
      rw [mul_sum,← sum_sub_distrib]
      apply sum_congr rfl; intro d _
      dsimp only [f,fixedBandFirstCorrection]
      rw [intervalIntegral.integral_const_mul]; ring
    _ = 0 := by
      rw [show (∑ d ∈ S, (μ d:ℝ)*latticeDifference ((N:ℝ)/d))=0 from
        latticeDifference_zero (by linarith) le_rfl,← intervalIntegral.integral_finsetSum hi,
        intervalIntegral.integral_congr hz,intervalIntegral.integral_zero,mul_zero,sub_zero]

private def rampPrimitive (y t : ℝ) := (y-1)*log t-y/t-t

private theorem rampPrimitive_deriv (y : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (rampPrimitive y) ((1+1/t)*(y/t-1)) t := by
  unfold rampPrimitive
  convert (((Real.hasDerivAt_log ht.ne').const_mul (y-1)).sub
    ((hasDerivAt_const t y).div (hasDerivAt_id' t) ht.ne')).sub (hasDerivAt_id' t) using 1
  simp
  field_simp
  ring

theorem fixedBandFirstCorrection_first {y : ℝ} (h1 : 1 ≤ y) (h2 : y ≤ 2) :
    fixedBandFirstCorrection y = fixedBandCenteredKernel y := by
  let f := integrand y
  have hy := zero_lt_one.trans_le h1
  have cont := integrand_continuous hy.le
  have hi {a b : ℝ} (ha : 1 ≤ a) (hb : b ≤ 2) (hab : a ≤ b) :
      IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact cont.mono (Set.Icc_subset_Icc ha hb)
  have hi₁ := hi le_rfl h2 h1
  have hi₂ := hi h1 le_rfl h2
  have hz : (∫ t in y..2, f t) = 0 := by
    rw [← intervalIntegral.integral_zero (a := y) (b := 2) (E := ℝ)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le h2] at ht
    have ht₀ := hy.trans_le ht.1
    have hy₁ := (div_le_one ht₀).mpr ht.1
    dsimp only [f,integrand]
    rw [latticeDifference_first (by positivity) (by linarith),max_eq_right (by linarith : y/t-1 ≤ 0),mul_zero]
  have hv : (∫ t in (1:ℝ)..y, f t) = rampPrimitive y y-rampPrimitive y 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := rampPrimitive y) _ hi₁
    intro t ht
    rw [Set.uIcc_of_le h1] at ht
    have ht₀ := zero_lt_one.trans_le ht.1
    have hlo := (one_le_div ht₀).mpr ht.2
    have hhi := (div_le_self hy.le ht.1).trans h2
    change HasDerivAt (rampPrimitive y) ((1+1/t)*latticeDifference (y/t)) t
    rw [latticeDifference_first (by positivity) hhi,max_eq_left (by linarith)]
    exact rampPrimitive_deriv y ht₀
  rw [fixedBandFirstCorrection,fixedBandCenteredKernel_first h1 h2,
    latticeDifference_first hy.le h2,max_eq_left (by linarith)]
  change _ - (∫ t in (1:ℝ)..2, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂,hz,hv]
  simp only [rampPrimitive,log_one,mul_zero,div_one,div_self hy.ne']
  ring

private theorem unitRamp_through_three {y : ℝ} (hy : 0 ≤ y) (h₃ : y ≤ 3) :
    fixedBandUnitRamp y = max (y-1) 0 + max (y/2-1) 0 := by
  rw [← fixedBandUnitRamp_sum hy h₃]
  norm_num [show Ioc 0 (3:ℕ) = {1,2,3} by decide,max_eq_right (show y/3-1 ≤ 0 by linarith)]

private theorem lattice_through_three {y : ℝ} (hy : 0 ≤ y) (h₃ : y ≤ 3) :
    fixedBandLattice y = max (y-1) 0 - 2*max (y/2-1) 0 := by
  rw [fixedBandLattice_ramps hy,unitRamp_through_three hy h₃,
    unitRamp_through_three (by positivity : 0 ≤ y/2) (by linarith),
    unitRamp_through_three (by positivity : 0 ≤ y/4) (by linarith)]
  rw [max_eq_right (by linarith : y/2/2-1 ≤ 0),max_eq_right (by linarith : y/4-1 ≤ 0),
    max_eq_right (by linarith : y/4/2-1 ≤ 0)]
  ring

private theorem latticeDifference_through_three {y : ℝ} (hy : 0 ≤ y) (h₃ : y ≤ 3) :
    latticeDifference y = max (y-1) 0 - 4*max (y/2-1) 0 := by
  rw [latticeDifference,lattice_through_three hy h₃,
    fixedBandLattice_first (by positivity : 0 ≤ y/2) (by linarith)]
  ring

/-- On the next block the reweighted kernel still has a nonzero arithmetic
weight. In this formula the argument is twice the scale variable z. -/
theorem fixedBandHalfKernel_second {z : ℝ} (h1 : 1 ≤ z) (h₃ : 2*z ≤ 3) :
    fixedBandCenteredKernel (2*z)-fixedBandFirstCorrection (2*z) =
      (z-1)*(2*(1-eulerMascheroniConstant)+4*log 2+1)+(3-4*z)*log z := by
  have hz := zero_lt_one.trans_le h1
  let y := 2*z
  have hy : 2 ≤ y := by dsimp [y]; linarith
  have hy₃ : y ≤ 3 := h₃
  let f (t : ℝ) := (1+1/t)*(y/t-1)
  have hf : IntervalIntegrable f volume 1 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    dsimp only [f]
    fun_prop (disch := intro x hx; have := hx.1; dsimp; linarith)
  have hi : IntervalIntegrable (integrand z) volume 1 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    exact integrand_continuous hz.le
  have he : (∫ t in (1:ℝ)..2, integrand y t) =
      (∫ t in (1:ℝ)..2, f t)-4*(∫ t in (1:ℝ)..2, integrand z t) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub hf (hi.const_mul 4)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have ht₀ := zero_lt_one.trans_le ht.1
    have y₀ : 0 ≤ y := by linarith
    have hlo := (one_le_div ht₀).mpr (ht.2.trans hy)
    have hhi := (div_le_self y₀ ht.1).trans hy₃
    have hz₂ : z/t ≤ 2 := (div_le_self hz.le ht.1).trans (by linarith)
    dsimp [integrand,f]
    rw [latticeDifference_through_three (by positivity) hhi,
      latticeDifference_first (by positivity) hz₂,max_eq_left (by linarith : 0 ≤ y/t-1)]
    rw [show y/t/2=z/t by dsimp [y]; ring]
    ring
  have hv : (∫ t in (1:ℝ)..2, f t) = rampPrimitive y 2 - rampPrimitive y 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hf
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have ht₀ := zero_lt_one.trans_le ht.1
    exact rampPrimitive_deriv y ht₀
  have hhalf : y/2=z := by dsimp [y]; ring
  have hj := fixedBandFirstCorrection_first h1 (by linarith : z ≤ 2)
  rw [fixedBandFirstCorrection,latticeDifference_first hz.le (by linarith),max_eq_left (by linarith),
    fixedBandCenteredKernel_first h1 (by linarith)] at hj
  have hF : fixedBandCenteredKernel y = log 2*(y-2)+1-eulerMascheroniConstant-log y := by
    rw [fixedBandCenteredKernel,unitRamp_through_three (by linarith) hy₃,hhalf,
      unitRamp_through_three hz.le (by linarith),lattice_through_three (by linarith) hy₃,hhalf,
      max_eq_left (by linarith : 0 ≤ y-1),max_eq_left (by linarith : 0 ≤ z-1),
      max_eq_right (by linarith : z/2-1 ≤ 0)]
    unfold fixedBandLogConstant
    dsimp only [y]
    ring
  change fixedBandCenteredKernel y-fixedBandFirstCorrection y = _
  rw [hF,fixedBandFirstCorrection,he,hv,latticeDifference_through_three (by linarith) hy₃,hhalf,
    max_eq_left (by linarith : 0 ≤ y-1),max_eq_left (by linarith : 0 ≤ z-1)]
  dsimp only [rampPrimitive,y]
  rw [log_mul (by norm_num) hz.ne',log_one]
  linarith only [hj]

/-- The first retained block already has weights bounded away from zero on
a fixed interval. Absolute estimates alone cannot exploit the Möbius signs there. -/
theorem fixedBandHalfKernel_second_lower {z : ℝ} (hlo : 9/8 ≤ z) (hhi : z ≤ 5/4) :
    1/5 ≤ fixedBandCenteredKernel (2*z)-fixedBandFirstCorrection (2*z) := by
  have hz : 1 ≤ z := by linarith
  rw [fixedBandHalfKernel_second hz (by linarith)]
  have hlog := log_le_sub_one_of_pos (zero_lt_one.trans_le hz)
  have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h₂
  have hprod := mul_le_mul_of_nonneg_left (show (5/3:ℝ) ≤ 2*(1-eulerMascheroniConstant)+4*log 2-1 by
    linarith only [eulerMascheroniConstant_lt_two_thirds,h₂]) (sub_nonneg.mpr hz)
  have hneg := mul_le_mul_of_nonneg_right (show (0:ℝ) ≤ (3-4*z)+2 by linarith) (log_nonneg hz)
  linarith only [hprod,hneg,hlog,hlo]

/-- After removing the first quotient block the signed linear tail needs only
indices up to half the original sample. -/
def fixedBandHalfTail (N K : ℕ) : ℝ :=
  ∑ d ∈ Ioc K (N/2), (μ d:ℝ)*(fixedBandCenteredKernel ((N:ℝ)/d)-fixedBandFirstCorrection ((N:ℝ)/d))

theorem fixedBandHalfTail_error {N K : ℕ} (hN : 16 ≤ N) (hK : K ≤ N) :
    |fixedBandCenteredTail N K-fixedBandHalfTail N K| ≤ 1500*(K:ℝ)^2/N := by
  let w (d : ℕ) := (μ d:ℝ)*fixedBandFirstCorrection ((N:ℝ)/d)
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hsub : fixedBandHalfTail N K = ∑ d ∈ Ioc K N,
      (μ d:ℝ)*(fixedBandCenteredKernel ((N:ℝ)/d)-fixedBandFirstCorrection ((N:ℝ)/d)) := by
    apply sum_subset (Ioc_subset_Ioc_right (Nat.div_le_self ..))
    intro d hd hd'
    have hdk := (mem_Ioc.mp hd).1
    have hdn := (mem_Ioc.mp hd).2
    have dh : N/2 < d := lt_of_not_ge (fun h => hd' (mem_Ioc.mpr ⟨hdk,h⟩))
    have hd₀ : 0 < (d:ℝ) := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt hdk)
    have hlo := (one_le_div hd₀).mpr (Nat.cast_le (α := ℝ).mpr hdn)
    have hhi := (div_le_iff₀ hd₀).mpr (show (N:ℝ) ≤ 2*d by exact_mod_cast (show N ≤ 2*d by omega))
    rw [fixedBandFirstCorrection_first hlo hhi,sub_self,mul_zero]
  have hsplit := sum_Ioc_consecutive w (Nat.zero_le K) hK
  change _ = ∑ d ∈ Ioc 0 N, (μ d:ℝ)*fixedBandFirstCorrection ((N:ℝ)/d) at hsplit
  rw [fixedBandFirstCorrection_zero hN] at hsplit
  have he : fixedBandCenteredTail N K-fixedBandHalfTail N K = -(∑ d ∈ Ioc 0 K, w d) := by
    rw [hsub,fixedBandCenteredTail]
    simp only [mul_sub,sum_sub_distrib,sub_sub_cancel]
    dsimp only [w] at hsplit ⊢
    linarith only [hsplit]
  rw [he,abs_neg]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    (∑ d ∈ Ioc 0 K, |w d|) ≤ ∑ _d ∈ Ioc 0 K, (1500:ℝ)*K/N := by
      apply sum_le_sum
      intro d hd
      have hd₀ := Nat.cast_pos (α := ℝ).mpr (mem_Ioc.mp hd).1
      change |(μ d:ℝ)*fixedBandFirstCorrection ((N:ℝ)/d)| ≤ _
      rw [abs_mul]
      apply (mul_le_of_le_one_left (abs_nonneg _) (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d))).trans
      apply (fixedBandFirstCorrection_decay (div_pos hn hd₀)).trans
      rw [div_div_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast (mem_Ioc.mp hd).2) (by norm_num)) hn.le
    _ = _ := by rw [sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul]; ring

private theorem multiples_in_interval (a L q : ℕ) (hq : 0 < q) :
    (((Ioc a (a+L)).filter (fun k => q ∣ k)).card:ℝ) ≤ (L:ℝ)/q+1 := by
  let S := (Ioc a (a+L)).filter fun k => q ∣ k
  have hc : S.card ≤ (Ioc (a/q) ((a+L)/q)).card := by
    apply card_le_card_of_injOn (fun k => k/q)
    · intro k hk
      obtain ⟨hI,hd⟩ := mem_filter.mp hk
      exact mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hq).mpr (by rw [Nat.div_mul_cancel hd]; exact (mem_Ioc.mp hI).1),
        Nat.div_le_div_right (mem_Ioc.mp hI).2⟩
    · intro i hi j hj he
      have h := congrArg (fun t => t*q) he
      simpa only [Nat.div_mul_cancel (mem_filter.mp hi).2,Nat.div_mul_cancel (mem_filter.mp hj).2] using h
  rw [Nat.card_Ioc,Nat.add_div hq] at hc
  have hcard : S.card ≤ L/q+1 := by
    apply hc.trans
    rw [Nat.add_assoc,Nat.add_sub_cancel_left]
    apply Nat.add_le_add_left
    split <;> decide
  have hquot : ((L/q:ℕ):ℝ) ≤ (L:ℝ)/q :=
    (le_div_iff₀ (Nat.cast_pos.mpr hq)).mpr (by exact_mod_cast Nat.div_mul_le_self L q)
  exact (show (S.card:ℝ) ≤ (L/q:ℕ)+1 by exact_mod_cast hcard).trans (by linarith)

private theorem squarefree_interval_lower (a L s : ℕ) (hs : 2 ≤ s) (hN : a+L ≤ s^2) :
    (L:ℝ)/4-s ≤ (((Ioc a (a+L)).filter Squarefree).card:ℝ) := by
  let S := Ioc a (a+L)
  let bad (d : ℕ) := S.filter fun k => d^2 ∣ k
  have hsub : S.filter (fun k => ¬Squarefree k) ⊆ (Ioc 1 s).biUnion bad := by
    intro k hk
    obtain ⟨hk,hn⟩ := mem_filter.mp hk
    rw [Nat.squarefree_iff_prime_squarefree] at hn
    push Not at hn
    obtain ⟨p,hp,hd⟩ := hn
    have hps : p*p ≤ s*s := (Nat.le_of_dvd ((Nat.zero_le _).trans_lt (mem_Ioc.mp hk).1) hd).trans
      ((mem_Ioc.mp hk).2.trans (by simpa [pow_two] using hN))
    exact mem_biUnion.mpr ⟨p,mem_Ioc.mpr ⟨hp.one_lt,Nat.mul_self_le_mul_self_iff.mp hps⟩,
      mem_filter.mpr ⟨hk,by simpa [pow_two] using hd⟩⟩
  have hc := (card_le_card hsub).trans card_biUnion_le
  have hrec : (∑ d ∈ Ioc 1 s, ((d:ℝ)^2)⁻¹) ≤ 3/4 := by
    rw [← sum_Ioc_consecutive (fun d : ℕ => ((d:ℝ)^2)⁻¹) (by decide : 1 ≤ 2) hs]
    have hb := sum_Ioc_inv_sq_le_sub (α := ℝ) (by decide : (2:ℕ) ≠ 0) hs
    norm_num [show Ioc (1:ℕ) 2 = {2} by decide] at hb ⊢
    linarith only [hb,inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) s)]
  have hbad : ((S.filter (fun k => ¬Squarefree k)).card:ℝ) ≤ (L:ℝ)*(3/4)+s := calc
    _ ≤ ∑ d ∈ Ioc 1 s, ((bad d).card:ℝ) := by exact_mod_cast hc
    _ ≤ ∑ d ∈ Ioc 1 s, ((L:ℝ)*((d:ℝ)^2)⁻¹+1) := by
      apply sum_le_sum
      intro d hd
      have hpos : 0 < d := (by decide : 0 ≤ 1).trans_lt (mem_Ioc.mp hd).1
      simpa [bad,S,div_eq_mul_inv] using multiples_in_interval a L (d^2) (pow_pos hpos _)
    _ ≤ _ := by
      rw [sum_add_distrib,← mul_sum,sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one]
      exact add_le_add (mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg L)) (Nat.cast_le.mpr (Nat.sub_le ..))
  have hh := card_filter_add_card_filter_not (s := S) Squarefree
  have hsize : S.card = L := by simp [S]
  rw [hsize] at hh
  have hr := congrArg (Nat.cast (R := ℝ)) hh
  push_cast at hr
  change _ ≤ ((S.filter Squarefree).card:ℝ)
  linarith only [hr,hbad]

/-- The absolute term sum on the same retained range as the signed half-tail. -/
def fixedBandHalfTailAbsolute (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc (fixedBandMultipleCutoff n) (n^4/2),
    |(μ d:ℝ)*(fixedBandCenteredKernel (((n^4:ℕ):ℝ)/d)-fixedBandFirstCorrection (((n^4:ℕ):ℝ)/d))|

/-- Even after removing half the linear tail, its unsigned sum grows at least as
fast as n⁴. The proof counts squarefree indices in the second quotient block. -/
theorem fixedBandHalfTail_absolute_lower {n : ℕ} (hn : 32 ≤ n) :
    (n:ℝ)^4/2000 ≤ fixedBandHalfTailAbsolute n := by
  let N := n^4
  let D := N/45
  let S := Ioc (19*D) (19*D+D)
  let a (d : ℕ) := (μ d:ℝ)*(fixedBandCenteredKernel ((N:ℝ)/d)-fixedBandFirstCorrection ((N:ℝ)/d))
  have h₁ : 32*n^3 ≤ N := by simpa [N,pow_succ n 3,mul_comm] using Nat.mul_le_mul_right (n^3) hn
  have hn₂ := Nat.pow_le_pow_left hn 2
  have h₂ : 1024*n^2 ≤ N := by
    calc
      _ ≤ n^2*n^2 := Nat.mul_le_mul_right _ hn₂
      _ = N := by dsimp [N]; ring
  have h₃ : 32^4 ≤ N := Nat.pow_le_pow_left hn 4
  have hD : D*45 ≤ N := Nat.div_mul_le_self ..
  have hD' : N < D*45+45 := Nat.lt_div_mul_add (by decide : 0 < 45)
  have hK : fixedBandMultipleCutoff n ≤ n^3 := Nat.div_le_self ..
  have hS (d : ℕ) (hd : d ∈ S) : 19*D < d ∧ d ≤ 20*D := by have := mem_Ioc.mp hd; omega
  have hsub : S.filter Squarefree ⊆ Ioc (fixedBandMultipleCutoff n) (N/2) := by
    intro d hd
    have := hS d (mem_filter.mp hd).1
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  have hpoint (d : ℕ) (hd : d ∈ S.filter Squarefree) : (1/5:ℝ) ≤ |a d| := by
    have hh := hS d (mem_filter.mp hd).1
    have hd₀ : 0 < (d:ℝ) := Nat.cast_pos.mpr (by omega)
    have h₉ : 9*(d:ℝ) ≤ 4*N := by exact_mod_cast (show 9*d ≤ 4*N by omega)
    have h₅ : 2*(N:ℝ) ≤ 5*d := by exact_mod_cast (show 2*N ≤ 5*d by omega)
    have hlow : (9/8:ℝ) ≤ (N:ℝ)/d/2 := by rw [le_div_iff₀ (by norm_num),le_div_iff₀ hd₀]; linarith
    have hhigh : (N:ℝ)/d/2 ≤ 5/4 := by rw [div_le_iff₀ (by norm_num),div_le_iff₀ hd₀]; linarith
    have h := fixedBandHalfKernel_second_lower hlow hhigh
    rw [show 2*((N:ℝ)/d/2) = (N:ℝ)/d by ring] at h
    have hmu : |(μ d:ℝ)| = 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree (mem_filter.mp hd).2
    dsimp only [a]
    rw [abs_mul,hmu,one_mul]
    exact h.trans (le_abs_self _)
  have hcount := squarefree_interval_lower (19*D) D (n^2) (by omega)
    (by rw [← pow_mul]; change 19*D+D ≤ N; omega)
  change _ ≤ ((S.filter Squarefree).card:ℝ) at hcount
  have hNcast : (N:ℝ) ≤ 45*D+45 := by exact_mod_cast (show N ≤ 45*D+45 by omega)
  have hbudget : 1024*((n:ℝ)^2) ≤ N := by exact_mod_cast h₂
  have hmin : (32:ℝ)^4 ≤ N := by exact_mod_cast h₃
  have hcost : (N:ℝ)/2000 ≤ ((S.filter Squarefree).card:ℝ)*(1/5) := by
    push_cast at hcount
    linarith only [hcount,hNcast,hbudget,hmin]
  calc
    (n:ℝ)^4/2000 = (N:ℝ)/2000 := by simp [N]
    _ ≤ ∑ _d ∈ S.filter Squarefree, (1/5:ℝ) := by simpa using hcost
    _ ≤ ∑ d ∈ S.filter Squarefree, |a d| := sum_le_sum hpoint
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => abs_nonneg (a d))

/-- Taking absolute values of the terms forces quartic growth on every
sufficiently late square window. -/
theorem fixedBandHalfTailAbsolute_window_lower {m : ℕ} (hm : 32 ≤ m) :
    (m:ℝ)^4/8000 ≤ ∑ n ∈ Icc m (m^2), fixedBandHalfTailAbsolute n/(n:ℝ)^3 := by
  let M := m^2
  have hmM : m ≤ M/2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    exact (Nat.mul_le_mul_left m (by omega : 2 ≤ m)).trans_eq (by simp [M,pow_two])
  have hsize : (M:ℝ)/2 ≤ ((Ioc (M/2) M).card:ℝ) := by
    rw [Nat.card_Ioc]
    have hh : M ≤ 2*(M-M/2) := by omega
    have hh' : (M:ℝ) ≤ 2*((M-M/2:ℕ):ℝ) := by exact_mod_cast hh
    linarith
  have hsub : Ioc (M/2) M ⊆ Icc m M := fun n hn =>
    mem_Icc.mpr ⟨hmM.trans (mem_Ioc.mp hn).1.le,(mem_Ioc.mp hn).2⟩
  calc
    (m:ℝ)^4/8000 = ((M:ℝ)/2)*((M:ℝ)/4000) := by dsimp [M]; push_cast; ring
    _ ≤ ∑ _n ∈ Ioc (M/2) M, (M:ℝ)/4000 := by
      rw [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hsize (by positivity)
    _ ≤ ∑ n ∈ Ioc (M/2) M, fixedBandHalfTailAbsolute n/(n:ℝ)^3 := by
      apply sum_le_sum
      intro n hn
      have hnm := (mem_Icc.mp (hsub hn)).1
      have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
      have hh : M ≤ 2*n := by have := (mem_Ioc.mp hn).1; omega
      have hh' : (M:ℝ) ≤ 2*n := by exact_mod_cast hh
      calc
        (M:ℝ)/4000 ≤ n/2000 := by linarith only [hh']
        _ = ((n:ℝ)^4/2000)/(n:ℝ)^3 := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right (fixedBandHalfTail_absolute_lower (hm.trans hnm)) (by positivity)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ =>
      div_nonneg (sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity))

/-- Only the signed positive-part window bound for the half-length tail remains. -/
def fixedBandHalfTailMass (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (fixedBandHalfTail (n^4) (fixedBandMultipleCutoff n)) 0/(n:ℝ)^3

theorem fixedBandHalfTailMass_error {m b : ℕ} (hm : 2 ≤ m) :
    |fixedBandCriticalTailMass m b-fixedBandHalfTailMass m b| ≤ 1500*(1+log b) := by
  apply fixedBand_mass_sqrt_error (by norm_num) _ hm
  intro n hn
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hK : fixedBandMultipleCutoff n ≤ n^3 := Nat.div_le_self ..
  have h₄ := (by decide : 16 ≤ 2^4).trans (Nat.pow_le_pow_left hn 4)
  have h₃ : n^3 ≤ n^4 := Nat.pow_le_pow_right (by omega) (by decide)
  apply (fixedBandHalfTail_error h₄ (hK.trans h₃)).trans
  rw [Nat.cast_pow]
  apply (div_le_iff₀ (pow_pos hnR 4)).mpr
  calc
    1500*(fixedBandMultipleCutoff n:ℝ)^2 ≤ 1500*((n:ℝ)^3)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hK) 2) (by norm_num)
    _ = _ := by ring

theorem fixedBandCriticalTail_iff_halfTail_log_squareWindows :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, fixedBandCriticalTailMass m (m^2) ≤ C*(1+2*log m)) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, fixedBandHalfTailMass m (m^2) ≤ C*(1+2*log m)) := by
  constructor <;> rintro ⟨C,hC,h⟩ <;> refine ⟨C+1500,by positivity,fun A => ?_⟩ <;>
    obtain ⟨m,hm,hw⟩ := h (max 2 A)
  all_goals
    have he := abs_le.mp (fixedBandHalfTailMass_error (b := m^2) ((le_max_left 2 A).trans hm))
    rw [Nat.cast_pow,log_pow,Nat.cast_ofNat] at he
    exact ⟨m,(le_max_right 2 A).trans hm,by linarith only [hw,he.1,he.2]⟩

theorem rh_of_fixedBandHalfTailMass_log_squareWindows
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, fixedBandHalfTailMass m (m^2) ≤ C*(1+2*log m)) :
    RiemannHypothesis :=
  rh_of_fixedBandCriticalTail_log_squareWindows (fixedBandCriticalTail_iff_halfTail_log_squareWindows.mpr h)

end RiemannGaussian.AlpogeMined
end

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.fixedBandFirstCorrection_zero,
      ``RiemannGaussian.AlpogeMined.fixedBandFirstCorrection_first,
      ``RiemannGaussian.AlpogeMined.fixedBandFirstCorrection_decay,
      ``RiemannGaussian.AlpogeMined.fixedBandHalfKernel_second_lower,
      ``RiemannGaussian.AlpogeMined.fixedBandHalfTail_absolute_lower,
      ``RiemannGaussian.AlpogeMined.fixedBandHalfTailAbsolute_window_lower,
      ``RiemannGaussian.AlpogeMined.fixedBandHalfTail_error,
      ``RiemannGaussian.AlpogeMined.fixedBandHalfTailMass_error,
      ``RiemannGaussian.AlpogeMined.fixedBandCriticalTail_iff_halfTail_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandHalfTailMass_log_squareWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"Half-tail implication uses {(← getEnv).header.moduleNames.size + 1} Lean modules including this module."

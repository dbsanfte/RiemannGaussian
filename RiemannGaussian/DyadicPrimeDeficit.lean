import RiemannGaussian.EtaMoebiusArithmeticGrowingHead
import RiemannGaussian.RosserSchoenfeldPrimePrimitive
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-! # A signed dyadic sum of prime powers and its exact primitive increment -/

namespace RiemannGaussian.DyadicPrime
noncomputable section
open Set MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Interval

/-- The shortfall in the weighted prime-power sum at an integer cutoff. -/
def dyadicPrimeError (n : ℕ) : ℝ :=
  n * (Real.log 2 - pairedEtaPrimeHarmonicShell n) +
    Chebyshev.psi n - 2 * Chebyshev.psi (n / 2 : ℕ)

/-- Prime powers through half the endpoint have full weight. The others taper to zero at the endpoint. -/
def weightedPrimeSum (n : ℕ) : ℝ :=
  Chebyshev.psi (n / 2 : ℕ) + ∑ k ∈ Finset.Ioc (n / 2) n, (((n : ℝ) / k - 1) * Λ k)

theorem dyadicPrimeError_eq_sub_weightedPrimeSum (n : ℕ) :
    dyadicPrimeError n = (n : ℝ) * Real.log 2 - weightedPrimeSum n := by
  have hsplit := Finset.sum_Ioc_consecutive (fun k : ℕ => Λ k) (Nat.zero_le (n/2)) (Nat.div_le_self n 2)
  have hpsi : Chebyshev.psi n = Chebyshev.psi (n / 2 : ℕ) + ∑ k ∈ Finset.Ioc (n/2) n, Λ k := by
    simpa only [Chebyshev.psi, Nat.floor_natCast] using hsplit.symm
  have hweighted : (∑ k ∈ Finset.Ioc (n/2) n, (((n : ℝ) / k - 1) * Λ k)) =
      n * (∑ k ∈ Finset.Ioc (n/2) n, Λ k / (k : ℝ)) - ∑ k ∈ Finset.Ioc (n/2) n, Λ k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [dyadicPrimeError, pairedEtaPrimeHarmonicShell_eq_sum_Ioc, weightedPrimeSum, hpsi, hweighted]
  ring

/-- The filtered sum is the signed Chebyshev deficit on one dyadic interval. -/
theorem dyadicPrimeError_eq_integral {n : ℕ} (hn : 0 < n) :
    dyadicPrimeError n = (n : ℝ) * ∫ t in Ioc ((n : ℝ) / 2) n, (t - Chebyshev.psi t) / t^2 := by
  let a := (n : ℝ) / 2
  let b := (n : ℝ)
  have hb : 0 < b := by dsimp [b]; exact_mod_cast hn
  have ha : 0 < a := by dsimp [a, b] at *; positivity
  have hab : a ≤ b := by change (n : ℝ) / 2 ≤ n; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ fun _ ht => (ha.trans_le ht.1).ne'
  have hder : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Icc a b) := by
    rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    exact ((continuousOn_id.pow 2).inv₀ (fun _ ht => pow_ne_zero _ (ha.trans_le ht.1).ne')).neg
  have he := sum_mul_eq_sub_sub_integral_mul (fun k : ℕ => Λ k) ha.le hab
    (fun t ht => (hasDerivAt_inv (ha.trans_le ht.1).ne').differentiableAt) hder
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at he
  have hfl : ⌊a⌋₊ = n / 2 := by simp [a, Nat.floor_div_ofNat]
  have hfr : ⌊b⌋₊ = n := Nat.floor_natCast n
  rw [hfl, hfr] at he
  have hs : ∑ k ∈ Finset.Ioc (n/2) n, (k : ℝ)⁻¹ * Λ k = pairedEtaPrimeHarmonicShell n := by
    rw [pairedEtaPrimeHarmonicShell_eq_sum_Ioc]
    simp only [div_eq_mul_inv, mul_comm]
  rw [hs, deriv_inv'] at he
  have hc := integrableOn_mul_sum_Icc (fun k : ℕ => Λ k) (m := 0) ha.le hder
  simp_rw [← Chebyshev.psi_eq_sum_Icc, deriv_inv'] at hc
  have hmeasure : IntegrableOn (fun t : ℝ => -(t^2)⁻¹ * Chebyshev.psi t) (Ioc a b) :=
    hc.mono_set Ioc_subset_Icc_self
  have hlog : (∫ t in Ioc a b, t⁻¹) = Real.log 2 := by
    rw [← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha hb]
    congr 1
    dsimp [a,b] at *
    field_simp
  have heq : (∫ t in Ioc a b, (t - Chebyshev.psi t) / t^2) =
      Real.log 2 + ∫ t in Ioc a b, -(t^2)⁻¹ * Chebyshev.psi t := by
    rw [← hlog, ← integral_add (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self) hmeasure]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    field_simp [ne_of_gt (ha.trans ht.1)]
    ring
  have hpsi : Chebyshev.psi a = Chebyshev.psi (n / 2 : ℕ) := by
    rw [Chebyshev.psi_eq_psi_coe_floor a, hfl]
  rw [show ((n : ℝ) / 2) = a from rfl, show (n : ℝ) = b from rfl, heq]
  rw [dyadicPrimeError, ← hpsi]
  have he' := congrArg (fun x : ℝ => b * x) he
  dsimp [a, b] at *
  field_simp at he' ⊢
  linarith

/-- The physical cutoff minus the logarithmically smoothed von Mangoldt sum. -/
def primePrimitiveDeficit (x : ℝ) : ℝ := x - RosserSchoenfeldPrimePrimitive.value (Real.log x)

private theorem primitive_log_integral {x : ℝ} (hx : 1 ≤ x) :
    RosserSchoenfeldPrimePrimitive.value (Real.log x) = ∫ t in (1 : ℝ)..x, Chebyshev.psi t / t := by
  have hpos : 0 < x := by linarith
  let f := fun t : ℝ => Real.log x - Real.log t
  have hd {t : ℝ} (ht : 0 < t) : HasDerivAt f (-(t⁻¹)) t := by
    simpa [f] using (Real.hasDerivAt_log ht.ne').const_sub (Real.log x)
  have hder : IntegrableOn (deriv f) (Icc 1 x) := by
    apply IntegrableOn.congr_fun (f := fun t : ℝ => -(t⁻¹)) _ _ measurableSet_Icc
    · exact (continuousOn_id.inv₀ (fun _ ht => (zero_lt_one.trans_le ht.1).ne')).neg.integrableOn_Icc
    · intro t ht
      exact (hd (zero_lt_one.trans_le ht.1)).deriv.symm
  have he := sum_mul_eq_sub_sub_integral_mul (fun n : ℕ => Λ n) (a := 1) (b := x)
    zero_le_one hx (fun _ ht => (hd (zero_lt_one.trans_le ht.1)).differentiableAt) hder
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at he
  rw [RosserSchoenfeldPrimePrimitive.value_eq_sum, Real.exp_log hpos, intervalIntegral.integral_of_le hx]
  have hsum : ∑ k ∈ Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊x⌋₊, f k * Λ k =
      ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Λ k * (Real.log x - Real.log k) := by
    rw [Nat.floor_one, ← Finset.sum_subset (show Finset.Ioc 1 ⌊x⌋₊ ⊆ Finset.Icc 1 ⌊x⌋₊ from
      fun k hk => Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hk).1.le, (Finset.mem_Ioc.mp hk).2⟩)]
    · simp [f, mul_comm]
    · intro k hk hnot
      have : k = 1 := by
        simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hnot
        omega
      simp [this]
  rw [hsum] at he
  have hzero : Chebyshev.psi 1 = 0 := by simp [Chebyshev.psi]
  have hfx : f x = 0 := sub_self _
  rw [hzero, hfx, zero_mul, mul_zero, sub_zero, zero_sub] at he
  rw [he, ← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  change -(deriv f t * Chebyshev.psi t) = Chebyshev.psi t / t
  rw [(hd (zero_lt_one.trans ht.1)).deriv, div_eq_mul_inv]
  ring

private theorem int_psi_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.psi t / t) volume a b := by
  simp only [div_eq_mul_inv]
  apply Chebyshev.psi_mono.intervalIntegrable.mul_continuousOn
  rw [uIcc_of_le hab]
  exact continuousOn_id.inv₀ fun _ ht => (ha.trans_le ht.1).ne'

/-- On any real interval the normalized Chebyshev deficit is a single increment of the
logarithmic prime primitive, evaluated at an intermediate real cutoff. -/
theorem exists_real_primitive_increment {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∃ v ∈ Icc a b, (∫ t in Ioc a b, (t-Chebyshev.psi t)/t^2) =
      (primePrimitiveDeficit v-primePrimitiveDeficit a)/a := by
  have ha0 := zero_lt_one.trans_le ha
  obtain ⟨v,hv,he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
    (f := fun t : ℝ => t⁻¹) (g := fun t : ℝ => 1-Chebyshev.psi t/t)
    hab (inv_nonneg.mpr (ha0.le.trans hab)) (fun u hu w _ huw => inv_anti₀ (ha0.trans_le hu.1) huw)
    (intervalIntegrable_const.sub (int_psi_div ha0 hab))
  refine ⟨v,hv,?_⟩
  have hker : (∫ t in Ioc a b, (t-Chebyshev.psi t)/t^2) =
      ∫ t in a..b, t⁻¹*(1-Chebyshev.psi t/t) := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    field_simp [ne_of_gt (ha0.trans ht.1)]
  rw [hker,he,intervalIntegral.integral_sub intervalIntegrable_const (int_psi_div ha0 hv.1),
    intervalIntegral.integral_const,smul_eq_mul,mul_one]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (int_psi_div zero_lt_one ha) (int_psi_div ha0 hv.1)
  rw [← primitive_log_integral ha,← primitive_log_integral (ha.trans hv.1)] at hadd
  unfold primePrimitiveDeficit
  rw [show (∫ t in a..v, Chebyshev.psi t/t) =
      RosserSchoenfeldPrimePrimitive.value (Real.log v)-RosserSchoenfeldPrimePrimitive.value (Real.log a)
      by linarith]
  ring

/-- The signed dyadic statistic is twice one upward increment of the existing prime primitive deficit. -/
theorem exists_primitive_increment {n : ℕ} (hn : 2 ≤ n) :
    ∃ ξ ∈ Icc ((n : ℝ)/2) n,
      dyadicPrimeError n = 2 * (primePrimitiveDeficit ξ - primePrimitiveDeficit ((n : ℝ)/2)) := by
  let a := (n : ℝ)/2
  let b := (n : ℝ)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ha1 : 1 ≤ a := by dsimp [a]; linarith
  have ha : 0 < a := by linarith
  have hab : a ≤ b := by dsimp [a,b]; linarith
  obtain ⟨ξ,hξ,hmean⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
    (f := fun t : ℝ => t⁻¹) (g := fun t : ℝ => 1 - Chebyshev.psi t / t)
    hab (inv_nonneg.mpr (ha.le.trans hab))
    (fun u hu v _ huv => inv_anti₀ (ha.trans_le hu.1) huv)
    (intervalIntegrable_const.sub (int_psi_div ha hab))
  refine ⟨ξ,hξ,?_⟩
  have he := dyadicPrimeError_eq_integral (show 0 < n by omega)
  have hkernel : (∫ t in Ioc a b, (t - Chebyshev.psi t) / t^2) =
      ∫ t in a..b, t⁻¹ * (1 - Chebyshev.psi t / t) := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    field_simp [ne_of_gt (ha.trans ht.1)]
  change dyadicPrimeError n = b * (∫ t in Ioc a b, _) at he
  rw [he, hkernel, hmean, intervalIntegral.integral_sub intervalIntegrable_const (int_psi_div ha hξ.1),
    intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (int_psi_div zero_lt_one ha1) (int_psi_div ha hξ.1)
  rw [← primitive_log_integral ha1, ← primitive_log_integral (ha1.trans hξ.1)] at hadd
  have hba : b * a⁻¹ = 2 := by dsimp [a,b]; field_simp
  rw [← mul_assoc, hba]
  change 2 * (ξ - a - _) = 2 * (primePrimitiveDeficit ξ - primePrimitiveDeficit a)
  unfold primePrimitiveDeficit
  linarith

end
end RiemannGaussian.DyadicPrime

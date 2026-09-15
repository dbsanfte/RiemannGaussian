import RiemannGaussian.ZetaRieszHeadOrders

/-!
# Retaining source-radius and physical-cutoff correlations

These estimates retain u in the literal damped cutoff bound,
instead of first replacing both quantities by their separate maxima.
-/

namespace RiemannGaussian.ZetaRieszHeadAdaptive
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszHeadOrders ZetaRieszCentralWindow ZetaRieszAnnulusJoint
open ZetaExposedPrimeMoments

/-- The annular radius lies below a simple rational cutoff. -/
theorem annular_radius_le_three_fifths {u : ℝ}
    (huh : u < Real.exp (-(2 / 3 : ℝ))) : u ≤ 3 / 5 := by
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 5)
  norm_num at hlog
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by norm_num)] at he
  exact huh.le.trans he

/-- The actual added-two floor bound retains the source radius,
using the damping denominator from the explicit third order onward. -/
theorem physical_base_le_source_pow {u : ℝ} (hu : 0 < u) (huh : u ≤ 3 / 5)
    {N : ℕ} (hN : 3 ≤ N) :
    (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ≤ u⁻¹ ^ N := by
  have hinv : (5 / 3 : ℝ) ≤ u⁻¹ := by
    have hi := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hu huh
    norm_num at hi
    exact hi
  have hp : (4 : ℝ) ≤ u⁻¹ ^ N := by
    calc
      _ ≤ (5 / 3 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ (5 / 3 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hinv N
  have hNc : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hfloor : (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) ≤
      u⁻¹ ^ N / (N + 1) := Nat.floor_le (by positivity)
  have hD : (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) ≤ u⁻¹ ^ N / 4 := by
    exact hfloor.trans (div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith))
  linarith

/-- The physical logarithmic length and source radius stay coupled
in a rigorous bound for the actual integer cutoff. -/
theorem length_le_source_log {u : ℝ} (hu : 0 < u) (huh : u ≤ 3 / 5)
    {N : ℕ} (hN : 3 ≤ N) :
    SquarefreeVaughanLogSource.length u N ≤ -2 * Real.log u * N := by
  have h := Real.log_le_log (by positivity) (physical_base_le_source_pow hu huh hN)
  rw [Real.log_pow, Real.log_inv] at h
  unfold SquarefreeVaughanLogSource.length
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- A cofactor tilt bound keeps the common physical logarithmic
ceiling available for correlation with the source radius. -/
theorem norm_cofactorMoment_le_tilt (A : Finset ℕ) (k : ℕ) (y L : ℝ)
    {q σ : ℝ} (hq : 0 < q) (hσ : 1 < σ) (hcoeff : 0 ≤ q + σ - 3 / 2)
    (hA : ∀ a ∈ A, Real.log a ≤ L) :
    ‖cofactorMoment A k (3 / 2 + Complex.I * y)‖ ≤
      q⁻¹ ^ k * Real.exp ((q + σ - 3 / 2) * L) * zetaMoebiusLogMajorantMass σ := by
  have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  have hw (a : ℕ) : 0 ≤ zetaMoebiusLogMajorant a * zetaPrimeExpWeight σ a :=
    mul_nonneg (zetaMoebiusLogMajorant_nonneg a) (Real.exp_pos _).le
  unfold cofactorMoment
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ A, (q⁻¹ ^ k * Real.exp ((q + σ - 3 / 2) * L)) *
        (zetaMoebiusLogMajorant a * zetaPrimeExpWeight σ a) := by
      apply Finset.sum_le_sum
      intro a ha
      have hker := norm_zetaPrimeLogKernel_le k (3 / 2 + Complex.I * y) a hq
      rw [hs] at hker
      have he : zetaPrimeExpWeight (3 / 2 - q) a =
          Real.exp ((q + σ - 3 / 2) * Real.log a) * zetaPrimeExpWeight σ a := by
        unfold zetaPrimeExpWeight
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he] at hker
      have hx := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hA a ha) hcoeff)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg a)]
      calc
        _ ≤ zetaMoebiusLogMajorant a *
            (q⁻¹ ^ k * (Real.exp ((q + σ - 3 / 2) * L) * zetaPrimeExpWeight σ a)) := by
          apply mul_le_mul (log_le_divisor_majorant a) _ (norm_nonneg _) (zetaMoebiusLogMajorant_nonneg a)
          exact hker.trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le) (by positivity))
        _ = _ := by ring
    _ = (q⁻¹ ^ k * Real.exp ((q + σ - 3 / 2) * L)) *
        ∑ a ∈ A, zetaMoebiusLogMajorant a * zetaPrimeExpWeight σ a := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_zetaMoebiusLogMajorant hσ).sum_le_tsum A (fun a _ => hw a)) (by positivity)

/-- A rational logarithm enclosure pays the tilted complementary
prime order without trusting a floating-point evaluation. -/
theorem log_euler_ratio_le : Real.log (1024 / 511 : ℝ) ≤ 89 / 128 := by
  have hlo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 511 / 512)
  have he : Real.log (1024 / 511 : ℝ) = Real.log 2 - Real.log (511 / 512 : ℝ) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  rw [he]
  norm_num at hlo
  linarith [Real.log_two_lt_d9]

/-- Retaining the common source radius in the cutoff improves the
strict scalar margin to all cofactor orders at least seven eighths. -/
theorem adaptive_high_scalar {u L : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) (M k : ℕ) (hkM : k ≤ M)
    (hk : 7 * M ≤ 8 * k) (hL : L ≤ -2 * Real.log u * M) :
    u ^ (M + 1) * ((2 / 3 : ℝ)⁻¹ ^ k * Real.exp ((515 / 3072 : ℝ) * L)) *
      (511 / 1024 : ℝ)⁻¹ ^ (M - k) ≤
        u * Real.exp (-(7 / 9216 : ℝ) * M) := by
  have hlogu : Real.log u ≤ -(2 / 3 : ℝ) := by
    simpa only [Real.log_exp] using (Real.log_lt_log hu huh).le
  have hloga : Real.log (3 / 2 : ℝ) ≤ 13 / 32 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  have hpow (x : ℝ) (hx : 0 < x) (n : ℕ) : x ^ n = Real.exp ((n : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  have hsub : ((M - k : ℕ) : ℝ) = M - k := Nat.cast_sub hkM
  have hkc : 7 * (M : ℝ) ≤ 8 * k := by exact_mod_cast hk
  have hLM := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 515 / 3072)
  have hua := mul_le_mul_of_nonneg_left hlogu
    (show 0 ≤ (1021 / 1536 : ℝ) * M by positivity)
  have hka := mul_le_mul_of_nonneg_left hloga (Nat.cast_nonneg (α := ℝ) k)
  have hmb := mul_le_mul_of_nonneg_left log_euler_ratio_le
    (Nat.cast_nonneg (α := ℝ) (M - k))
  rw [hsub] at hmb
  have hexp : (M : ℝ) * Real.log u + k * Real.log (3 / 2 : ℝ) +
      (515 / 3072 : ℝ) * L + (M - k) * Real.log (1024 / 511 : ℝ) ≤ -(7 / 9216 : ℝ) * M := by
    nlinarith
  rw [show (2 / 3 : ℝ)⁻¹ = 3 / 2 by norm_num,
    show (511 / 1024 : ℝ)⁻¹ = 1024 / 511 by norm_num,
    pow_succ u M, hpow u hu M, hpow (3 / 2) (by norm_num) k,
    hpow (1024 / 511) (by norm_num) (M - k)]
  calc
    _ = u * Real.exp ((M : ℝ) * Real.log u + k * Real.log (3 / 2 : ℝ) +
        (515 / 3072 : ℝ) * L + (M - k) * Real.log (1024 / 511 : ℝ)) := by
      rw [hsub, Real.exp_add, Real.exp_add, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hu.le

/-- The high-order convolution atom now has an independent bound for
every finite mask obeying the shared source-dependent logarithmic cutoff. -/
theorem norm_adaptive_high_atom (A : Finset ℕ) (M k : ℕ) (y : ℝ)
    {u L : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hkM : k ≤ M) (hk : 7 * M ≤ 8 * k) (hL : L ≤ -2 * Real.log u * M)
    (hA : ∀ a ∈ A, Real.log a ≤ L) :
    ‖(u : ℂ) ^ (M + 1) * (cofactorMoment A k (3 / 2 + Complex.I * y) *
      ordinaryPrimeMoment (M - k) (3 / 2 + Complex.I * y))‖ ≤
        Real.exp (-(7 / 9216 : ℝ) * M) * (u * zetaMoebiusLogMajorantMass (1025 / 1024) *
          ∑' n, zetaPrimeExpWeight (1025 / 1024) n) := by
  have hG := norm_cofactorMoment_le_tilt A k y L (q := 2 / 3) (σ := 1025 / 1024)
    (by norm_num) (by norm_num) (by norm_num) hA
  rw [show (2 / 3 : ℝ) + 1025 / 1024 - 3 / 2 = 515 / 3072 by norm_num] at hG
  have hB := norm_ordinaryPrimeMoment_le_euler (M - k) y
    (q := 511 / 1024) (by norm_num) (by norm_num)
  rw [show (3 / 2 : ℝ) - 511 / 1024 = 1025 / 1024 by norm_num] at hB
  have hmass := zetaMoebiusLogMajorantMass_nonneg (1025 / 1024)
  have hZ : 0 ≤ ∑' n, zetaPrimeExpWeight (1025 / 1024) n := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le, norm_mul]
  calc
    _ ≤ u ^ (M + 1) *
        (((2 / 3 : ℝ)⁻¹ ^ k * Real.exp ((515 / 3072 : ℝ) * L) * zetaMoebiusLogMajorantMass (1025 / 1024)) *
          ((511 / 1024 : ℝ)⁻¹ ^ (M - k) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hG hB (norm_nonneg _) (by positivity)
    _ = (u ^ (M + 1) * ((2 / 3 : ℝ)⁻¹ ^ k * Real.exp ((515 / 3072 : ℝ) * L)) *
        (511 / 1024 : ℝ)⁻¹ ^ (M - k)) *
        (zetaMoebiusLogMajorantMass (1025 / 1024) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n) := by ring
    _ ≤ (u * Real.exp (-(7 / 9216 : ℝ) * M)) *
        (zetaMoebiusLogMajorantMass (1025 / 1024) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n) :=
      mul_le_mul_of_nonneg_right (adaptive_high_scalar hu huh M k hkM hk hL) (by positivity)
    _ = _ := by ring

/-- The actual intermediate prime set supplies the shared logarithmic
ceiling for every shifted order at least N, with its original floor intact. -/
theorem intermediate_log_le_source_order {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    ∀ a ∈ intermediatePrimes u N, Real.log a ≤ -2 * Real.log u * M := by
  intro a ha
  obtain ⟨hpa, _, haX⟩ := (mem_intermediatePrimes u N a).mp ha
  have haL : Real.log a ≤ SquarefreeVaughanLogSource.length u N := by
    apply Real.log_le_log (by exact_mod_cast hpa.pos)
    exact_mod_cast haX.le
  have hL := length_le_source_log hu (annular_radius_le_three_fifths huh) hN
  have hlogu : Real.log u ≤ -(2 / 3 : ℝ) := by
    simpa only [Real.log_exp] using (Real.log_lt_log hu huh).le
  have hNc : (N : ℝ) ≤ M := by exact_mod_cast hNM
  exact haL.trans (hL.trans (mul_le_mul_of_nonneg_left hNc (by linarith)))

/-- The larger paid range is a literal finite mask of cofactor
factorial orders. Neither arithmetic prime variable is truncated. -/
def adaptiveHighOrders (M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter (fun k => 7 * M ≤ 8 * k)

/-- The full coupled convolution on the larger seven-eighths range. -/
def adaptiveHighConvolution (A : Finset ℕ) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ adaptiveHighOrders M, cofactorMoment A k s * ordinaryPrimeMoment (M - k) s

/-- Every selected high cofactor order at the actual physical cutoff
has an independent bound on the larger seven-eighths range. -/
theorem norm_actual_adaptive_high_atom (N M k : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hN : 3 ≤ N) (hNM : N ≤ M) (hk : k ∈ adaptiveHighOrders M) :
    ‖(u : ℂ) ^ (M + 1) * (cofactorMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y) *
      ordinaryPrimeMoment (M - k) (3 / 2 + Complex.I * y))‖ ≤
        Real.exp (-(7 / 9216 : ℝ) * M) * (u * zetaMoebiusLogMajorantMass (1025 / 1024) *
          ∑' n, zetaPrimeExpWeight (1025 / 1024) n) := by
  obtain ⟨hkr, hfrac⟩ := Finset.mem_filter.mp hk
  have hkM : k ≤ M := by simpa using Finset.mem_range.mp hkr
  exact norm_adaptive_high_atom _ M k y hu huh hkM hfrac le_rfl
    (intermediate_log_le_source_order hu huh hN hNM)

/-- The whole larger high-order convolution at the genuine cutoff is
independently bounded, uniformly in the ordinate and every shifted order. -/
theorem norm_actual_adaptiveHighConvolution (N M : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hN : 3 ≤ N) (hNM : N ≤ M) :
    ‖(u : ℂ) ^ (M + 1) * adaptiveHighConvolution (intermediatePrimes u N) M
      (3 / 2 + Complex.I * y)‖ ≤
        (M + 1 : ℝ) * Real.exp (-(7 / 9216 : ℝ) * M) *
          (u * zetaMoebiusLogMajorantMass (1025 / 1024) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n) := by
  unfold adaptiveHighConvolution
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ adaptiveHighOrders M, Real.exp (-(7 / 9216 : ℝ) * M) *
        (u * zetaMoebiusLogMajorantMass (1025 / 1024) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n) :=
      Finset.sum_le_sum (fun k hk => norm_actual_adaptive_high_atom N M k y hu huh hN hNM hk)
    _ = ((adaptiveHighOrders M).card : ℝ) * (Real.exp (-(7 / 9216 : ℝ) * M) *
        (u * zetaMoebiusLogMajorantMass (1025 / 1024) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n)) := by simp
    _ ≤ _ := by
      have hc : ((adaptiveHighOrders M).card : ℝ) ≤ M + 1 := by
        exact_mod_cast (Finset.card_filter_le (Finset.range (M + 1)) (fun k => 7 * M ≤ 8 * k)).trans_eq
          (Finset.card_range (M + 1))
      have hmass := zetaMoebiusLogMajorantMass_nonneg (1025 / 1024)
      have hZ : 0 ≤ ∑' n, zetaPrimeExpWeight (1025 / 1024) n := tsum_nonneg (fun _ => (Real.exp_pos _).le)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
        (show 0 ≤ Real.exp (-(7 / 9216 : ℝ) * M) *
          (u * zetaMoebiusLogMajorantMass (1025 / 1024) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n) by positivity)

end
end RiemannGaussian.ZetaRieszHeadAdaptive

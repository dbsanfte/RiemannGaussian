/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCentralPrimeLayers

/-!
# Coupled cofactor moments and independent high-order head bounds

The finite cofactor sum is retained inside its complex factorial moments.
All complete prime series keep genuine summability. For 1/2<=u<exp(-2/3), the original physical head orders
k>=15(N+j+1)/16 have independent allowance C(P,u)*(N+1)^2*exp(-7N/3200).
The exact remaining joint carrier retains the whole source; its signed floor
remains open. No new zero-free region is claimed.
-/

namespace RiemannGaussian.ZetaRieszHeadOrders
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaPrimeCofactorCompletion ZetaExposedPrimeMoments
open ZetaRieszAnnulusJoint ZetaRieszCentralWindow ZetaArithmeticLogWindow

/-- The finite logged cofactor moment retains every cofactor phase. -/
def cofactorMoment (A : Finset ℕ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ a ∈ A, (Real.log a : ℂ) * zetaPrimeLogKernel k s a

/-- A product logarithm is exactly one extra factorial order. -/
theorem log_mul_kernel (N n : ℕ) (s : ℂ) :
    (Real.log n : ℂ) * zetaPrimeLogKernel N s n =
      ((N + 1 : ℕ) : ℂ) * zetaPrimeLogKernel (N + 1) s n := by
  simp only [zetaPrimeLogKernel, pow_succ, Nat.factorial_succ, Nat.cast_mul]
  have hN : ((N + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N)
  field_simp

/-- The genuinely convergent completed prime product is an exact
factorial convolution at the shifted order. -/
theorem completedMoment_eq_convolution {s : ℂ} (hs : 1 < s.re)
    {a : ℕ} (ha : 0 < a) (N : ℕ) :
    completedPrimeProductMoment a N s = ((N + 1 : ℕ) : ℂ) *
      (zetaPrimeFeature s a * ∑ k ∈ Finset.range (N + 2),
        (Real.log a : ℂ) ^ k / (k.factorial : ℂ) * ordinaryPrimeMoment (N + 1 - k) s) := by
  apply HasSum.tsum_eq
  apply ((hasSum_unlogged_prime_product hs (N + 1) ha).mul_left
    ((N + 1 : ℕ) : ℂ)).congr_fun
  intro p
  by_cases hp : p.Prime
  · simp only [if_pos hp, log_mul_kernel]
  · simp [hp]

/-- Exact head convolution: the finite cofactor phases are summed
before any norm; every original filter shift and prime order survives. -/
theorem completedHead_eq_convolution (A : Finset ℕ)
    (hA : ∀ a ∈ A, 0 < a) (P : Polynomial ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) (L : ℝ) :
    completedCofactorHead A P N s L =
      ∑ j ∈ P.support, -(P.coeff j * ((N + j + 1 : ℕ) : ℂ) / (L : ℂ)) *
        ∑ k ∈ Finset.range (N + j + 2),
          cofactorMoment A k s * ordinaryPrimeMoment (N + j + 1 - k) s := by
  unfold completedCofactorHead completedPrimeProductFilter
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [cofactorMoment, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [completedMoment_eq_convolution hs (hA a ha)]
  simp only [Finset.mul_sum, zetaPrimeLogKernel]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The actual damped floor is bounded using its denominator, including
the physical added two, from order two onward. -/
theorem physical_base_le_two_pow {u : ℝ} (hu : 1 / 2 ≤ u)
    {N : ℕ} (hN : 2 ≤ N) :
    (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ≤ 2 ^ N := by
  have hu0 : 0 < u := by linarith
  have hinv : u⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hu0).mpr (by linarith)
  have hfloor : (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) ≤
      u⁻¹ ^ N / (N + 1) := Nat.floor_le (by positivity)
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (4 : ℝ) ≤ 2 ^ N := by
    calc
      _ = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hN
  have hD : (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) ≤ 2 ^ N / 3 := by
    calc
      _ ≤ u⁻¹ ^ N / (N + 1) := hfloor
      _ ≤ 2 ^ N / (N + 1) := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hinv N) (by positivity)
      _ ≤ 2 ^ N / 3 := div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  linarith

/-- A sharper physical length bound keeps the original integer floor. -/
theorem length_le_two_log_two {u : ℝ} (hu : 1 / 2 ≤ u)
    {N : ℕ} (hN : 2 ≤ N) :
    SquarefreeVaughanLogSource.length u N ≤ 2 * Real.log 2 * N := by
  have h := Real.log_le_log (by positivity) (physical_base_le_two_pow hu hN)
  rw [Real.log_pow] at h
  unfold SquarefreeVaughanLogSource.length
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- The sharper physical bound places high cofactor orders inside
the already controlled lower logarithmic window. -/
theorem cofactor_log_le_lower_order {u : ℝ} (hu : 1 / 2 ≤ u)
    {N M k a : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) (hk : 15 * M ≤ 16 * k)
    (ha : a ∈ intermediatePrimes u N) : Real.log a ≤ (3 / 2 : ℝ) * k := by
  obtain ⟨hpa, _, haX⟩ := (mem_intermediatePrimes u N a).mp ha
  have haL : Real.log a ≤ SquarefreeVaughanLogSource.length u N := by
    apply Real.log_le_log (by exact_mod_cast hpa.pos)
    exact_mod_cast haX.le
  have hL := length_le_two_log_two hu hN
  have htwo : 2 * Real.log 2 ≤ (45 / 32 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hNc : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hkc : 15 * (M : ℝ) ≤ 16 * k := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg (α := ℝ) N)
  nlinarith

/-- Complete unlogged prime moments have an independent Euler envelope
for every positive tilt strictly below the half-plane gap. -/
theorem norm_ordinaryPrimeMoment_le_euler (m : ℕ) (y : ℝ)
    {q : ℝ} (hq : 0 < q) (hqhalf : q < 1 / 2) :
    ‖ordinaryPrimeMoment m (3 / 2 + Complex.I * y)‖ ≤
      q⁻¹ ^ m * ∑' n, zetaPrimeExpWeight (3 / 2 - q) n := by
  let s : ℂ := 3 / 2 + Complex.I * y
  let f : ℕ → ℂ := fun n => if n.Prime then zetaPrimeLogKernel m s n else 0
  let w : ℕ → ℝ := fun n => q⁻¹ ^ m * zetaPrimeExpWeight (3 / 2 - q) n
  have hs : s.re = (3 / 2 : ℝ) := by simp [s]
  have hf : Summable f := summable_ordinaryPrimeMoment (by rw [hs]; norm_num) m
  have hw : Summable w := (summable_zetaPrimeExpWeight
    (by linarith : 1 < (3 / 2 : ℝ) - q)).mul_left (q⁻¹ ^ m)
  have hb (n : ℕ) : ‖f n‖ ≤ w n := by
    by_cases hn : n.Prime
    · simpa only [f, w, if_pos hn, hs] using norm_zetaPrimeLogKernel_le m s n hq
    · simp only [f, if_neg hn, norm_zero, w]
      unfold zetaPrimeExpWeight
      positivity
  calc
    _ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n, w n := hf.norm.tsum_le_tsum hb hw
    _ = _ := tsum_mul_left

/-- A rational exponential margin refines the existing lower-window
rate without numerical or external certificate assumptions. -/
theorem lowerRate_le_exp : centralLowerRate ≤ Real.exp (-(1 / 200 : ℝ)) := by
  have hlog : Real.log (3 / 2 : ℝ) - 631 / 1536 ≤ -(1 / 200 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  calc
    _ = Real.exp (Real.log (3 / 2 : ℝ) - 631 / 1536) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num), centralLowerRate, Real.exp_neg]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hlog

/-- The independent Euler tilt has only a small exponential cost
at every source radius in the proved annular range. -/
theorem eulerRate_le_exp {u : ℝ} (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    u * (127 / 256 : ℝ)⁻¹ ≤ Real.exp (1 / 25 : ℝ) := by
  have hlo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 127 / 128)
  have hlog : Real.log (256 / 127 : ℝ) - 2 / 3 ≤ 1 / 25 := by
    have he : Real.log (256 / 127 : ℝ) = Real.log 2 - Real.log (127 / 128 : ℝ) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]
      norm_num
    rw [he]
    norm_num at hlo
    linarith [Real.log_two_lt_d9]
  calc
    _ ≤ Real.exp (-(2 / 3 : ℝ)) * (127 / 256 : ℝ)⁻¹ := by gcongr
    _ = Real.exp (Real.log (256 / 127 : ℝ) - 2 / 3) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num), Real.exp_neg]
      norm_num
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hlog

/-- The finite cofactor moment is independently small when its
physical logarithms lie in the lower window of its own factorial order. -/
theorem norm_normalized_cofactorMoment_lower (A : Finset ℕ) (k : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hA : ∀ a ∈ A, Real.log a ≤ (3 / 2 : ℝ) * k) :
    ‖(u : ℂ) ^ (k + 1) * cofactorMoment A k (3 / 2 + Complex.I * y)‖ ≤
      Real.exp (-(k : ℝ) / 200) * (u * tiltConstant 1 (2 / 3) (257 / 256)) := by
  have hf (n : ℕ) : ‖(Real.log n : ℂ)‖ ≤ zetaMoebiusLogMajorant n := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg n)] using
      log_le_divisor_majorant n
  have h := norm_lower_central_sum_le A (fun n => (Real.log n : ℂ))
    (fun n _ => hf n) 1 k y hu huh hA
  have he : (fun n : ℕ => zetaPrimeFilterKernel 1 k (3 / 2 + Complex.I * y) n) =
      (fun n => zetaPrimeLogKernel k (3 / 2 + Complex.I * y) n) := by
    funext n
    simp only [zetaPrimeFilterKernel, ZetaRieszCosineCarrier.factorialPolynomial_one,
      zetaPrimeLogKernel, zetaPrimeFeature, neg_mul]
  change ‖(u : ℂ) ^ (k + 1) * ∑ n ∈ A,
    (Real.log n : ℂ) * (fun n : ℕ => zetaPrimeFilterKernel 1 k (3 / 2 + Complex.I * y) n) n‖ ≤ _ at h
  rw [he] at h
  apply h.trans
  have hr := pow_le_pow_left₀ (by unfold centralLowerRate; positivity) lowerRate_le_exp k
  have hepow : Real.exp (-(1 / 200 : ℝ)) ^ k = Real.exp (-(k : ℝ) / 200) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hepow] at hr
  exact mul_le_mul_of_nonneg_right hr
    (mul_nonneg hu.le (tiltConstant_nonneg 1 (by norm_num)))

/-- Uniform phase-independent control of every complete prime order
at the fixed rational Euler tilt, including order zero. -/
theorem norm_normalized_ordinaryMoment (m : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ‖(u : ℂ) ^ m * ordinaryPrimeMoment m (3 / 2 + Complex.I * y)‖ ≤
      Real.exp ((m : ℝ) / 25) * ∑' n, zetaPrimeExpWeight (257 / 256) n := by
  have h := norm_ordinaryPrimeMoment_le_euler m y
    (q := 127 / 256) (by norm_num) (by norm_num)
  rw [show (3 / 2 : ℝ) - 127 / 256 = 257 / 256 by norm_num] at h
  have hm : 0 ≤ ∑' n, zetaPrimeExpWeight (257 / 256) n :=
    tsum_nonneg (fun _ => (Real.exp_pos _).le)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  calc
    _ ≤ u ^ m * ((127 / 256 : ℝ)⁻¹ ^ m * ∑' n, zetaPrimeExpWeight (257 / 256) n) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = (u * (127 / 256 : ℝ)⁻¹) ^ m * ∑' n, zetaPrimeExpWeight (257 / 256) n := by rw [mul_pow]; ring
    _ ≤ Real.exp (1 / 25 : ℝ) ^ m * ∑' n, zetaPrimeExpWeight (257 / 256) n :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (eulerRate_le_exp huh) m) hm
    _ = _ := by rw [← Real.exp_nat_mul]; congr 2; ring

/-- The retained high-order mask is a mask on factorial orders, not a
truncation of the infinite prime variable. -/
def highOrders (M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter (fun k => 15 * M ≤ 16 * k)

/-- The high-order part of the exact cofactor convolution, retaining
both complex factors before any estimate. -/
def highConvolution (A : Finset ℕ) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ highOrders M, cofactorMoment A k s * ordinaryPrimeMoment (M - k) s

/-- A uniform strict exponential margin for the coupled high orders. -/
def highRate : ℝ := Real.exp (-(7 / 3200 : ℝ))

/-- The exact high-order rate is positive and strictly below one. -/
theorem highRate_bounds : 0 < highRate ∧ highRate < 1 := by
  constructor
  · exact Real.exp_pos _
  · exact Real.exp_lt_one_iff.mpr (by norm_num)

/-- Every high convolution order has an independent bound. The Euler
growth of its complementary prime order is paid by the cofactor decay. -/
theorem norm_high_order_atom (A : Finset ℕ) (M k : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hk : k ∈ highOrders M)
    (hA : ∀ a ∈ A, Real.log a ≤ (45 / 32 : ℝ) * M) :
    ‖(u : ℂ) ^ (M + 1) * (cofactorMoment A k (3 / 2 + Complex.I * y) *
      ordinaryPrimeMoment (M - k) (3 / 2 + Complex.I * y))‖ ≤
      highRate ^ M * (u * tiltConstant 1 (2 / 3) (257 / 256) *
        ∑' n, zetaPrimeExpWeight (257 / 256) n) := by
  obtain ⟨hkr, hfrac⟩ := Finset.mem_filter.mp hk
  have hkM : k ≤ M := by simpa using Finset.mem_range.mp hkr
  have hf : 15 * (M : ℝ) ≤ 16 * k := by exact_mod_cast hfrac
  have hsub : ((M - k : ℕ) : ℝ) = M - k := by exact Nat.cast_sub hkM
  have hlow : ∀ a ∈ A, Real.log a ≤ (3 / 2 : ℝ) * k := by
    intro a ha
    linarith [hA a ha]
  have hG := norm_normalized_cofactorMoment_lower A k y hu huh hlow
  have hB := norm_normalized_ordinaryMoment (M - k) y hu.le huh
  have he : (u : ℂ) ^ (M + 1) * (cofactorMoment A k (3 / 2 + Complex.I * y) *
      ordinaryPrimeMoment (M - k) (3 / 2 + Complex.I * y)) =
      ((u : ℂ) ^ (k + 1) * cofactorMoment A k (3 / 2 + Complex.I * y)) *
        ((u : ℂ) ^ (M - k) * ordinaryPrimeMoment (M - k) (3 / 2 + Complex.I * y)) := by
    rw [show M + 1 = (k + 1) + (M - k) by omega, pow_add]
    ring
  have hT : 0 ≤ tiltConstant 1 (2 / 3) (257 / 256) := tiltConstant_nonneg 1 (by norm_num)
  have hZ : 0 ≤ ∑' n, zetaPrimeExpWeight (257 / 256) n :=
    tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have hexp : Real.exp (-(k : ℝ) / 200) * Real.exp (((M - k : ℕ) : ℝ) / 25) ≤ highRate ^ M := by
    rw [← Real.exp_add, highRate, ← Real.exp_nat_mul, hsub]
    apply Real.exp_le_exp.mpr
    linarith
  rw [he, norm_mul]
  calc
    _ ≤ (Real.exp (-(k : ℝ) / 200) * (u * tiltConstant 1 (2 / 3) (257 / 256))) *
        (Real.exp (((M - k : ℕ) : ℝ) / 25) * ∑' n, zetaPrimeExpWeight (257 / 256) n) :=
      mul_le_mul hG hB (norm_nonneg _) (by positivity)
    _ = (Real.exp (-(k : ℝ) / 200) * Real.exp (((M - k : ℕ) : ℝ) / 25)) *
        (u * tiltConstant 1 (2 / 3) (257 / 256) * ∑' n, zetaPrimeExpWeight (257 / 256) n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp (by positivity)

/-- The whole high-order convolution has an independent explicit
geometric allowance, uniformly in phase and in the finite cofactor mask. -/
theorem norm_highConvolution_le (A : Finset ℕ) (M : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hA : ∀ a ∈ A, Real.log a ≤ (45 / 32 : ℝ) * M) :
    ‖(u : ℂ) ^ (M + 1) * highConvolution A M (3 / 2 + Complex.I * y)‖ ≤
      (M + 1 : ℝ) * highRate ^ M * (u * tiltConstant 1 (2 / 3) (257 / 256) *
        ∑' n, zetaPrimeExpWeight (257 / 256) n) := by
  unfold highConvolution
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ highOrders M, highRate ^ M * (u * tiltConstant 1 (2 / 3) (257 / 256) *
        ∑' n, zetaPrimeExpWeight (257 / 256) n) :=
      Finset.sum_le_sum (fun k hk => norm_high_order_atom A M k y hu huh hk hA)
    _ = ((highOrders M).card : ℝ) * (highRate ^ M * (u * tiltConstant 1 (2 / 3) (257 / 256) *
        ∑' n, zetaPrimeExpWeight (257 / 256) n)) := by simp
    _ ≤ _ := by
      have hc : ((highOrders M).card : ℝ) ≤ M + 1 := by
        exact_mod_cast (Finset.card_filter_le (Finset.range (M + 1)) (fun k => 15 * M ≤ 16 * k)).trans_eq
          (Finset.card_range (M + 1))
      have hT : 0 ≤ tiltConstant 1 (2 / 3) (257 / 256) := tiltConstant_nonneg 1 (by norm_num)
      have hZ : 0 ≤ ∑' n, zetaPrimeExpWeight (257 / 256) n :=
        tsum_nonneg (fun _ => (Real.exp_pos _).le)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
        (show 0 ≤ highRate ^ M * (u * tiltConstant 1 (2 / 3) (257 / 256) *
          ∑' n, zetaPrimeExpWeight (257 / 256) n) by unfold highRate; positivity)

/-- Every actual intermediate cofactor meets the uniform support bound
for every original shifted factorial order at least N. -/
theorem intermediate_log_le_order {u : ℝ} (hu : 1 / 2 ≤ u)
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ∀ a ∈ intermediatePrimes u N, Real.log a ≤ (45 / 32 : ℝ) * M := by
  intro a ha
  obtain ⟨hpa, _, haX⟩ := (mem_intermediatePrimes u N a).mp ha
  have haL : Real.log a ≤ SquarefreeVaughanLogSource.length u N := by
    apply Real.log_le_log (by exact_mod_cast hpa.pos)
    exact_mod_cast haX.le
  have htwo : 2 * Real.log 2 ≤ (45 / 32 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hm := mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg (α := ℝ) N)
  have hNc : (N : ℝ) ≤ M := by exact_mod_cast hNM
  linarith [length_le_two_log_two hu hN]

/-- The physical reciprocal length never grows: the added two gives
a logarithmic length strictly exceeding one at every order. -/
theorem one_le_length (u : ℝ) (N : ℕ) : 1 ≤ SquarefreeVaughanLogSource.length u N := by
  have hlog : Real.log 2 ≤ Real.log (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) :=
    Real.log_le_log (by norm_num) (by exact le_add_of_nonneg_left (Nat.cast_nonneg _))
  unfold SquarefreeVaughanLogSource.length
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith [Real.log_two_gt_d9]

/-- The exact high-order part of the physical completed head retains
all fixed polynomial coefficients and factorial shifts. -/
def highHead (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ P.support, -(P.coeff j * ((N + j + 1 : ℕ) : ℂ) /
      (SquarefreeVaughanLogSource.length u N : ℂ)) *
    highConvolution (intermediatePrimes u N) (N + j + 1) (3 / 2 + Complex.I * y)

/-- A finite fixed-filter cost; no source or phase cancellation is
assumed in its definition or in the high-order estimate. -/
def highHeadCost (P : Polynomial ℂ) (u : ℝ) : ℝ :=
  (u * tiltConstant 1 (2 / 3) (257 / 256) * ∑' n, zetaPrimeExpWeight (257 / 256) n) *
    ∑ j ∈ P.support, ‖P.coeff j‖ * u⁻¹ ^ (j + 1) * (j + 2 : ℝ) ^ 2


/-- One fixed filter coefficient has an explicit source-normalized
high-order allowance at the original physical cutoff. -/
theorem norm_highHead_term_le (c : ℂ) (j N : ℕ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) (hN : 2 ≤ N) :
    ‖(u : ℂ) ^ (N + 1) * (-(c * ((N + j + 1 : ℕ) : ℂ) /
      (SquarefreeVaughanLogSource.length u N : ℂ)) *
      highConvolution (intermediatePrimes u N) (N + j + 1) (3 / 2 + Complex.I * y))‖ ≤
      ((N + 1 : ℝ) ^ 2 * highRate ^ N) *
        ((u * tiltConstant 1 (2 / 3) (257 / 256) * ∑' n, zetaPrimeExpWeight (257 / 256) n) *
          (‖c‖ * u⁻¹ ^ (j + 1) * (j + 2 : ℝ) ^ 2)) := by
  let M : ℕ := N + j + 1
  let L : ℝ := SquarefreeVaughanLogSource.length u N
  let C : ℝ := u * tiltConstant 1 (2 / 3) (257 / 256) * ∑' n, zetaPrimeExpWeight (257 / 256) n
  have hu0 : 0 < u := by linarith
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
  have hT : 0 ≤ tiltConstant 1 (2 / 3) (257 / 256) := tiltConstant_nonneg 1 (by norm_num)
  have hZ : 0 ≤ ∑' n, zetaPrimeExpWeight (257 / 256) n := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL : 1 ≤ L := one_le_length u N
  have hNM : N ≤ M := by dsimp [M]; omega
  have hconv := norm_highConvolution_le (intermediatePrimes u N) M y hu0 huh
    (intermediate_log_le_order hu hN hNM)
  have hpow : (u : ℂ)⁻¹ ^ (j + 1) * (u : ℂ) ^ (M + 1) = (u : ℂ) ^ (N + 1) := by
    rw [show M + 1 = (j + 1) + (N + 1) by dsimp [M]; omega,
      pow_add (u : ℂ) (j + 1) (N + 1),
      ← mul_assoc, ← mul_pow, inv_mul_cancel₀ huC, one_pow, one_mul]
  have he (v : ℂ) : (u : ℂ) ^ (N + 1) * (-(c * (M : ℂ) / (L : ℂ)) * v) =
      (-(c * (M : ℂ) / (L : ℂ)) * (u : ℂ)⁻¹ ^ (j + 1)) * ((u : ℂ) ^ (M + 1) * v) := by
    calc
      _ = -(c * (M : ℂ) / (L : ℂ)) * ((u : ℂ) ^ (N + 1) * v) := by ring
      _ = _ := by rw [← hpow]; ring
  have hc : ‖-(c * (M : ℂ) / (L : ℂ)) * (u : ℂ)⁻¹ ^ (j + 1)‖ ≤
      ‖c‖ * M * u⁻¹ ^ (j + 1) := by
    rw [norm_mul, norm_neg, norm_div, norm_mul, Complex.norm_natCast,
      Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ L),
      norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    exact mul_le_mul_of_nonneg_right (div_le_self (by positivity) hL) (by positivity)
  have hMa : (M : ℝ) ≤ (N + 1 : ℝ) * (j + 2 : ℝ) := by
    dsimp [M]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) j,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (Nat.cast_nonneg (α := ℝ) j)]
  have hMb : (M + 1 : ℝ) ≤ (N + 1 : ℝ) * (j + 2 : ℝ) := by
    dsimp [M]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) j,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (Nat.cast_nonneg (α := ℝ) j)]
  have hMM : (M : ℝ) * (M + 1) ≤ (N + 1 : ℝ) ^ 2 * (j + 2 : ℝ) ^ 2 := by
    calc
      _ ≤ ((N + 1 : ℝ) * (j + 2 : ℝ)) * ((N + 1 : ℝ) * (j + 2 : ℝ)) :=
        mul_le_mul hMa hMb (by positivity) (by positivity)
      _ = _ := by ring
  have hr : highRate ^ M ≤ highRate ^ N := by
    rw [highRate, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
    linarith
  change ‖(u : ℂ) ^ (N + 1) * (-(c * (M : ℂ) / (L : ℂ)) * _)‖ ≤
    ((N + 1 : ℝ) ^ 2 * highRate ^ N) * (C * (‖c‖ * u⁻¹ ^ (j + 1) * (j + 2 : ℝ) ^ 2))
  rw [he, norm_mul]
  calc
    _ ≤ (‖c‖ * M * u⁻¹ ^ (j + 1)) * ((M + 1 : ℝ) * highRate ^ M * C) :=
      mul_le_mul hc hconv (norm_nonneg _) (by positivity)
    _ = ((M : ℝ) * (M + 1) * highRate ^ M) * (C * ‖c‖ * u⁻¹ ^ (j + 1)) := by ring
    _ ≤ ((N + 1 : ℝ) ^ 2 * (j + 2 : ℝ) ^ 2 * highRate ^ N) *
        (C * ‖c‖ * u⁻¹ ^ (j + 1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hMM hr (pow_nonneg highRate_bounds.1.le _) (by positivity)
    _ = _ := by ring

/-- The entire physical high-order head is independently bounded for
every fixed filter and every ordinate, with its exact shifted order cost. -/
theorem norm_highHead_le (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) (hN : 2 ≤ N) :
    ‖(u : ℂ) ^ (N + 1) * highHead P u y N‖ ≤
      ((N + 1 : ℝ) ^ 2 * highRate ^ N) * highHeadCost P u := by
  unfold highHead
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ P.support, ((N + 1 : ℝ) ^ 2 * highRate ^ N) *
        ((u * tiltConstant 1 (2 / 3) (257 / 256) * ∑' n, zetaPrimeExpWeight (257 / 256) n) *
          (‖P.coeff j‖ * u⁻¹ ^ (j + 1) * (j + 2 : ℝ) ^ 2)) :=
      Finset.sum_le_sum (fun j _ => norm_highHead_term_le (P.coeff j) j N y hu huh hN)
    _ = _ := by simp only [highHeadCost, Finset.mul_sum]

/-- The explicit polynomial-times-geometric allowance tends to zero. -/
theorem tendsto_high_allowance :
    Tendsto (fun N : ℕ => (N + 1 : ℝ) ^ 2 * highRate ^ N) atTop (nhds 0) := by
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 highRate_bounds.1.le highRate_bounds.2
  have h1 := tendsto_self_mul_const_pow_of_lt_one highRate_bounds.1.le highRate_bounds.2
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one highRate_bounds.1.le highRate_bounds.2
  have h := (h2.add (h1.const_mul 2)).add h0
  simpa only [mul_zero, zero_add] using h.congr (fun N => by ring)

/-- A definite part of the actual completed head now has independent
source-scale decay, with no zero, exposure, or cancellation hypothesis. -/
theorem tendsto_highHead (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * highHead P u y N) atTop (nhds 0) := by
  apply squeeze_zero_norm' (by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact norm_highHead_le P N y hu huh hN)
  simpa only [zero_mul] using tendsto_high_allowance.mul_const (highHeadCost P u)

/-- The remaining exact lower and middle cofactor orders keep both
complex prime factors coupled, with no absolute-value replacement. -/
def remainingHead (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ P.support, -(P.coeff j * ((N + j + 1 : ℕ) : ℂ) /
      (SquarefreeVaughanLogSource.length u N : ℂ)) *
    ∑ k ∈ (Finset.range (N + j + 2)).filter (fun k => 16 * k < 15 * (N + j + 1)),
      cofactorMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y) *
        ordinaryPrimeMoment (N + j + 1 - k) (3 / 2 + Complex.I * y)

/-- The remaining head and paid head partition every original
factorial order exactly. No infinite prime tail is truncated. -/
theorem completedHead_eq_remaining_add_high (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    completedCofactorHead (intermediatePrimes u N) P N (3 / 2 + Complex.I * y)
      (SquarefreeVaughanLogSource.length u N) = remainingHead P u y N + highHead P u y N := by
  rw [completedHead_eq_convolution _ (fun a ha =>
    ((mem_intermediatePrimes u N a).mp ha).1.pos) P N (by norm_num)]
  simp only [remainingHead, highHead, highConvolution, highOrders,
    ← Finset.sum_add_distrib, ← mul_add]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : 15 * (N + j + 1) ≤ 16 * k
  · simp [hk, not_lt.mpr hk]
  · simp [hk, lt_of_not_ge hk]

/-- Removing only the independently controlled high orders gives an
exact asymptotic transport for the actual physical completed head. -/
theorem tendsto_completedHead_sub_remaining (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (completedCofactorHead (intermediatePrimes u N) P N (3 / 2 + Complex.I * y)
        (SquarefreeVaughanLogSource.length u N) - remainingHead P u y N)) atTop (nhds 0) := by
  simpa only [completedHead_eq_remaining_add_high, add_sub_cancel_left] using tendsto_highHead P y hu huh


/-- The actual completed central carrier with only its independently
paid high factorial orders removed. Every finite arithmetic mask survives. -/
def orderReducedJoint (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ZetaRieszCentralPair.centralUnpairedResponse P u y N + remainingHead P u y N +
    ZetaRieszCentralPair.centralPairResponse P u y N

/-- The exact difference of the whole signed carriers is precisely
the high-order head, without any norm on the surviving correlations. -/
theorem centralJoint_sub_orderReduced (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    ZetaRieszCentralPair.centralJoint P u y N - orderReducedJoint P u y N = highHead P u y N := by
  rw [ZetaRieszCentralPair.centralJoint, orderReducedJoint, completedHead_eq_remaining_add_high]
  ring

/-- The actual joint carrier has an explicit independent transport
allowance from order two onward, uniform in the ordinate. -/
theorem norm_centralJoint_sub_orderReduced_le (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) (hN : 2 ≤ N) :
    ‖(u : ℂ) ^ (N + 1) *
      (ZetaRieszCentralPair.centralJoint P u y N - orderReducedJoint P u y N)‖ ≤
      ((N + 1 : ℝ) ^ 2 * highRate ^ N) * highHeadCost P u := by
  rw [centralJoint_sub_orderReduced]
  exact norm_highHead_le P N y hu huh hN

/-- The entire central source survives this independently paid
deletion. A floor for the remaining joint signed carrier is still open. -/
theorem tendsto_orderReducedJoint_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      orderReducedJoint 1 (3 / 2 - rho.1.re) rho.1.im N)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (ZetaRieszCentralPair.tendsto_centralJoint_exposed rho hrho hexposed huh).sub
    (tendsto_highHead 1 rho.1.im hu huh)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have he := centralJoint_sub_orderReduced 1 (3 / 2 - rho.1.re) rho.1.im N
  rw [← he]
  ring

end
end RiemannGaussian.ZetaRieszHeadOrders

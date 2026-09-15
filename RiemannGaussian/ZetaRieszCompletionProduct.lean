/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCompletion

/-!
# Completion errors at their full product scale

Both literal omitted prime ranges are multiplied by their actual complementary moment before any decay claim. The bounds are independent of hypothetical zeros and uniform in height.
-/

namespace RiemannGaussian.ZetaRieszCompletionProduct
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeCompletion ZetaRieszPrimePairConvolution
open ZetaRieszAnnulusJoint ZetaExposedPrimeMoments

/-- A tighter checked logarithm enclosure leaves a strict margin after
the growing complementary moment is included. -/
theorem log_eight_thirds_le_sharp : Real.log (8 / 3 : ℝ) ≤ 63 / 64 := by
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num, Nat.cast_ofNat] using
      Real.log_pow (2 : ℝ) (3 : ℕ)
  rw [Real.log_div (by norm_num) (by norm_num), hlog8]
  linarith [Real.log_two_lt_d9, Real.log_three_gt_d9]

/-- The polynomial small-prime prefix has a uniform moment bound with
no factorial-order growth; its original cutoff is unchanged. -/
theorem norm_smallPrimeMoment_le (N k : ℕ) (y : ℝ) :
    ‖smallPrimeMoment N k y‖ ≤ (N + 1 : ℝ) ^ 2 *
      ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by
  let L : ℝ := Real.log ((N + 1 : ℝ) ^ 2)
  have hL : 0 ≤ L := Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  have hA : ∀ p ∈ Nat.primesLE (N ^ 2), Real.log p ≤ L := by
    intro p hp
    obtain ⟨hpN, hprime⟩ := Nat.mem_primesLE.mp hp
    apply Real.log_le_log (by exact_mod_cast hprime.pos)
    have hc : (p : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hpN
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hb := ZetaRieszPairOrders.norm_finiteMoment_le_tilt (Nat.primesLE (N ^ 2)) k y L
    (q := 1) (σ := 1025 / 1024) (by norm_num) (by norm_num) (by norm_num) hA
  norm_num only [inv_one, one_pow, one_mul] at hb
  have he : Real.exp ((1 + 1025 / 1024 - 3 / 2 : ℝ) * L) ≤ (N + 1 : ℝ) ^ 2 := by
    calc
      _ ≤ Real.exp L := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := Real.exp_log (by positivity)
  norm_num at he
  exact hb.trans (mul_le_mul_of_nonneg_right he (tsum_nonneg (fun _ => (Real.exp_pos _).le)))

/-- The full complete prime array has the same Euler norm envelope as
any finite selection, with its genuine infinite sum justified. -/
theorem norm_completeMoment_le (k : ℕ) (y : ℝ) :
    ‖ordinaryPrimeMoment k (3 / 2 + Complex.I * y)‖ ≤
      (511 / 1024 : ℝ)⁻¹ ^ k * ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by
  have h := norm_maskedMoment_upper_le (fun p => p.Prime) k y 0
    (q := 511 / 1024) (σ := 1025 / 1024) (by norm_num) (by norm_num) (by norm_num)
    (fun p _ => Real.log_natCast_nonneg p)
  have he : maskedMoment (fun p => p.Prime) k y =
      ordinaryPrimeMoment k (3 / 2 + Complex.I * y) := by
    unfold maskedMoment ordinaryPrimeMoment
    congr 1
    funext p
    by_cases hp : p.Prime <;> simp [hp]
  rw [he] at h
  simpa only [mul_zero, Real.exp_zero, mul_one] using h

/-- The literal upper completion error still decays after multiplication
by the entire complementary Euler envelope. Three shifted orders are
allowed above 15N/32, and the total order may reach N+2. -/
theorem upper_product_scalar {u L : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) (N k l : ℕ)
    (hk : 32 * k ≤ 15 * N + 96) (hkl : k + l ≤ N + 2)
    (hL : (4 / 3 : ℝ) * N ≤ L) :
    u ^ (N + 1) * (((3 / 8 : ℝ)⁻¹ ^ k * Real.exp (-(127 / 1024 : ℝ) * L)) *
      (511 / 1024 : ℝ)⁻¹ ^ l) ≤
        Real.exp 2 * Real.exp (-(5 / 4096 : ℝ) * N) := by
  have hlu : Real.log u ≤ -(2 / 3 : ℝ) := by
    simpa only [Real.log_exp] using (Real.log_lt_log hu huh).le
  have ha := mul_le_mul_of_nonneg_left log_eight_thirds_le_sharp (Nat.cast_nonneg (α := ℝ) k)
  have hb := mul_le_mul_of_nonneg_left ZetaRieszHeadAdaptive.log_euler_ratio_le
    (Nat.cast_nonneg (α := ℝ) l)
  have hc := mul_le_mul_of_nonneg_left hlu (Nat.cast_nonneg (α := ℝ) (N + 1))
  have hkc : 32 * (k : ℝ) ≤ 15 * N + 96 := by exact_mod_cast hk
  have hklc : (k : ℝ) + l ≤ N + 2 := by exact_mod_cast hkl
  have hpow (x : ℝ) (hx : 0 < x) (r : ℕ) : x ^ r = Real.exp ((r : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  rw [show (3 / 8 : ℝ)⁻¹ = 8 / 3 by norm_num,
    show (511 / 1024 : ℝ)⁻¹ = 1024 / 511 by norm_num,
    hpow u hu, hpow (8 / 3) (by norm_num), hpow (1024 / 511) (by norm_num),
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast at hc ⊢
  nlinarith only [ha, hb, hc, hkc, hklc, hL]

/-- The omitted polynomial prime prefix pays the growing other factor
from order N/8 onward, at the same common geometric rate. -/
theorem small_product_scalar {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) (N k l : ℕ)
    (hk : N ≤ 8 * k) (hkl : k + l ≤ N + 2) :
    u ^ (N + 1) * (511 / 1024 : ℝ)⁻¹ ^ l ≤
      Real.exp 2 * Real.exp (-(5 / 4096 : ℝ) * N) := by
  have hlu : Real.log u ≤ -(2 / 3 : ℝ) := by
    simpa only [Real.log_exp] using (Real.log_lt_log hu huh).le
  have hb := mul_le_mul_of_nonneg_left ZetaRieszHeadAdaptive.log_euler_ratio_le
    (Nat.cast_nonneg (α := ℝ) l)
  have hc := mul_le_mul_of_nonneg_left hlu (Nat.cast_nonneg (α := ℝ) (N + 1))
  have hkc : (N : ℝ) ≤ 8 * k := by exact_mod_cast hk
  have hklc : (k : ℝ) + l ≤ N + 2 := by exact_mod_cast hkl
  have hpow (x : ℝ) (hx : 0 < x) (r : ℕ) : x ^ r = Real.exp ((r : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  rw [show (511 / 1024 : ℝ)⁻¹ = 1024 / 511 by norm_num,
    hpow u hu, hpow (1024 / 511) (by norm_num), ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast at hc ⊢
  nlinarith only [hb, hc, hkc, hklc, Nat.cast_nonneg (α := ℝ) N]

/-- Both omitted prime ranges are paid after multiplication by the
full complementary moment envelope. This is independent of every
hypothetical zero and uniform over the eligible orders and all heights. -/
theorem eventually_norm_completion_product_le {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ k l : ℕ, N ≤ 8 * k → 32 * k ≤ 15 * N + 96 →
      k + l ≤ N + 2 → ∀ (y : ℝ) (z : ℂ),
      ‖z‖ ≤ (511 / 1024 : ℝ)⁻¹ ^ l * (∑' n, zetaPrimeExpWeight (1025 / 1024) n) →
      ‖(u : ℂ) ^ (N + 1) *
        ((finiteMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y) -
          ordinaryPrimeMoment k (3 / 2 + Complex.I * y)) * z)‖ ≤
        2 * Real.exp 2 * (N + 1 : ℝ) ^ 2 * Real.exp (-(5 / 4096 : ℝ) * N) *
          (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2 := by
  have hu1 : u < 1 := huh.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  filter_upwards [ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
    (by norm_num : (0 : ℝ) ≤ 2 / 3) huh,
    ZetaRieszSemiprimeSupport.eventually_quadratic_head_lt_physical hu hu1] with N hLN hNX
  intro k l hklo hkhi hkl y z hz
  let Z : ℝ := ∑' n, zetaPrimeExpWeight (1025 / 1024) n
  let H : ℝ := (3 / 8 : ℝ)⁻¹ ^ k * Real.exp (-(127 / 1024 : ℝ) *
    SquarefreeVaughanLogSource.length u N)
  let R : ℝ := Real.exp 2 * Real.exp (-(5 / 4096 : ℝ) * N)
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have hhigh := norm_maskedMoment_upper_le (fun p => p.Prime ∧
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p)
    k y (SquarefreeVaughanLogSource.length u N) (q := 3 / 8) (σ := 1025 / 1024)
    (by norm_num) (by norm_num) (by norm_num)
    (fun p hp => physicalPrimeTail_log_support u N p hp.2)
  norm_num only [show (3 / 2 : ℝ) - 3 / 8 - 1025 / 1024 = 127 / 1024 by norm_num] at hhigh
  rw [show (8 / 3 : ℝ) = (3 / 8 : ℝ)⁻¹ by norm_num] at hhigh
  change ‖physicalPrimeTail u N k y‖ ≤ H * Z at hhigh
  have hlow : ‖smallPrimeMoment N k y‖ ≤ (N + 1 : ℝ) ^ 2 * Z := norm_smallPrimeMoment_le N k y
  have hE : ‖finiteMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y) -
      ordinaryPrimeMoment k (3 / 2 + Complex.I * y)‖ ≤ ((N + 1 : ℝ) ^ 2 + H) * Z := by
    rw [ordinaryPrimeMoment_eq_actual_split u N k y hNX]
    have he (a b c : ℂ) : a - (b + a + c) = -(b + c) := by ring
    rw [he, norm_neg]
    exact ((norm_add_le _ _).trans (add_le_add hlow hhigh)).trans_eq (by ring)
  have hs := small_product_scalar hu huh N k l hklo hkl
  have hh := upper_product_scalar hu huh N k l hkhi hkl
    (show (4 / 3 : ℝ) * N ≤ SquarefreeVaughanLogSource.length u N by nlinarith [hLN])
  change u ^ (N + 1) * (H * (511 / 1024 : ℝ)⁻¹ ^ l) ≤ R at hh
  change u ^ (N + 1) * (511 / 1024 : ℝ)⁻¹ ^ l ≤ R at hs
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le, norm_mul]
  calc
    _ ≤ u ^ (N + 1) * ((((N + 1 : ℝ) ^ 2 + H) * Z) *
        ((511 / 1024 : ℝ)⁻¹ ^ l * Z)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hE hz (norm_nonneg _) (by dsimp [H]; positivity))
        (pow_nonneg hu.le _)
    _ = ((N + 1 : ℝ) ^ 2 * (u ^ (N + 1) * (511 / 1024 : ℝ)⁻¹ ^ l) +
        u ^ (N + 1) * (H * (511 / 1024 : ℝ)⁻¹ ^ l)) * Z ^ 2 := by ring
    _ ≤ ((N + 1 : ℝ) ^ 2 * R + R) * Z ^ 2 :=
      mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) hh) (sq_nonneg _)
    _ ≤ _ := by
      have hNs : (1 : ℝ) ≤ (N + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
      have hR : 0 ≤ R := by dsimp [R]; positivity
      have hb := mul_le_mul_of_nonneg_right
        (show (N + 1 : ℝ) ^ 2 * R + R ≤ 2 * (N + 1 : ℝ) ^ 2 * R by nlinarith) (sq_nonneg Z)
      dsimp only [R, Z] at hb
      nlinarith only [hb]

/-- The first reflected completion error is independently bounded
with the actual finite complementary prime factor, not an assumed budget. -/
theorem eventually_norm_finite_completion_product {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ k l : ℕ, N ≤ 8 * k → 32 * k ≤ 15 * N + 96 →
      k + l ≤ N + 2 → ∀ (y : ℝ) (A : Finset ℕ),
      ‖(u : ℂ) ^ (N + 1) *
        ((finiteMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y) -
          ordinaryPrimeMoment k (3 / 2 + Complex.I * y)) *
            finiteMoment A l (3 / 2 + Complex.I * y))‖ ≤
        2 * Real.exp 2 * (N + 1 : ℝ) ^ 2 * Real.exp (-(5 / 4096 : ℝ) * N) *
          (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2 := by
  filter_upwards [eventually_norm_completion_product_le hu huh] with N hN
  intro k l hklo hkhi hkl y A
  apply hN k l hklo hkhi hkl y
  simpa only [show (3 / 2 : ℝ) - 511 / 1024 = 1025 / 1024 by norm_num] using
    ZetaRieszPairOrders.norm_finiteMoment_le_euler A l y
      (q := 511 / 1024) (by norm_num) (by norm_num)

/-- The second reflected completion error is independently bounded
with the genuine complete complementary prime series. -/
theorem eventually_norm_complete_completion_product {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ k l : ℕ, N ≤ 8 * k → 32 * k ≤ 15 * N + 96 →
      k + l ≤ N + 2 → ∀ y : ℝ,
      ‖(u : ℂ) ^ (N + 1) *
        ((finiteMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y) -
          ordinaryPrimeMoment k (3 / 2 + Complex.I * y)) *
            ordinaryPrimeMoment l (3 / 2 + Complex.I * y))‖ ≤
        2 * Real.exp 2 * (N + 1 : ℝ) ^ 2 * Real.exp (-(5 / 4096 : ℝ) * N) *
          (∑' n, zetaPrimeExpWeight (1025 / 1024) n) ^ 2 := by
  filter_upwards [eventually_norm_completion_product_le hu huh] with N hN
  intro k l hklo hkhi hkl y
  exact hN k l hklo hkhi hkl y _ (norm_completeMoment_le l y)

end
end RiemannGaussian.ZetaRieszCompletionProduct

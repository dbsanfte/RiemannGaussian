/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairOrders

/-!
# Independent errors for completing the finite prime moment array

These estimates pay actual omitted prime ranges. They retain every
complex moment before taking norms and do not posit prime cancellation.
-/

namespace RiemannGaussian.ZetaRieszPrimeCompletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAnnulusJoint ZetaExposedPrimeMoments

/-- An arbitrary selected moment, retaining the original complex atom. -/
def maskedMoment (Q : ℕ → Prop) (k : ℕ) (y : ℝ) : ℂ :=
  ∑' n, if Q n then zetaPrimeLogKernel k (3 / 2 + Complex.I * y) n else 0

/-- The upper support supplies an independent summable tilted majorant. -/
theorem upper_atom_le (Q : ℕ → Prop) (k : ℕ) (y L : ℝ)
    {q σ : ℝ} (hq : 0 < q) (hgap : 0 ≤ 3 / 2 - q - σ)
    (hQ : ∀ n, Q n → L ≤ Real.log n) (n : ℕ) :
    ‖if Q n then zetaPrimeLogKernel k (3 / 2 + Complex.I * y) n else 0‖ ≤
      (q⁻¹ ^ k * Real.exp (-(3 / 2 - q - σ) * L)) * zetaPrimeExpWeight σ n := by
  by_cases hn : Q n
  · rw [if_pos hn]
    have hb := norm_zetaPrimeLogKernel_le k (3 / 2 + Complex.I * (y : ℂ)) n hq
    have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
    rw [hs] at hb
    have he : zetaPrimeExpWeight (3 / 2 - q) n =
        Real.exp (-(3 / 2 - q - σ) * Real.log n) * zetaPrimeExpWeight σ n := by
      unfold zetaPrimeExpWeight
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at hb
    have hx := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left (hQ n hn) (neg_nonpos.mpr hgap))
    exact hb.trans ((mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le) (by positivity)).trans_eq (by
        unfold zetaPrimeExpWeight
        ring))
  · rw [if_neg hn, norm_zero]
    unfold zetaPrimeExpWeight
    positivity

/-- The selected upper series converges genuinely before any estimate. -/
theorem summable_upper (Q : ℕ → Prop) (k : ℕ) (y L : ℝ)
    {q σ : ℝ} (hq : 0 < q) (hσ : 1 < σ) (hgap : 0 ≤ 3 / 2 - q - σ)
    (hQ : ∀ n, Q n → L ≤ Real.log n) :
    Summable (fun n => if Q n then zetaPrimeLogKernel k (3 / 2 + Complex.I * y) n else 0) := by
  apply ((summable_zetaPrimeExpWeight hσ).mul_left
    (q⁻¹ ^ k * Real.exp (-(3 / 2 - q - σ) * L))).of_norm_bounded
  exact upper_atom_le Q k y L hq hgap hQ

/-- The full infinite upper completion error has an independent norm bound. -/
theorem norm_maskedMoment_upper_le (Q : ℕ → Prop) (k : ℕ) (y L : ℝ)
    {q σ : ℝ} (hq : 0 < q) (hσ : 1 < σ) (hgap : 0 ≤ 3 / 2 - q - σ)
    (hQ : ∀ n, Q n → L ≤ Real.log n) :
    ‖maskedMoment Q k y‖ ≤
      (q⁻¹ ^ k * Real.exp (-(3 / 2 - q - σ) * L)) *
        ∑' n, zetaPrimeExpWeight σ n := by
  have hf := summable_upper Q k y L hq hσ hgap hQ
  have hw := (summable_zetaPrimeExpWeight hσ).mul_left
    (q⁻¹ ^ k * Real.exp (-(3 / 2 - q - σ) * L))
  calc
    _ ≤ ∑' n, ‖if Q n then zetaPrimeLogKernel k (3 / 2 + Complex.I * y) n else 0‖ :=
      norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n, (q⁻¹ ^ k * Real.exp (-(3 / 2 - q - σ) * L)) *
        zetaPrimeExpWeight σ n := hf.norm.tsum_le_tsum (upper_atom_le Q k y L hq hgap hQ) hw
    _ = _ := tsum_mul_left

/-- A rational logarithm bound already used by the physical upper tail. -/
theorem log_eight_thirds_le : Real.log (8 / 3 : ℝ) ≤ 95 / 96 := by
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num, Nat.cast_ofNat] using
      (Real.log_pow (2 : ℝ) (3 : ℕ))
  rw [Real.log_div (by norm_num) (by norm_num), hlog8]
  linarith [Real.log_two_lt_d9, Real.log_three_gt_d9]

/-- The physical upper tail is geometrically small through a little
more than half of the original factorial order. -/
theorem upper_completion_scalar {u L : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) (N k : ℕ)
    (hk : 128 * k ≤ 65 * N) (hL : (4 / 3 : ℝ) * N ≤ L) :
    u ^ k * ((3 / 8 : ℝ)⁻¹ ^ k * Real.exp (-(127 / 1024 : ℝ) * L)) ≤
      Real.exp (-(17 / 12288 : ℝ) * N) := by
  have hlogu : Real.log u ≤ -(2 / 3 : ℝ) := by
    simpa only [Real.log_exp] using (Real.log_lt_log hu huh).le
  have hpow (x : ℝ) (hx : 0 < x) (n : ℕ) : x ^ n = Real.exp ((n : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  have hku := mul_le_mul_of_nonneg_left hlogu (Nat.cast_nonneg (α := ℝ) k)
  have hkq := mul_le_mul_of_nonneg_left log_eight_thirds_le (Nat.cast_nonneg (α := ℝ) k)
  have hkc : 128 * (k : ℝ) ≤ 65 * N := by exact_mod_cast hk
  have hexp : (k : ℝ) * Real.log u + k * Real.log (8 / 3 : ℝ) -
      (127 / 1024 : ℝ) * L ≤ -(17 / 12288 : ℝ) * N := by nlinarith
  rw [show (3 / 8 : ℝ)⁻¹ = 8 / 3 by norm_num, hpow u hu k,
    hpow (8 / 3) (by norm_num) k, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The actual omitted primes above the literal physical cutoff. -/
def physicalPrimeTail (u : ℝ) (N k : ℕ) (y : ℝ) : ℂ :=
  maskedMoment (fun p => p.Prime ∧
    (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p) k y

/-- At the actual floor, every omitted upper prime has the original
physical logarithmic length, with no rounding replacement. -/
theorem physicalPrimeTail_log_support (u : ℝ) (N p : ℕ)
    (hp : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p) :
    SquarefreeVaughanLogSource.length u N ≤ Real.log p := by
  have hb : (0 : ℝ) < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ^ 2 := by positivity
  have hc : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ^ 2 ≤ (p : ℝ) := by
    exact_mod_cast hp
  exact Real.log_le_log hb hc

/-- An independent, height-uniform bound for the genuine infinite
upper-prime completion error through order sixty-five over one hundred
twenty-eight of the physical order. The small-prime error is separate. -/
theorem eventually_norm_physicalPrimeTail_le {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 128 * k ≤ 65 * N → ∀ y : ℝ,
      ‖(u : ℂ) ^ k * physicalPrimeTail u N k y‖ ≤
        Real.exp (-(17 / 12288 : ℝ) * N) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by
  filter_upwards [ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
    (by norm_num : (0 : ℝ) ≤ 2 / 3) huh] with N hLN
  intro k hk y
  have hb := norm_maskedMoment_upper_le (fun p => p.Prime ∧
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p)
    k y (SquarefreeVaughanLogSource.length u N) (q := 3 / 8) (σ := 1025 / 1024)
    (by norm_num) (by norm_num) (by norm_num)
    (fun p hp => physicalPrimeTail_log_support u N p hp.2)
  rw [show (3 / 2 : ℝ) - 3 / 8 - 1025 / 1024 = 127 / 1024 by norm_num] at hb
  have hs := upper_completion_scalar (L := SquarefreeVaughanLogSource.length u N)
    hu huh N k hk (by nlinarith [hLN])
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ k * (((3 / 8 : ℝ)⁻¹ ^ k * Real.exp (-(127 / 1024 : ℝ) *
        SquarefreeVaughanLogSource.length u N)) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hu.le _)
    _ = (u ^ k * ((3 / 8 : ℝ)⁻¹ ^ k * Real.exp (-(127 / 1024 : ℝ) *
        SquarefreeVaughanLogSource.length u N))) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (tsum_nonneg (fun _ => (Real.exp_pos _).le))

/-- The original polynomial prime prefix eventually lies below every
factorial order at least one third of the physical order. -/
theorem eventually_small_prime_log_le_order :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 3 * k → ∀ p : ℕ,
      p ∈ Nat.primesLE (N ^ 2) → Real.log p ≤ k := by
  have hl : Tendsto (fun N : ℕ => Real.log N / ((N : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [Function.comp_def, pow_zero, pow_one, one_mul] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 1 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hl.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 12)),
    eventually_ge_atTop 1] with N hlog hN
  intro k hk p hp
  obtain ⟨hpN, hprime⟩ := Nat.mem_primesLE.mp hp
  have hc : (p : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hpN
  have hplog := Real.log_le_log (by exact_mod_cast hprime.pos : (0 : ℝ) < p) hc
  rw [Real.log_pow] at hplog
  have hln : Real.log N < (1 / 12 : ℝ) * (N + 1) :=
    (div_lt_iff₀ (by positivity)).mp hlog
  have hNc : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hkc : (N : ℝ) ≤ 3 * k := by exact_mod_cast hk
  norm_num only [Nat.cast_ofNat] at hplog
  nlinarith

/-- The small finite moment has a strict independent geometric envelope
when its support is below its own factorial order. -/
theorem norm_small_finiteMoment_le (A : Finset ℕ) (k : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hA : ∀ a ∈ A, Real.log a ≤ k) :
    ‖(u : ℂ) ^ k * ZetaRieszPrimePairConvolution.finiteMoment A k
      (3 / 2 + Complex.I * y)‖ ≤ Real.exp (-(95 / 1024 : ℝ) * k) *
        ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by
  have hb := ZetaRieszPairOrders.norm_finiteMoment_le_tilt A k y k
    (q := 2 / 3) (σ := 1025 / 1024) (by norm_num) (by norm_num) (by norm_num) hA
  rw [show (2 / 3 : ℝ) + 1025 / 1024 - 3 / 2 = 515 / 3072 by norm_num] at hb
  have hlogu : Real.log u ≤ -(2 / 3 : ℝ) := by
    simpa only [Real.log_exp] using (Real.log_lt_log hu huh).le
  have hlogq : Real.log (3 / 2 : ℝ) ≤ 13 / 32 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  have hs : u ^ k * ((2 / 3 : ℝ)⁻¹ ^ k * Real.exp ((515 / 3072 : ℝ) * k)) ≤
      Real.exp (-(95 / 1024 : ℝ) * k) := by
    have hpow (x : ℝ) (hx : 0 < x) : x ^ k = Real.exp ((k : ℝ) * Real.log x) := by
      rw [Real.exp_nat_mul, Real.exp_log hx]
    rw [show (2 / 3 : ℝ)⁻¹ = 3 / 2 by norm_num, hpow u hu,
      hpow (3 / 2) (by norm_num), ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha := mul_le_mul_of_nonneg_left hlogu (Nat.cast_nonneg (α := ℝ) k)
    have hq := mul_le_mul_of_nonneg_left hlogq (Nat.cast_nonneg (α := ℝ) k)
    nlinarith
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  exact ((mul_le_mul_of_nonneg_left hb (pow_nonneg hu.le k)).trans_eq (mul_assoc _ _ _).symm).trans
    (mul_le_mul_of_nonneg_right hs (tsum_nonneg (fun _ => (Real.exp_pos _).le)))

/-- The small primes omitted from the actual intermediate prime set. -/
def smallPrimeMoment (N k : ℕ) (y : ℝ) : ℂ :=
  ZetaRieszPrimePairConvolution.finiteMoment (Nat.primesLE (N ^ 2)) k (3 / 2 + Complex.I * y)

/-- Every omitted small prime is paid uniformly over all moving orders
at least N/3 and all ordinates. No exposed zero is assumed. -/
theorem eventually_norm_smallPrimeMoment_le {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 3 * k → ∀ y : ℝ,
      ‖(u : ℂ) ^ k * smallPrimeMoment N k y‖ ≤
        Real.exp (-(95 / 3072 : ℝ) * N) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by
  filter_upwards [eventually_small_prime_log_le_order] with N hN
  intro k hk y
  have hb := norm_small_finiteMoment_le (Nat.primesLE (N ^ 2)) k y hu huh (hN k hk)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (tsum_nonneg (fun _ => (Real.exp_pos _).le))
  apply Real.exp_le_exp.mpr
  have hc : (N : ℝ) ≤ 3 * k := by exact_mod_cast hk
  nlinarith

/-- Every finite moment is the genuine sum of its selected complex atoms. -/
theorem hasSum_finiteMoment (A : Finset ℕ) (k : ℕ) (y : ℝ) :
    HasSum (fun p => if p ∈ A then zetaPrimeLogKernel k (3 / 2 + Complex.I * y) p else 0)
      (ZetaRieszPrimePairConvolution.finiteMoment A k (3 / 2 + Complex.I * y)) := by
  have h : HasSum (fun p => if p ∈ A then zetaPrimeLogKernel k (3 / 2 + Complex.I * y) p else 0)
      (∑ p ∈ A, if p ∈ A then zetaPrimeLogKernel k (3 / 2 + Complex.I * y) p else 0) :=
    hasSum_sum_of_ne_finset_zero (s := A) (by intro p hp; exact if_neg hp)
  convert h using 1
  exact (Finset.sum_congr rfl (fun p hp => if_pos hp)).symm

/-- The entire prime series splits at both actual endpoints. No prime
mask is completed before its two exact omitted pieces are recorded. -/
theorem ordinaryPrimeMoment_eq_actual_split (u : ℝ) (N k : ℕ) (y : ℝ)
    (hNX : N ^ 2 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ordinaryPrimeMoment k (3 / 2 + Complex.I * y) = smallPrimeMoment N k y +
      ZetaRieszPrimePairConvolution.finiteMoment (intermediatePrimes u N) k
        (3 / 2 + Complex.I * y) + physicalPrimeTail u N k y := by
  have ht := (summable_upper (fun p => p.Prime ∧
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p)
    k y (SquarefreeVaughanLogSource.length u N) (q := 3 / 8) (σ := 1025 / 1024)
    (by norm_num) (by norm_num) (by norm_num)
    (fun p hp => physicalPrimeTail_log_support u N p hp.2)).hasSum
  have hs := ((hasSum_finiteMoment (Nat.primesLE (N ^ 2)) k y).add
    (hasSum_finiteMoment (intermediatePrimes u N) k y)).add ht
  have hf : HasSum (fun p => if p.Prime then zetaPrimeLogKernel k (3 / 2 + Complex.I * y) p else 0)
      (smallPrimeMoment N k y + ZetaRieszPrimePairConvolution.finiteMoment
        (intermediatePrimes u N) k (3 / 2 + Complex.I * y) + physicalPrimeTail u N k y) := by
    apply hs.congr_fun
    intro p
    simp only [Nat.mem_primesLE, mem_intermediatePrimes]
    by_cases hp : p.Prime
    · by_cases hpN : p ≤ N ^ 2
      · have hn : ¬ N ^ 2 < p := by omega
        have hx : ¬ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p := by omega
        simp [hp, hpN, hn, hx]
      · have hn : N ^ 2 < p := by omega
        by_cases hpX : p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2
        · have hx : ¬ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p := by omega
          simp [hp, hpN, hn, hpX, hx]
        · have hx : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p := by omega
          simp [hp, hpN, hn, hpX, hx]
    · simp [hp]
  exact (summable_ordinaryPrimeMoment (by norm_num) k).hasSum.unique hf

/-- Both omitted prime ranges are now independently paid. The finite
array is uniformly close to its complete prime array on this moving
middle-order band, with the literal physical cutoff and every phase. -/
theorem eventually_norm_finite_sub_complete_le {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 3 * k → 128 * k ≤ 65 * N → ∀ y : ℝ,
      ‖(u : ℂ) ^ k * (ZetaRieszPrimePairConvolution.finiteMoment (intermediatePrimes u N) k
        (3 / 2 + Complex.I * y) - ordinaryPrimeMoment k (3 / 2 + Complex.I * y))‖ ≤
          2 * Real.exp (-(17 / 12288 : ℝ) * N) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by
  have hu1 : u < 1 := huh.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  filter_upwards [eventually_norm_physicalPrimeTail_le hu huh,
    eventually_norm_smallPrimeMoment_le hu huh,
    ZetaRieszSemiprimeSupport.eventually_quadratic_head_lt_physical hu hu1] with N hhigh hlow hNX
  intro k hklo hkhi y
  rw [ordinaryPrimeMoment_eq_actual_split u N k y hNX]
  have he (a b c : ℂ) : a - (b + a + c) = -(b + c) := by ring
  rw [he, mul_neg, norm_neg, mul_add]
  have hZ : 0 ≤ ∑' n, zetaPrimeExpWeight (1025 / 1024) n :=
    tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have helo : Real.exp (-(95 / 3072 : ℝ) * N) ≤ Real.exp (-(17 / 12288 : ℝ) * N) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  calc
    _ ≤ ‖(u : ℂ) ^ k * smallPrimeMoment N k y‖ + ‖(u : ℂ) ^ k * physicalPrimeTail u N k y‖ :=
      norm_add_le _ _
    _ ≤ Real.exp (-(95 / 3072 : ℝ) * N) * (∑' n, zetaPrimeExpWeight (1025 / 1024) n) +
        Real.exp (-(17 / 12288 : ℝ) * N) * ∑' n, zetaPrimeExpWeight (1025 / 1024) n :=
      add_le_add (hlow k hklo y) (hhigh k hkhi y)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right helo hZ]

/-- The actual completion error tends to zero for every moving order
inside the proved band and every moving ordinate. This is not restricted
to a fixed finite moment or a numerically selected frequency family. -/
theorem tendsto_finite_sub_complete (k : ℕ → ℕ) (y : ℕ → ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hk : ∀ᶠ N : ℕ in atTop, N ≤ 3 * k N ∧ 128 * k N ≤ 65 * N) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ k N *
      (ZetaRieszPrimePairConvolution.finiteMoment (intermediatePrimes u N) (k N)
        (3 / 2 + Complex.I * y N) - ordinaryPrimeMoment (k N) (3 / 2 + Complex.I * y N)))
        atTop (nhds 0) := by
  apply squeeze_zero_norm' (by
    filter_upwards [eventually_norm_finite_sub_complete_le hu huh, hk] with N hN hkN
    exact hN (k N) hkN.1 hkN.2 (y N))
  have hr0 : 0 ≤ Real.exp (-(17 / 12288 : ℝ)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(17 / 12288 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul
    (2 * ∑' n, zetaPrimeExpWeight (1025 / 1024) n)
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [show -(17 / 12288 : ℝ) * N = (N : ℝ) * -(17 / 12288) by ring, Real.exp_nat_mul]
  ring

end
end RiemannGaussian.ZetaRieszPrimeCompletion

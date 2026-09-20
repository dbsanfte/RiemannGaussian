/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCofactorBoundary

/-!
# Paying the prime prefix and repeated-prime corrections

Restoring the original tapered wing requires its clipped physical
prime prefix and the diagonal excluded by coprimality. Both complete
corrections have height-uniform geometric bounds with the original
endpoint weights and unpaid factorial orders.
-/

namespace RiemannGaussian.ZetaRieszJointCofactor
noncomputable section
open Complex Filter Topology
open scoped Classical BigOperators ArithmeticFunction.Moebius

/-- The exact clipped-prime-prefix correction, including its physical ramp,
coprimality and both factorial kernels. -/
def prefixAtom (L y : ℝ) (k l p a : ℕ) : ℂ :=
  if a.Prime ∧ ¬p ∣ a then
    ((max 0 (L - Real.log p - Real.log a) : ℝ) : ℂ) *
      zetaPrimeLogKernel k (3 / 2 + I * y) a * zetaPrimeLogKernel l (3 / 2 + I * y) p
  else 0

/-- The physical product cutoff pays every prefix atom with a positive summable two-
factor majorant, uniformly in height. -/
theorem prefix_atom_bound (y : ℝ) (k l p a : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ‖prefixAtom L y k l p a‖ ≤
      (L * (10 / 7 : ℝ) ^ (k + l) * Real.exp ((21 / 100 : ℝ) * L) *
        zetaPrimeExpWeight (101 / 100) p) * zetaPrimeExpWeight (101 / 100) a := by
  have hpa : 0 ≤ zetaPrimeExpWeight (101 / 100) p := (Real.exp_pos _).le
  have haa : 0 ≤ zetaPrimeExpWeight (101 / 100) a := (Real.exp_pos _).le
  by_cases hgood : a.Prime ∧ ¬p ∣ a
  · rw [prefixAtom, if_pos hgood]
    by_cases hlog : L ≤ Real.log p + Real.log a
    · rw [max_eq_left (by linarith), Complex.ofReal_zero, zero_mul, zero_mul, norm_zero]
      positivity
    have hlogp := Real.log_natCast_nonneg p
    have hloga := Real.log_natCast_nonneg a
    have hmax : max 0 (L - Real.log p - Real.log a) ≤ L :=
      max_le hL (by linarith)
    have hk := norm_zetaPrimeLogKernel_le k (3 / 2 + I * (y : ℂ)) a
      (q := 7 / 10) (by norm_num)
    have hl := norm_zetaPrimeLogKernel_le l (3 / 2 + I * (y : ℂ)) p
      (q := 7 / 10) (by norm_num)
    norm_num at hk hl
    have hex : zetaPrimeExpWeight (4 / 5) a * zetaPrimeExpWeight (4 / 5) p ≤
        Real.exp ((21 / 100 : ℝ) * L) *
          zetaPrimeExpWeight (101 / 100) p * zetaPrimeExpWeight (101 / 100) a := by
      unfold zetaPrimeExpWeight
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_max_left 0 _)]
    calc
      _ ≤ L * ((10 / 7 : ℝ) ^ k * zetaPrimeExpWeight (4 / 5) a) *
          ((10 / 7 : ℝ) ^ l * zetaPrimeExpWeight (4 / 5) p) := by
        have ha0 : 0 ≤ zetaPrimeExpWeight (4 / 5) a := (Real.exp_pos _).le
        have hp0 : 0 ≤ zetaPrimeExpWeight (4 / 5) p := (Real.exp_pos _).le
        gcongr
      _ = (L * (10 / 7 : ℝ) ^ (k + l)) *
          (zetaPrimeExpWeight (4 / 5) a * zetaPrimeExpWeight (4 / 5) p) := by rw [pow_add]; ring
      _ ≤ (L * (10 / 7 : ℝ) ^ (k + l)) *
          (Real.exp ((21 / 100 : ℝ) * L) *
            zetaPrimeExpWeight (101 / 100) p * zetaPrimeExpWeight (101 / 100) a) :=
        mul_le_mul_of_nonneg_left hex (by positivity)
      _ = _ := by ring
  · rw [prefixAtom, if_neg hgood, norm_zero]
    positivity

/-- The full clipped prime prefix, summed over the actual finite distinguished-prime
selection and all cofactors. -/
def prefixBlock (A : Finset ℕ) (L y : ℝ) (k l : ℕ) : ℂ :=
  ∑ p ∈ A, ∑' a, prefixAtom L y k l p a

/-- Both prime factors of the entire clipped prefix have a common height-uniform
bound with no invented cutoff or prime-count cost. -/
theorem norm_prefixBlock_le (A : Finset ℕ) (k l : ℕ) (y : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ‖prefixBlock A L y k l‖ ≤
      (∑' n, zetaPrimeExpWeight (101 / 100) n) ^ 2 *
        (L * (10 / 7 : ℝ) ^ (k + l) * Real.exp ((21 / 100 : ℝ) * L)) := by
  let Z := ∑' n, zetaPrimeExpWeight (101 / 100) n
  let B := L * (10 / 7 : ℝ) ^ (k + l) * Real.exp ((21 / 100 : ℝ) * L)
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hmass := summable_zetaPrimeExpWeight (by norm_num : (1 : ℝ) < 101 / 100)
  have ht (p : ℕ) : ‖∑' a, prefixAtom L y k l p a‖ ≤ B * zetaPrimeExpWeight (101 / 100) p * Z := by
    have hs := hmass.mul_left (B * zetaPrimeExpWeight (101 / 100) p)
    have hf : Summable (fun a => ‖prefixAtom L y k l p a‖) :=
      hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => prefix_atom_bound y k l p a hL)
    apply (norm_tsum_le_tsum_norm hf).trans
    apply (hf.tsum_le_tsum (fun a => prefix_atom_bound y k l p a hL) hs).trans_eq
    exact tsum_mul_left
  calc
    _ ≤ ∑ p ∈ A, ‖∑' a, prefixAtom L y k l p a‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ A, B * zetaPrimeExpWeight (101 / 100) p * Z := Finset.sum_le_sum (fun p _ => ht p)
    _ = B * Z * ∑ p ∈ A, zetaPrimeExpWeight (101 / 100) p := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ B * Z * Z := mul_le_mul_of_nonneg_left
      (hmass.sum_le_tsum A (fun _ _ => (Real.exp_pos _).le)) (by positivity)
    _ = _ := by ring

/-- The clipped-prefix allowance has geometric decay at the original source scale. -/
theorem prefix_source_scalar {u L : ℝ} (hu : 0 < u)
    (huh : u ≤ Real.exp (-(2 / 3 : ℝ))) (N : ℕ)
    (hL : L ≤ (139 / 100 : ℝ) * N) :
    u ^ N * (10 / 7 : ℝ) ^ N * Real.exp ((21 / 100 : ℝ) * L) ≤
      Real.exp (-(N : ℝ) / 64) := by
  have hlu : Real.log u ≤ -(2 / 3 : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log hu huh
  have hlq : Real.log (10 / 7 : ℝ) ≤ 357 / 1000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 357 / 1000) 7
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hpow (x : ℝ) (hx : 0 < x) : x ^ N = Real.exp ((N : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  rw [hpow u hu, hpow (10 / 7) (by norm_num), ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_left hlu (Nat.cast_nonneg (α := ℝ) N)
  have h2 := mul_le_mul_of_nonneg_left hlq (Nat.cast_nonneg (α := ℝ) N)
  nlinarith [Nat.cast_nonneg (α := ℝ) N]


private theorem unpaid_card_le (N : ℕ) :
    ((ZetaRieszWingHighOrders.unpaidOrders N).card : ℝ) ≤ 2 * (N + 1 : ℝ) := by
  have hs : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N + 2) := by
    intro k hk
    have hkM := (ZetaRieszReflectedCompletion.lowerWing_bounds
      (ZetaRieszWingHighOrders.unpaidOrders_support hk).1).2.2
    exact Finset.mem_range.mpr (by omega)
  have hc : (ZetaRieszWingHighOrders.unpaidOrders N).card ≤ N + 2 := by
    simpa using Finset.card_le_card hs
  have hc' : ((ZetaRieszWingHighOrders.unpaidOrders N).card : ℝ) ≤ N + 2 := by exact_mod_cast hc
  linarith [Nat.cast_nonneg (α := ℝ) N]

private theorem normalized_order_sum_bound (N : ℕ) (v : ℕ → ℂ)
    {u L C E : ℝ} (hL : 0 < L) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hv : ∀ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      ‖(u : ℂ) ^ (N + 1) * v k‖ ≤ C * L * E) :
    ‖(u : ℂ) ^ (N + 1) * (((N + 1 : ℕ) : ℂ) / (L : ℂ) *
      ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, v k)‖ ≤
        2 * C * (N + 1 : ℝ) ^ 2 * E := by
  rw [mul_left_comm, Finset.mul_sum, norm_mul, norm_div, Complex.norm_natCast,
    Complex.norm_real, Real.norm_of_nonneg hL.le]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hb : ‖∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, (u : ℂ) ^ (N + 1) * v k‖ ≤
      (2 * (N + 1 : ℝ)) * (C * L * E) := by
    apply (norm_sum_le _ _).trans
    have h := Finset.sum_le_sum hv
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right (unpaid_card_le N) (by positivity))
  apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (N + 1 : ℝ) / L)).trans_eq
  field_simp

/-- The entire clipped-prefix correction on the original unpaid order set and
physical prime family. -/
def prefixWing (u y : ℝ) (N : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
    ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      prefixBlock (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k)

/-- The full normalized prefix correction has an explicit quadratic-times-
exponential bound, uniformly in height and source radius. -/
theorem norm_prefixWing_le {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u ≤ Real.exp (-(2 / 3 : ℝ))) {N : ℕ} (hN : 2 ≤ N) (y : ℝ) :
    ‖(u : ℂ) ^ (N + 1) * prefixWing u y N‖ ≤
      (2 * (∑' n, zetaPrimeExpWeight (101 / 100) n) ^ 2) *
        (N + 1 : ℝ) ^ 2 * Real.exp (-(N + 1 : ℝ) / 64) := by
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let Z := ∑' n, zetaPrimeExpWeight (101 / 100) n
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  have hu0 : 0 < u := by linarith
  have hLL : L ≤ (139 / 100 : ℝ) * (N + 1) := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu hN
    have hl : 2 * Real.log 2 ≤ (139 / 100 : ℝ) := by linarith [Real.log_two_lt_d9]
    have h' := h.trans (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg (α := ℝ) N))
    dsimp only [L]
    linarith
  apply normalized_order_sum_bound N _ hL (sq_nonneg Z) (Real.exp_pos _).le
  intro k hk
  have hkM := (ZetaRieszReflectedCompletion.lowerWing_bounds
    (ZetaRieszWingHighOrders.unpaidOrders_support hk).1).2.2
  have hb := norm_prefixBlock_le A k (N + 1 - k) y hL.le
  rw [Nat.add_sub_of_le hkM] at hb
  have hr := prefix_source_scalar hu0 huh (N + 1) (by exact_mod_cast hLL)
  norm_num only [Nat.cast_add, Nat.cast_one] at hr
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le]
  calc
    _ ≤ u ^ (N + 1) * (Z ^ 2 * (L * (10 / 7 : ℝ) ^ (N + 1) * Real.exp ((21 / 100 : ℝ) * L))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (Z ^ 2 * L) * (u ^ (N + 1) * (10 / 7 : ℝ) ^ (N + 1) * Real.exp ((21 / 100 : ℝ) * L)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)

/-- The repeated-prime correction omitted by cofactor coprimality, retaining the
original endpoint weight and both orders. -/
def diagonalBlock (A : Finset ℕ) (L y : ℝ) (k l : ℕ) : ℂ :=
  ∑ p ∈ A, ((L - Real.log p : ℝ) : ℂ) *
    zetaPrimeLogKernel k (3 / 2 + I * y) p * zetaPrimeLogKernel l (3 / 2 + I * y) p

/-- The repeated-prime block is paid by a convergent prime-square mass, uniformly in
the finite prime selection and height. -/
theorem norm_diagonalBlock_le (A : Finset ℕ) (k l : ℕ) (y : ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hA : ∀ p ∈ A, Real.log p ≤ L) :
    ‖diagonalBlock A L y k l‖ ≤
      (∑' n, zetaPrimeExpWeight (3 / 2) n) * (L * (4 / 3 : ℝ) ^ (k + l)) := by
  have ht (p : ℕ) (hp : p ∈ A) :
      ‖((L - Real.log p : ℝ) : ℂ) *
        zetaPrimeLogKernel k (3 / 2 + I * y) p * zetaPrimeLogKernel l (3 / 2 + I * y) p‖ ≤
          (L * (4 / 3 : ℝ) ^ (k + l)) * zetaPrimeExpWeight (3 / 2) p := by
    have hk := norm_zetaPrimeLogKernel_le k (3 / 2 + I * (y : ℂ)) p (q := 3 / 4) (by norm_num)
    have hl := norm_zetaPrimeLogKernel_le l (3 / 2 + I * (y : ℂ)) p (q := 3 / 4) (by norm_num)
    norm_num at hk hl
    have hw : 0 ≤ zetaPrimeExpWeight (3 / 4) p := (Real.exp_pos _).le
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (hA p hp))]
    calc
      _ ≤ L * ((4 / 3 : ℝ) ^ k * zetaPrimeExpWeight (3 / 4) p) *
          ((4 / 3 : ℝ) ^ l * zetaPrimeExpWeight (3 / 4) p) := by
        have hLp : L - Real.log p ≤ L := sub_le_self _ (Real.log_natCast_nonneg p)
        gcongr
      _ = _ := by
        have he : zetaPrimeExpWeight (3 / 4) p * zetaPrimeExpWeight (3 / 4) p =
            zetaPrimeExpWeight (3 / 2) p := by
          unfold zetaPrimeExpWeight
          rw [← Real.exp_add]
          congr 1
          ring
        rw [pow_add]
        linear_combination (L * (4 / 3 : ℝ) ^ k * (4 / 3 : ℝ) ^ l) * he
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum ht).trans
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left
    ((summable_zetaPrimeExpWeight (by norm_num : (1 : ℝ) < 3 / 2)).sum_le_tsum A
      (fun _ _ => (Real.exp_pos _).le)) (by positivity)).trans_eq (mul_comm _ _)

/-- The complete repeated-prime correction on the original unpaid orders and
intermediate primes. -/
def diagonalWing (u y : ℝ) (N : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
    ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      diagonalBlock (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k)

/-- The normalized repeated-prime correction decays geometrically, uniformly in
height throughout the harmonic source interval. -/
theorem norm_diagonalWing_le {u : ℝ} (hu : 0 < u)
    (huh : u ≤ Real.exp (-(2 / 3 : ℝ))) (N : ℕ) (y : ℝ) :
    ‖(u : ℂ) ^ (N + 1) * diagonalWing u y N‖ ≤
      (2 * ∑' n, zetaPrimeExpWeight (3 / 2) n) *
        (N + 1 : ℝ) ^ 2 * Real.exp (-(N + 1 : ℝ) / 64) := by
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let Z := ∑' n, zetaPrimeExpWeight (3 / 2) n
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  apply normalized_order_sum_bound N _ hL hZ (Real.exp_pos _).le
  intro k hk
  have hkM := (ZetaRieszReflectedCompletion.lowerWing_bounds
    (ZetaRieszWingHighOrders.unpaidOrders_support hk).1).2.2
  have hb := norm_diagonalBlock_le A k (N + 1 - k) y hL.le (by
    intro p hp
    obtain ⟨hprime, _, hpX⟩ := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hp
    exact (Real.log_lt_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpX)).le)
  rw [Nat.add_sub_of_le hkM] at hb
  have hr := joint_source_scalar (L := 0) hu huh (N + 1) (by positivity)
  norm_num only [mul_zero, Real.exp_zero, mul_one, Nat.cast_add, Nat.cast_one] at hr
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (Z * (L * (4 / 3 : ℝ) ^ (N + 1))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (Z * L) * (u ^ (N + 1) * (4 / 3 : ℝ) ^ (N + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)

end
end RiemannGaussian.ZetaRieszJointCofactor

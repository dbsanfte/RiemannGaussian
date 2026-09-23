/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWideOwnerAudit

/-!
# The actual completion cost of the concrete wide-owner test

Completing the composite cofactor restores a tapered prime product.  The
owned finite carrier is not identified with this completion: its difference
keeps the owner condition, original allocation and original window masks.
-/

namespace RiemannGaussian.ZetaRieszWideOwnerAudit
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeCompletion ZetaRieszPrimeCompletionRate
open ZetaRieszPrimePairConvolution ZetaRieszAnnulusJoint ZetaExposedPrimeMoments
open ZetaRieszJointCofactor ZetaRieszWingReserve ZetaRieszMatchedMiddle

/-- Retaining complementary orders leaves a strict completion margin even
after the full other moment is included. -/
theorem wide_product_scalar {u L : ℝ} (hu : 0 < u) (huU : u ≤ radiusCeiling)
    (N k : ℕ) (hk : 40 * k ≤ 27 * N) (hkM : k ≤ N + 1)
    (hL : (11 / 8 : ℝ) * N ≤ L) :
    u ^ (N + 1) * (27 / 55 : ℝ)⁻¹ ^ k *
        (131071 / 262144 : ℝ)⁻¹ ^ (N + 1 - k) *
        Real.exp (-(3 / 2 - 27 / 55 - (1 + 1 / 262144) : ℝ) * L) ≤
      Real.exp (1 - (N : ℝ) / 200000) := by
  have hlogu : Real.log (u / (131071 / 262144 : ℝ)) ≤ 108 / 1000000 := by
    apply (Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_right huU (by norm_num))).trans
    apply (Real.log_le_iff_le_exp (by norm_num [radiusCeiling])).mpr
    have h := Real.add_one_le_exp (108 / 1000000 : ℝ)
    norm_num [radiusCeiling] at h ⊢
    linarith
  have hlogq : Real.log ((131071 / 262144 : ℝ) / (27 / 55)) ≤ 183416 / 10000000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 183416 / 10000000) 4
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have he : u ^ (N + 1) * (27 / 55 : ℝ)⁻¹ ^ k *
      (131071 / 262144 : ℝ)⁻¹ ^ (N + 1 - k) =
      (u / (131071 / 262144 : ℝ)) ^ (N + 1) *
        ((131071 / 262144 : ℝ) / (27 / 55)) ^ k := by
    have hp : (131071 / 262144 : ℝ)⁻¹ ^ (N + 1) =
        (131071 / 262144 : ℝ)⁻¹ ^ k * (131071 / 262144 : ℝ)⁻¹ ^ (N + 1 - k) := by
      rw [← pow_add, Nat.add_sub_of_le hkM]
    rw [div_eq_mul_inv u, mul_pow, hp,
      show (27 / 55 : ℝ)⁻¹ = (131071 / 262144 : ℝ)⁻¹ *
        ((131071 / 262144 : ℝ) / (27 / 55)) by norm_num, mul_pow]
    ring
  rw [he]
  have hpow (x : ℝ) (hx : 0 < x) (m : ℕ) :
      x ^ m = Real.exp ((m : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  rw [hpow _ (by positivity), hpow _ (by norm_num), ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_left hlogu (Nat.cast_nonneg (α := ℝ) (N + 1))
  have h2 := mul_le_mul_of_nonneg_left hlogq (Nat.cast_nonneg (α := ℝ) k)
  have hkc : 40 * (k : ℝ) ≤ 27 * N := by exact_mod_cast hk
  push_cast at h1 ⊢
  nlinarith only [h1, h2, hkc, hL, Nat.cast_nonneg (α := ℝ) N]

private theorem wide_boundary_atom (p a k : ℕ) (y : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ‖boundaryCoefficient p L a * zetaPrimeLogKernel k (3 / 2 + I * y) a‖ ≤
      (L * (27 / 55 : ℝ)⁻¹ ^ k *
        Real.exp (-(3 / 2 - 27 / 55 - (1 + 1 / 262144) : ℝ) * L)) *
        ((a.divisors.card : ℝ) ^ 2 * (a : ℝ) ^ (-(1 + 1 / 262144 : ℝ))) := by
  by_cases haL : Real.log (a : ℝ) ≤ L
  · rw [boundaryCoefficient_eq_zero haL, zero_mul, norm_zero]
    positivity
  by_cases ha : Squarefree a ∧ a ≠ 1 ∧ ¬a.Prime ∧ ¬p ∣ a
  · have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha.1.ne_zero
    have hc : (a.divisors.card : ℝ) ≤ (a.divisors.card : ℝ) ^ 2 := by
      have hcard : 1 ≤ a.divisors.card := Finset.one_le_card.mpr
        ⟨1, Nat.one_mem_divisors.mpr ha.1.ne_zero⟩
      have hc' : (1 : ℝ) ≤ a.divisors.card := by exact_mod_cast hcard
      nlinarith
    have hk := upper_atom_le (fun n => L < Real.log n) k y L
      (q := 27 / 55) (σ := 1 + 1 / 262144) (by norm_num) (by norm_num)
      (fun _ hn => hn.le) a
    rw [if_pos (lt_of_not_ge haL)] at hk
    have hw : zetaPrimeExpWeight (1 + 1 / 262144) a =
        (a : ℝ) ^ (-(1 + 1 / 262144 : ℝ)) := by
      rw [zetaPrimeExpWeight, Real.rpow_def_of_pos ha0]
      congr 1
      ring
    rw [hw] at hk
    rw [boundaryCoefficient, if_pos ha, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (L * (a.divisors.card : ℝ) ^ 2) *
          (((27 / 55 : ℝ)⁻¹ ^ k *
            Real.exp (-(3 / 2 - 27 / 55 - (1 + 1 / 262144) : ℝ) * L)) *
              (a : ℝ) ^ (-(1 + 1 / 262144 : ℝ))) :=
        mul_le_mul ((abs_riesz_le hL a).trans (mul_le_mul_of_nonneg_left hc hL))
          hk (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · simp only [boundaryCoefficient, if_neg ha, zero_mul, norm_zero]
    positivity

private theorem wide_boundary_response (p k : ℕ) (y : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ‖boundaryResponse p L k (3 / 2 + I * y)‖ ≤
      L * (27 / 55 : ℝ)⁻¹ ^ k *
        Real.exp (-(3 / 2 - 27 / 55 - (1 + 1 / 262144) : ℝ) * L) *
          divisorSquareDirichletMass (1 + 1 / 262144) := by
  let B := L * (27 / 55 : ℝ)⁻¹ ^ k *
    Real.exp (-(3 / 2 - 27 / 55 - (1 + 1 / 262144) : ℝ) * L)
  have hs := (summable_card_divisors_sq_mul_rpow_neg
    (by norm_num : (1 : ℝ) < 1 + 1 / 262144)).mul_left B
  have hf : Summable (fun a =>
      ‖boundaryCoefficient p L a * zetaPrimeLogKernel k (3 / 2 + I * y) a‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => wide_boundary_atom p a k y hL)
  apply (norm_tsum_le_tsum_norm hf).trans
  exact (hf.tsum_le_tsum (fun a => wide_boundary_atom p a k y hL) hs).trans_eq tsum_mul_left

private theorem wide_boundary_block (A : Finset ℕ) (k l : ℕ) (y : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ‖boundaryBlock A L y k l‖ ≤
      (divisorSquareDirichletMass (1 + 1 / 262144) *
        ∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n) *
        (L * (27 / 55 : ℝ)⁻¹ ^ k * (131071 / 262144 : ℝ)⁻¹ ^ l *
          Real.exp (-(3 / 2 - 27 / 55 - (1 + 1 / 262144) : ℝ) * L)) := by
  let B := divisorSquareDirichletMass (1 + 1 / 262144)
  have hB : 0 ≤ B := divisorSquareDirichletMass_nonneg _
  have ht (p : ℕ) :
      ‖zetaPrimeLogKernel l (3 / 2 + I * y) p * boundaryResponse p L k (3 / 2 + I * y)‖ ≤
        (B * (L * (27 / 55 : ℝ)⁻¹ ^ k * (131071 / 262144 : ℝ)⁻¹ ^ l *
          Real.exp (-(3 / 2 - 27 / 55 - (1 + 1 / 262144) : ℝ) * L))) *
            zetaPrimeExpWeight (1 + 1 / 262144) p := by
    have hk := norm_zetaPrimeLogKernel_le l (3 / 2 + I * (y : ℂ)) p
      (q := 131071 / 262144) (by norm_num)
    norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero,
      sub_self, add_zero] at hk
    have hk' : ‖zetaPrimeLogKernel l (3 / 2 + I * y) p‖ ≤
        (131071 / 262144 : ℝ)⁻¹ ^ l * zetaPrimeExpWeight (1 + 1 / 262144) p := by
      convert hk using 1
      norm_num
    have hw0 : 0 ≤ zetaPrimeExpWeight (1 + 1 / 262144) p := (Real.exp_pos _).le
    rw [norm_mul]
    exact (mul_le_mul hk' (wide_boundary_response p k y hL) (norm_nonneg _)
      (by positivity)).trans_eq (by dsimp only [B]; ring)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun p _ => ht p)).trans
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left
    ((summable_zetaPrimeExpWeight (by norm_num : (1 : ℝ) < 1 + 1 / 262144)).sum_le_tsum A
      (fun _ _ => (Real.exp_pos _).le)) (by positivity)).trans_eq
        (by dsimp only [B, zetaPrimeExpWeight]; ring)

/-- The raw complete signed companion at exactly the proposed order band.
It includes all coprime squarefree composite cofactors. -/
def wideComplete (u y : ℝ) (N : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
    ∑ k ∈ ownerOrders N, ∑ p ∈ intermediatePrimes u N,
      ∑' a, compositeAtom (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k) p a

/-- The tapered prime product restored by that complete signed companion. -/
def wideWing (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ ownerOrders N, wingAtom u y N k

/-- Every correction in the literal cofactor completion, without a hidden
finite-mask or owner-removal assumption. -/
theorem wide_completion_identity (u y : ℝ) (N : ℕ) :
    wideWing u y N + wideComplete u y N =
      ((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
        ∑ k ∈ ownerOrders N,
          (jointBlock (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k) -
            boundaryBlock (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k) +
            prefixBlock (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k) +
            diagonalBlock (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k)) := by
  have hLc : (SquarefreeVaughanLogSource.length u N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (SquarefreeVaughanLogSource.length_pos u N).ne'
  unfold wideWing wideComplete
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : 0 < k := by have h := (Finset.mem_filter.mp hk).2.1; omega
  unfold wingAtom ZetaRieszEndpointTaper.taperedMoment jointBlock boundaryBlock prefixBlock diagonalBlock
  simp only [Finset.mul_sum]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hprime, _, hpX⟩ := (mem_intermediatePrimes u N p).mp hp
  have hpL : Real.log p ≤ SquarefreeVaughanLogSource.length u N :=
    (Real.log_lt_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpX)).le
  rw [(hasSum_compositeAtom hprime hpL hk0 (N + 1 - k) y).tsum_eq,
    coupledResponse_eq hprime hpL hk0 y]
  unfold ZetaRieszEndpointTaper.endpointWeight
  push_cast
  field_simp [hLc]
  ring

private theorem wide_order_sum_bound (N : ℕ) (v : ℕ → ℂ)
    {u L C E : ℝ} (hL : 0 < L) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hv : ∀ k ∈ ownerOrders N, ‖(u : ℂ) ^ (N + 1) * v k‖ ≤ C * L * E) :
    ‖(u : ℂ) ^ (N + 1) * (((N + 1 : ℕ) : ℂ) / (L : ℂ) *
      ∑ k ∈ ownerOrders N, v k)‖ ≤ 2 * C * (N + 1 : ℝ) ^ 2 * E := by
  have hcard : ((ownerOrders N).card : ℝ) ≤ 2 * (N + 1 : ℝ) := by
    have h : (ownerOrders N).card ≤ N + 2 := by
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
    have hc : ((ownerOrders N).card : ℝ) ≤ N + 2 := by exact_mod_cast h
    linarith [Nat.cast_nonneg (α := ℝ) N]
  rw [mul_left_comm, Finset.mul_sum, norm_mul, norm_div, Complex.norm_natCast,
    Complex.norm_real, Real.norm_of_nonneg hL.le]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hb : ‖∑ k ∈ ownerOrders N, (u : ℂ) ^ (N + 1) * v k‖ ≤
      (2 * (N + 1 : ℝ)) * (C * L * E) := by
    apply (norm_sum_le _ _).trans
    have h := Finset.sum_le_sum hv
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
  apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (N + 1 : ℝ) / L)).trans_eq
  field_simp

/-- The full wider completion cancels its restored tapered prime product,
with a quantitative geometric error.  No zero hypothesis is used. -/
theorem exists_wide_completion_bound (y : ℝ) (hy : 1 < |y|) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huU : u ≤ radiusCeiling) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖(u : ℂ) ^ (N + 1) * (wideWing u y N + wideComplete u y N)‖ ≤
        C * (N + 1 : ℝ) ^ 2 * Real.exp (1 - (N : ℝ) / 200000) := by
  obtain ⟨C0, hC0, hb0⟩ := exists_jointBlock_bound y hy
  let C1 := divisorSquareDirichletMass (1 + 1 / 262144) *
    ∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n
  let C2 := (∑' n, zetaPrimeExpWeight (101 / 100) n) ^ 2
  let C3 := ∑' n, zetaPrimeExpWeight (3 / 2) n
  have hC1 : 0 ≤ C1 := mul_nonneg (divisorSquareDirichletMass_nonneg _)
    (tsum_nonneg (fun _ => (Real.exp_pos _).le))
  have hC2 : 0 ≤ C2 := sq_nonneg _
  have hC3 : 0 ≤ C3 := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨2 * (C0 + C1 + C2 + C3), by positivity, ?_⟩
  have hu0 : 0 < u := by linarith
  have hue := huU.trans_lt radius_lt_source
  have huAnn := hue.trans reserve_radius_lt_annular
  filter_upwards [ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu0
    (show (0 : ℝ) ≤ 11 / 16 by norm_num) hue, eventually_ge_atTop 2] with N hLN hN
  let L := SquarefreeVaughanLogSource.length u N
  let A := intermediatePrimes u N
  let E := Real.exp (1 - (N : ℝ) / 200000)
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  have hLL : (11 / 8 : ℝ) * N ≤ L := by dsimp [L]; nlinarith [hLN]
  have hLU : L ≤ (139 / 100 : ℝ) * (N + 1 : ℕ) := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu hN
    have hl : 2 * Real.log 2 ≤ (139 / 100 : ℝ) := by linarith [Real.log_two_lt_d9]
    have h' := h.trans (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg (α := ℝ) N))
    dsimp only [L]
    push_cast
    linarith
  have hA : ∀ p ∈ A, p.Prime ∧ Real.log p ≤ L := by
    intro p hp
    obtain ⟨hprime, _, hpX⟩ := (mem_intermediatePrimes u N p).mp hp
    exact ⟨hprime, (Real.log_lt_log (by exact_mod_cast hprime.pos)
      (by exact_mod_cast hpX)).le⟩
  have hE : Real.exp (-((N + 1 : ℕ) : ℝ) / 64) ≤ E := by
    apply Real.exp_le_exp.mpr
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) N]
  rw [wide_completion_identity]
  apply wide_order_sum_bound N _ hL (by positivity) (Real.exp_pos _).le
  intro k hk
  let l := N + 1 - k
  have hkM := ownerOrders_le hk
  have hkl : k + l = N + 1 := Nat.add_sub_of_le hkM
  have h0 : ‖(u : ℂ) ^ (N + 1) * jointBlock A L y k l‖ ≤ C0 * L * E := by
    have hb := hb0 A L hL.le hA k l
    rw [hkl] at hb
    have hr := (joint_source_scalar hu0 huAnn.le (N + 1) hLU).trans hE
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    calc
      _ ≤ u ^ (N + 1) * (C0 * L * Real.exp ((13 / 50 : ℝ) * L) * (4 / 3 : ℝ) ^ (N + 1)) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hu0.le _)
      _ = C0 * L * (u ^ (N + 1) * (4 / 3 : ℝ) ^ (N + 1) * Real.exp ((13 / 50 : ℝ) * L)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
  have h1 : ‖(u : ℂ) ^ (N + 1) * boundaryBlock A L y k l‖ ≤ C1 * L * E := by
    have hr := wide_product_scalar hu0 huU N k (Finset.mem_filter.mp hk).2.2 hkM hLL
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    calc
      _ ≤ u ^ (N + 1) * (C1 * (L * (27 / 55 : ℝ)⁻¹ ^ k * (131071 / 262144 : ℝ)⁻¹ ^ l *
          Real.exp (-(3 / 2 - 27 / 55 - (1 + 1 / 262144) : ℝ) * L))) :=
        mul_le_mul_of_nonneg_left (wide_boundary_block A k l y hL.le) (pow_nonneg hu0.le _)
      _ = C1 * L * (u ^ (N + 1) * (27 / 55 : ℝ)⁻¹ ^ k * (131071 / 262144 : ℝ)⁻¹ ^ l *
          Real.exp (-(3 / 2 - 27 / 55 - (1 + 1 / 262144) : ℝ) * L)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
  have h2 : ‖(u : ℂ) ^ (N + 1) * prefixBlock A L y k l‖ ≤ C2 * L * E := by
    have hb := norm_prefixBlock_le A k l y hL.le
    rw [hkl] at hb
    have hr := (prefix_source_scalar hu0 huAnn.le (N + 1) hLU).trans hE
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    calc
      _ ≤ u ^ (N + 1) * (C2 * (L * (10 / 7 : ℝ) ^ (N + 1) * Real.exp ((21 / 100 : ℝ) * L))) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hu0.le _)
      _ = C2 * L * (u ^ (N + 1) * (10 / 7 : ℝ) ^ (N + 1) * Real.exp ((21 / 100 : ℝ) * L)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
  have h3 : ‖(u : ℂ) ^ (N + 1) * diagonalBlock A L y k l‖ ≤ C3 * L * E := by
    have hb := norm_diagonalBlock_le A k l y hL.le (fun p hp => (hA p hp).2)
    rw [hkl] at hb
    have hr := (joint_source_scalar hu0 huAnn.le (N + 1)
      (L := 0) (by positivity)).trans hE
    simp only [mul_zero, Real.exp_zero, mul_one] at hr
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    calc
      _ ≤ u ^ (N + 1) * (C3 * (L * (4 / 3 : ℝ) ^ (N + 1))) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hu0.le _)
      _ = C3 * L * (u ^ (N + 1) * (4 / 3 : ℝ) ^ (N + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
  rw [mul_add, mul_add, mul_sub]
  apply ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)).trans
  exact (add_le_add (add_le_add (add_le_add h0 h1) h2) h3).trans_eq (by ring)

/-- Completion pays all new saturation, prefix and diagonal errors, but
leaves the tapered prime product with the opposite sign. -/
theorem tendsto_wide_completion (y : ℝ) (hy : 1 < |y|) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huU : u ≤ radiusCeiling) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * (wideWing u y N + wideComplete u y N))
      atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_wide_completion_bound y hy hu huU
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2
    (Real.exp_pos (-(1 / 200000 : ℝ)))
    (Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 200000 : ℝ) < 0))).const_mul (C * Real.exp 1)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm' (a := fun N : ℕ =>
    C * Real.exp 1 * ((N + 1 : ℝ) ^ 2 * Real.exp (-(1 / 200000 : ℝ)) ^ N)) ?_ ht
  filter_upwards [hb] with N hN
  convert hN using 1
  rw [show 1 - (N : ℝ) / 200000 = 1 + (N : ℝ) * -(1 / 200000 : ℝ) by ring,
    Real.exp_add, Real.exp_nat_mul]
  ring

end
end RiemannGaussian.ZetaRieszWideOwnerAudit

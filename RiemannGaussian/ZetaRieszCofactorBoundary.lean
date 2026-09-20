/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCofactorCompletionBound

/-!
# Paying the full saturation correction

The correction is supported on cofactors above the physical cutoff.
Its complete divisor mass and complementary prime moment are summed
with independent source-scale bounds. The exact coupled coefficient
retains the original signed composite Riesz profile and clipped prime
term. No finite carrier mask or independent lower bound is presumed.
-/

namespace RiemannGaussian.ZetaRieszJointCofactor
noncomputable section
open Complex Filter Topology
open scoped Classical BigOperators ArithmeticFunction.Moebius

-- The saturation correction is genuinely supported on large cofactors.
/-- The exact saturation correction on nonunit composite squarefree cofactors, with
coprimality retained. -/
def boundaryCoefficient (p : ℕ) (L : ℝ) (a : ℕ) : ℂ :=
  if Squarefree a ∧ a ≠ 1 ∧ ¬a.Prime ∧ ¬p ∣ a then (VaughanLogAverage.riesz L a : ℂ) else 0

/-- Saturation kills the correction whenever the cofactor logarithm is at most the
original physical length. -/
theorem boundaryCoefficient_eq_zero {p a : ℕ} {L : ℝ} (ha : Real.log a ≤ L) :
    boundaryCoefficient p L a = 0 := by
  unfold boundaryCoefficient
  split_ifs with h
  · rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated h.1 h.2.1 h.2.2.1 ha]
    rfl
  · rfl

/-- The full finite Riesz divisor sum has the elementary length-times-divisor-count
allowance. -/
theorem abs_riesz_le {L : ℝ} (hL : 0 ≤ L) (a : ℕ) :
    |VaughanLogAverage.riesz L a| ≤ L * a.divisors.card := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _d ∈ a.divisors, L := by
      apply Finset.sum_le_sum
      intro d _
      rw [abs_mul, abs_of_nonneg (le_max_left 0 (L - Real.log d))]
      have hm : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      apply (mul_le_mul_of_nonneg_right hm (le_max_left 0 _)).trans
      simp only [one_mul]
      exact max_le hL (sub_le_self _ (Real.log_natCast_nonneg d))
    _ = _ := by simp [mul_comm]

/-- The complete complex moment of the saturation correction, before taking a norm. -/
def boundaryResponse (p : ℕ) (L : ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑' a, boundaryCoefficient p L a * zetaPrimeLogKernel k s a

/-- Large-cofactor support supplies an exponential length saving against a genuinely
summable divisor-square weight. -/
theorem boundary_atom_bound (p a k : ℕ) (y : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ‖boundaryCoefficient p L a * zetaPrimeLogKernel k (3 / 2 + I * y) a‖ ≤
      (L * (1024 / 255 : ℝ) ^ k * Real.exp (-L / 4)) *
        ((a.divisors.card : ℝ) ^ 2 * (a : ℝ) ^ (-(1025 / 1024 : ℝ))) := by
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
    have hk := norm_zetaPrimeLogKernel_le k (3 / 2 + I * (y : ℂ)) a
      (q := 255 / 1024) (by norm_num)
    norm_num at hk
    have hw : zetaPrimeExpWeight (1281 / 1024) a ≤
        Real.exp (-L / 4) * (a : ℝ) ^ (-(1025 / 1024 : ℝ)) := by
      rw [zetaPrimeExpWeight, Real.rpow_def_of_pos ha0, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    rw [boundaryCoefficient, if_pos ha, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (L * (a.divisors.card : ℝ)) *
          ((1024 / 255 : ℝ) ^ k * zetaPrimeExpWeight (1281 / 1024) a) :=
        mul_le_mul (abs_riesz_le hL a) hk (norm_nonneg _) (by positivity)
      _ ≤ (L * (a.divisors.card : ℝ) ^ 2) *
          ((1024 / 255 : ℝ) ^ k * (Real.exp (-L / 4) * (a : ℝ) ^ (-(1025 / 1024 : ℝ)))) := by
        have hw0 : 0 ≤ zetaPrimeExpWeight (1281 / 1024) a := (Real.exp_pos _).le
        gcongr
      _ = _ := by ring
  · simp only [boundaryCoefficient, if_neg ha, zero_mul, norm_zero]
    positivity

/-- The complete saturation-correction series has an independent height-uniform norm
bound, with its full cofactor mass summed. -/
theorem norm_boundaryResponse_le (p k : ℕ) (y : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ‖boundaryResponse p L k (3 / 2 + I * y)‖ ≤
      L * (1024 / 255 : ℝ) ^ k * Real.exp (-L / 4) *
        divisorSquareDirichletMass (1025 / 1024) := by
  let B := L * (1024 / 255 : ℝ) ^ k * Real.exp (-L / 4)
  have hsum := (summable_card_divisors_sq_mul_rpow_neg
    (by norm_num : (1 : ℝ) < 1025 / 1024)).mul_left B
  have hnorm : Summable (fun a =>
      ‖boundaryCoefficient p L a * zetaPrimeLogKernel k (3 / 2 + I * y) a‖) :=
    hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => boundary_atom_bound p a k y hL)
  apply (norm_tsum_le_tsum_norm hnorm).trans
  apply (hnorm.tsum_le_tsum (fun a => boundary_atom_bound p a k y hL) hsum).trans_eq
  exact tsum_mul_left

/-- The large-cofactor saving absorbs every original unpaid order and its
complementary prime moment at source scale. -/
theorem boundary_source_scalar {u L : ℝ} (hu : 0 < u)
    (huh : u ≤ Real.exp (-(2 / 3 : ℝ))) (N k : ℕ)
    (hk : k ≤ 13 * N / 32) (hkM : k ≤ N + 1) (hL : 4 / 3 * N ≤ L) :
    u ^ (N + 1) * (1024 / 255 : ℝ) ^ k * (1024 / 511 : ℝ) ^ (N + 1 - k) *
        Real.exp (-L / 4) ≤ Real.exp (1 / 30 - (N : ℝ) / 64) := by
  have hlu : Real.log u ≤ -(2 / 3 : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log hu huh
  have hlogs : Real.log (1024 / 511 : ℝ) ≤ 7 / 10 ∧ Real.log (511 / 255 : ℝ) ≤ 7 / 10 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 10) 7
    norm_num [Finset.sum_range_succ] at h
    constructor <;> apply (Real.log_le_iff_le_exp (by norm_num)).mpr <;> linarith
  have he : (1024 / 255 : ℝ) ^ k * (1024 / 511 : ℝ) ^ (N + 1 - k) =
      (1024 / 511 : ℝ) ^ (N + 1) * (511 / 255 : ℝ) ^ k := by
    have hpow : (1024 / 511 : ℝ) ^ (N + 1) =
        (1024 / 511 : ℝ) ^ k * (1024 / 511 : ℝ) ^ (N + 1 - k) := by
      rw [← pow_add, Nat.add_sub_of_le hkM]
    rw [hpow,
      show (1024 / 255 : ℝ) = (1024 / 511) * (511 / 255) by norm_num, mul_pow]
    ring
  rw [mul_assoc (u ^ (N + 1)), he]
  have hpow (x : ℝ) (hx : 0 < x) (m : ℕ) : x ^ m = Real.exp ((m : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  rw [hpow u hu, hpow (1024 / 511) (by norm_num), hpow (511 / 255) (by norm_num),
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_left hlu (Nat.cast_nonneg (α := ℝ) (N + 1))
  have h2 := mul_le_mul_of_nonneg_left hlogs.1 (Nat.cast_nonneg (α := ℝ) (N + 1))
  have h3 := mul_le_mul_of_nonneg_left hlogs.2 (Nat.cast_nonneg (α := ℝ) k)
  have hkc : 32 * (k : ℝ) ≤ 13 * N := by
    exact_mod_cast (show 32 * k ≤ 13 * N by omega)
  norm_num only [Nat.cast_add, Nat.cast_one] at *
  nlinarith


/-- The original distinguished-prime family coupled to the complete saturation-
correction series. -/
def boundaryBlock (A : Finset ℕ) (L y : ℝ) (k l : ℕ) : ℂ :=
  ∑ p ∈ A, zetaPrimeLogKernel l (3 / 2 + I * y) p *
    boundaryResponse p L k (3 / 2 + I * y)

/-- Both arithmetic series in the boundary block are paid by convergent positive
masses, uniformly in height and finite selection. -/
theorem norm_boundaryBlock_le (A : Finset ℕ) (k l : ℕ) (y : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ‖boundaryBlock A L y k l‖ ≤
      (divisorSquareDirichletMass (1025 / 1024) *
        ∑' n, zetaPrimeExpWeight (1025 / 1024) n) *
          (L * (1024 / 255 : ℝ) ^ k * (1024 / 511 : ℝ) ^ l * Real.exp (-L / 4)) := by
  let B := divisorSquareDirichletMass (1025 / 1024)
  have hB : 0 ≤ B := divisorSquareDirichletMass_nonneg _
  have hterm (p : ℕ) :
      ‖zetaPrimeLogKernel l (3 / 2 + I * y) p * boundaryResponse p L k (3 / 2 + I * y)‖ ≤
        (B * (L * (1024 / 255 : ℝ) ^ k * (1024 / 511 : ℝ) ^ l * Real.exp (-L / 4))) *
          zetaPrimeExpWeight (1025 / 1024) p := by
    have hk := norm_zetaPrimeLogKernel_le l (3 / 2 + I * (y : ℂ)) p
      (q := 511 / 1024) (by norm_num)
    norm_num at hk
    have hw0 : 0 ≤ zetaPrimeExpWeight (1025 / 1024) p := (Real.exp_pos _).le
    rw [norm_mul]
    exact (mul_le_mul hk (norm_boundaryResponse_le p k y hL) (norm_nonneg _)
      (by positivity)).trans_eq (by dsimp only [B]; ring)
  calc
    _ ≤ ∑ p ∈ A, ‖zetaPrimeLogKernel l (3 / 2 + I * y) p * boundaryResponse p L k (3 / 2 + I * y)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ A,
        (B * (L * (1024 / 255 : ℝ) ^ k * (1024 / 511 : ℝ) ^ l * Real.exp (-L / 4))) *
          zetaPrimeExpWeight (1025 / 1024) p := Finset.sum_le_sum (fun p _ => hterm p)
    _ = (B * (L * (1024 / 255 : ℝ) ^ k * (1024 / 511 : ℝ) ^ l * Real.exp (-L / 4))) *
        ∑ p ∈ A, zetaPrimeExpWeight (1025 / 1024) p := by rw [Finset.mul_sum]
    _ ≤ (B * (L * (1024 / 255 : ℝ) ^ k * (1024 / 511 : ℝ) ^ l * Real.exp (-L / 4))) *
        ∑' p, zetaPrimeExpWeight (1025 / 1024) p :=
      mul_le_mul_of_nonneg_left
        ((summable_zetaPrimeExpWeight (by norm_num : (1 : ℝ) < 1025 / 1024)).sum_le_tsum A
          (fun _ _ => (Real.exp_pos _).le)) (by positivity)
    _ = _ := by ring

/-- The saturation correction summed over the exact original unpaid wing orders and
physical primes. -/
def boundaryWing (u y : ℝ) (N : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
    ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      boundaryBlock (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k)

/-- One constant bounds the normalized whole boundary correction by C(N+1)^2
exp(-N/64), uniformly in height. The starting order may depend on the radius. -/
theorem exists_boundaryWing_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ), 1 / 2 ≤ u → u < Real.exp (-(2 / 3 : ℝ)) →
      ∀ᶠ N : ℕ in atTop, ∀ y : ℝ,
        ‖(u : ℂ) ^ (N + 1) * boundaryWing u y N‖ ≤
          C * (N + 1 : ℝ) ^ 2 * Real.exp (-(N : ℝ) / 64) := by
  let B := divisorSquareDirichletMass (1025 / 1024) *
    ∑' n, zetaPrimeExpWeight (1025 / 1024) n
  have hB : 0 ≤ B := mul_nonneg (divisorSquareDirichletMass_nonneg _)
    (tsum_nonneg (fun _ => (Real.exp_pos _).le))
  refine ⟨2 * B * Real.exp (1 / 30), by positivity, ?_⟩
  intro u hu huh
  have hu0 : 0 < u := by linarith
  filter_upwards [ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu0
    (by norm_num : (0 : ℝ) ≤ 2 / 3) huh] with N hLN y
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszWingHighOrders.unpaidOrders N
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  have hkM (k : ℕ) (hk : k ∈ S) : k ≤ N + 1 :=
    (ZetaRieszReflectedCompletion.lowerWing_bounds
      (ZetaRieszWingHighOrders.unpaidOrders_support hk).1).2.2
  have hcard : (S.card : ℝ) ≤ 2 * (N + 1 : ℝ) := by
    have hs : S ⊆ Finset.range (N + 2) := fun k hk =>
      Finset.mem_range.mpr (by have := hkM k hk; omega)
    have hc' : S.card ≤ N + 2 := by simpa using Finset.card_le_card hs
    have hc : (S.card : ℝ) ≤ N + 2 := by exact_mod_cast hc'
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have ht (k : ℕ) (hk : k ∈ S) :
      ‖(u : ℂ) ^ (N + 1) * (((N + 1 : ℕ) : ℂ) / (L : ℂ) *
        boundaryBlock A L y k (N + 1 - k))‖ ≤
          B * (N + 1 : ℝ) * Real.exp (1 / 30 - (N : ℝ) / 64) := by
    have hb := norm_boundaryBlock_le A k (N + 1 - k) y hL.le
    have hr := boundary_source_scalar (L := L) hu0 huh.le N k
      (ZetaRieszWingHighOrders.unpaidOrders_support hk).2.1 (hkM k hk)
      (by nlinarith only [hLN])
    rw [norm_mul, norm_mul, norm_pow, norm_div, Complex.norm_natCast,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hu0.le,
      Real.norm_of_nonneg hL.le]
    norm_num only [Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ u ^ (N + 1) * (((N + 1 : ℝ) / L) *
          (B * (L * (1024 / 255 : ℝ) ^ k * (1024 / 511 : ℝ) ^ (N + 1 - k) * Real.exp (-L / 4)))) := by
        gcongr
      _ = B * (N + 1 : ℝ) *
          (u ^ (N + 1) * (1024 / 255 : ℝ) ^ k * (1024 / 511 : ℝ) ^ (N + 1 - k) * Real.exp (-L / 4)) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
  change ‖(u : ℂ) ^ (N + 1) *
    (((N + 1 : ℕ) : ℂ) / (L : ℂ) * ∑ k ∈ S, boundaryBlock A L y k (N + 1 - k))‖ ≤ _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  have hsum := Finset.sum_le_sum ht
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  apply hsum.trans
  have hc := mul_le_mul_of_nonneg_right hcard
    (show 0 ≤ B * (N + 1 : ℝ) * Real.exp (1 / 30 - (N : ℝ) / 64) by positivity)
  apply hc.trans_eq
  rw [Real.exp_sub]
  rw [show Real.exp (-(N : ℝ) / 64) = (Real.exp ((N : ℝ) / 64))⁻¹ by
    rw [neg_div, Real.exp_neg]]
  ring


-- This keeps the composite Riesz coefficient and the prime cofactor
-- in ONE convergent series. The original wing is recovered only after
-- paying its clipped-prefix and repeated-prime differences.
/-- The signed original composite Riesz coefficient coupled to the clipped coprime
prime term. Neither the prime term nor the saturation correction is silently
discarded. -/
def coupledCoefficient (p : ℕ) (L : ℝ) (a : ℕ) : ℂ :=
  (if Squarefree a ∧ a ≠ 1 ∧ ¬a.Prime ∧ ¬p ∣ a then
    -(VaughanLogAverage.riesz L (p * a) : ℂ) else 0) +
  (if a.Prime ∧ ¬p ∣ a then
    ((L - Real.log p - max 0 (L - Real.log p - Real.log a) : ℝ) : ℂ) else 0)

/-- The complete cofactor coefficient splits exactly into the coupled arithmetic,
saturation correction and unit term. -/
theorem cofactorCoefficient_eq_coupled {p : ℕ} (hp : p.Prime) {L : ℝ}
    (hpL : Real.log p ≤ L) (a : ℕ) :
    cofactorCoefficient p (L - Real.log p) a =
      coupledCoefficient p L a + boundaryCoefficient p L a +
        if a = 1 then ((L - Real.log p : ℝ) : ℂ) else 0 := by
  by_cases ha1 : a = 1
  · subst a
    simp [cofactorCoefficient, coupledCoefficient, boundaryCoefficient,
      VaughanLogAverage.riesz, hp.not_dvd_one, max_eq_right (sub_nonneg.mpr hpL)]
  by_cases ha : Squarefree a ∧ ¬p ∣ a
  · by_cases hprime : a.Prime
    · have hr : VaughanLogAverage.riesz (L - Real.log p) a =
          L - Real.log p - max 0 (L - Real.log p - Real.log a) := by
        rw [VaughanLogAverage.riesz, hprime.sum_divisors]
        simp [ArithmeticFunction.moebius_apply_prime hprime,
          max_eq_right (sub_nonneg.mpr hpL)]
        ring
      simp [cofactorCoefficient, coupledCoefficient, boundaryCoefficient,
        ha.1, ha.2, ha1, hprime, hr]
    · have hgood : Squarefree a ∧ a ≠ 1 ∧ ¬a.Prime ∧ ¬p ∣ a := ⟨ha.1, ha1, hprime, ha.2⟩
      have hbad : ¬(a.Prime ∧ ¬p ∣ a) := fun h => hprime h.1
      rw [cofactorCoefficient, if_pos ha, coupledCoefficient, if_pos hgood,
        if_neg hbad, boundaryCoefficient, if_pos hgood, if_neg ha1, add_zero, add_zero]
      rw [ZetaSquarefreeRieszWindows.riesz_prime_mul L hp ha.2]
      push_cast
      ring
  · have hc : ¬(Squarefree a ∧ a ≠ 1 ∧ ¬a.Prime ∧ ¬p ∣ a) :=
      fun h => ha ⟨h.1, h.2.2.2⟩
    have hprime : ¬(a.Prime ∧ ¬p ∣ a) := fun h => ha ⟨h.1.squarefree, h.2⟩
    simp only [cofactorCoefficient, coupledCoefficient, boundaryCoefficient,
      if_neg ha, if_neg hc, if_neg hprime, if_neg ha1, add_zero]

/-- For every eligible composite cofactor, the coupled coefficient with its physical
logarithmic factor is precisely the original carrier coefficient. -/
theorem coupledCoefficient_eq_original {p a : ℕ} (hp : p.Prime)
    (ha : Squarefree a) (ha1 : a ≠ 1) (hprime : ¬a.Prime) (hpa : ¬p ∣ a)
    {L : ℝ} :
    ((Real.log (p * a : ℕ) : ℝ) : ℂ) / (L : ℂ) * coupledCoefficient p L a =
      SquarefreeVaughanLogSource.coefficient L (p * a) := by
  have hsf := Nat.squarefree_mul_iff.mpr
    ⟨hp.coprime_iff_not_dvd.mpr hpa, hp.squarefree, ha⟩
  have hgood : Squarefree a ∧ a ≠ 1 ∧ ¬a.Prime ∧ ¬p ∣ a := ⟨ha, ha1, hprime, hpa⟩
  have hbad : ¬(a.Prime ∧ ¬p ∣ a) := fun h => hprime h.1
  have hpacom : Squarefree (p * a) ∧ ¬(p * a).Prime :=
    ⟨hsf, Nat.not_prime_mul hp.ne_one ha1⟩
  rw [coupledCoefficient, if_pos hgood, if_neg hbad, add_zero,
    SquarefreeVaughanLogSource.coefficient, if_pos hpacom]
  push_cast
  ring

/-- The prime and composite cofactor coefficients remain coupled in one complete
arithmetic series. -/
def coupledResponse (p : ℕ) (L : ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑' a, coupledCoefficient p L a * zetaPrimeLogKernel k s a

/-- The coupled arithmetic series genuinely converges and is exactly the completed
cofactor response minus the saturation correction. -/
theorem hasSum_coupledResponse {p : ℕ} (hp : p.Prime) {L : ℝ}
    (hpL : Real.log p ≤ L) {k : ℕ} (hk : 0 < k) (y : ℝ) :
    HasSum (fun a => coupledCoefficient p L a * zetaPrimeLogKernel k (3 / 2 + I * y) a)
      (cofactorResponse p (L - Real.log p) k (3 / 2 + I * y) -
        boundaryResponse p L k (3 / 2 + I * y)) := by
  have hL : 0 ≤ L := (Real.log_natCast_nonneg p).trans hpL
  have hD : L - Real.log p ≤ Real.log (⌈Real.exp (L - Real.log p)⌉₊ + 1 : ℕ) := by
    have he := Nat.le_ceil (Real.exp (L - Real.log p))
    have he' : Real.exp (L - Real.log p) ≤ (⌈Real.exp (L - Real.log p)⌉₊ + 1 : ℕ) := by
      push_cast
      linarith
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) he'
  have hc := (hasSum_cofactorResponse hp (L - Real.log p) hD k
    (by norm_num : (1 : ℝ) < (3 / 2 + I * (y : ℂ)).re)).summable
  have hb : Summable (fun a => boundaryCoefficient p L a * zetaPrimeLogKernel k (3 / 2 + I * y) a) :=
    ((summable_card_divisors_sq_mul_rpow_neg
      (by norm_num : (1 : ℝ) < 1025 / 1024)).mul_left
        (L * (1024 / 255 : ℝ) ^ k * Real.exp (-L / 4))).of_norm_bounded
      (fun a => boundary_atom_bound p a k y hL)
  apply (hc.hasSum.sub hb.hasSum).congr_fun
  intro a
  rw [SquarefreeEulerQuadratic.primeFilterKernel_one]
  change _ = cofactorCoefficient p (L - Real.log p) a * zetaPrimeLogKernel k (3 / 2 + I * y) a - _
  rw [cofactorCoefficient_eq_coupled hp hpL]
  by_cases ha : a = 1
  · simp [ha, zetaPrimeLogKernel, hk.ne']
  · rw [if_neg ha]
    ring

/-- The complete coupled response is the difference of the two independently bounded
arithmetic responses. -/
theorem coupledResponse_eq {p : ℕ} (hp : p.Prime) {L : ℝ}
    (hpL : Real.log p ≤ L) {k : ℕ} (hk : 0 < k) (y : ℝ) :
    coupledResponse p L k (3 / 2 + I * y) =
      cofactorResponse p (L - Real.log p) k (3 / 2 + I * y) -
        boundaryResponse p L k (3 / 2 + I * y) :=
  (hasSum_coupledResponse hp hpL hk y).tsum_eq

/-- The coupled prime/composite series on the original unpaid orders and
intermediate primes. Prime clipping and the repeated-prime correction are
treated separately. -/
def coupledWing (u y : ℝ) (N : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
    ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      ∑ p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N,
        zetaPrimeLogKernel (N + 1 - k) (3 / 2 + I * y) p *
          coupledResponse p (SquarefreeVaughanLogSource.length u N) k (3 / 2 + I * y)

/-- The full coupled wing equals the completed wing minus its exact saturation
correction at every order. -/
theorem coupledWing_eq (u y : ℝ) (N : ℕ) :
    coupledWing u y N = completedWing u y N - boundaryWing u y N := by
  unfold coupledWing completedWing boundaryWing
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  unfold jointBlock boundaryBlock
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hprime, _, hpX⟩ := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hp
  have hpL : Real.log p ≤ SquarefreeVaughanLogSource.length u N :=
    (Real.log_lt_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpX)).le
  have hk0 : 0 < k := by have h := (ZetaRieszWingHighOrders.unpaidOrders_support hk).2.2; omega
  rw [coupledResponse_eq hprime hpL hk0]
  ring

/-- The complete coupled wing decays at source scale without any hypothetical-zero
premise. The original finite count masks are not imposed on its cofactors. -/
theorem tendsto_coupledWing (y : ℝ) (hy : 1 < |y|) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * coupledWing u y N) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_boundaryWing_bound
  have h := (ZetaRieszShiftedHeadBudget.tendsto_quadratic_geometric
    (Real.exp_pos (-(1 / 64 : ℝ))).le
    (Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 64 : ℝ) < 0))).const_mul C
  simp only [mul_zero] at h
  have hboundary : Tendsto (fun N => (u : ℂ) ^ (N + 1) * boundaryWing u y N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => C * ((N + 1 : ℝ) ^ 2 *
      Real.exp (-(1 / 64 : ℝ)) ^ N)) _ h
    filter_upwards [hb u hu huh] with N hN
    have he : Real.exp (-(1 / 64 : ℝ)) ^ N = Real.exp (-(N : ℝ) / 64) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simpa only [mul_assoc, he] using hN y
  have he := (tendsto_completedWing y hy hu huh.le).sub hboundary
  simpa only [sub_zero, coupledWing_eq, mul_sub] using he

end
end RiemannGaussian.ZetaRieszJointCofactor

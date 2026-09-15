/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSemiprimePrefixDecay
import RiemannGaussian.ZetaRieszCosineCarrier

/-!
# Sign and amplitude bounds for actual three-prime coefficients

The third prime inserts an exact difference of two tents. On
log(n)<=2L the actual three-prime coefficient is nonnegative and at most
half log(n), with a further reflection-gap bound. Its signed response
pays only for negative observations; that phase cost is not yet bounded
at the source scale.
-/

namespace RiemannGaussian.ZetaRieszTriplePrime
noncomputable section
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows

/-- Inserting the third prime retains the difference of two complete
two-prime tents, with the same logarithmic cutoff. -/
def tripleDifference (a b c L : ℝ) : ℝ :=
  primePairTent a b L - primePairTent a b (L - c)

/-- On the upper half of the total logarithmic support, the three-prime
profile has a fixed sign and costs at most half the physical length. -/
theorem tripleDifference_bounds {a b c L : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hL : a + b + c ≤ 2 * L) :
    -(L / 2) ≤ tripleDifference a b c L ∧ tripleDifference a b c L ≤ 0 := by
  simp only [tripleDifference, primePairTent, max_def]
  split_ifs <;> constructor <;> linarith

/-- The three-prime profile vanishes at the reflection midpoint, and
its signed size is bounded by the distance from that midpoint. -/
theorem neg_tripleDifference_le_midpoint_gap {a b c L : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hL : a + b + c ≤ 2 * L) :
    -tripleDifference a b c L ≤ 2 * L - (a + b + c) := by
  simp only [tripleDifference, primePairTent, max_def]
  split_ifs <;> linarith

/-- The actual squarefree three-prime profile is the same signed tent
difference. All three prime logarithms remain in their original positions. -/
theorem riesz_three_primes_eq_difference (L : ℝ) {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    VaughanLogAverage.riesz L (p * (q * r)) =
      tripleDifference (Real.log p) (Real.log q) (Real.log r) L := by
  have hpd : ¬ p ∣ r := fun hd => hpr ((Nat.dvd_prime_two_le hr hp.two_le).mp hd)
  have hqd : ¬ q ∣ r := fun hd => hqr ((Nat.dvd_prime_two_le hr hq.two_le).mp hd)
  rw [riesz_two_primes_eq_tent L hp hq hpq hpd hqd, hr.sum_divisors]
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.cast_one,
    Real.log_one, sub_zero, one_mul, ArithmeticFunction.moebius_apply_prime hr,
    Int.cast_neg, neg_one_mul, tripleDifference]
  ring

/-- Squarefreeness and exactly three distinct factors produce an actual
product of three distinct primes, without ordered incidence overcounting. -/
theorem exists_three_primes {n : ℕ} (hsf : Squarefree n)
    (hcard : n.primeFactors.card = 3) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧
      p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p * (q * r) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, he⟩ := Finset.card_eq_three.mp hcard
  have hp : p ∈ n.primeFactors := by simp [he]
  have hq : q ∈ n.primeFactors := by simp [he]
  have hr : r ∈ n.primeFactors := by simp [he]
  refine ⟨p, q, r, Nat.prime_of_mem_primeFactors hp,
    Nat.prime_of_mem_primeFactors hq, Nat.prime_of_mem_primeFactors hr,
    hpq, hpr, hqr, ?_⟩
  simpa [he, hpq, hpr, hqr, mul_assoc] using
    (Nat.prod_primeFactors_of_squarefree hsf).symm

/-- The actual three-prime Riesz divisor sum is nonpositive in the
physical annulus and bounded below by minus half its cutoff length. -/
theorem riesz_of_three_primeFactors_bounds {n : ℕ} (hsf : Squarefree n)
    (hcard : n.primeFactors.card = 3) {L : ℝ} (hmid : Real.log n ≤ 2 * L) :
    -(L / 2) ≤ VaughanLogAverage.riesz L n ∧ VaughanLogAverage.riesz L n ≤ 0 := by
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr, rfl⟩ := exists_three_primes hsf hcard
  have hlog : Real.log (p * (q * r) : ℕ) = Real.log p + Real.log q + Real.log r := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast (Nat.mul_ne_zero hq.ne_zero hr.ne_zero)), Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hr.ne_zero)]
    ring
  rw [hlog] at hmid
  rw [riesz_three_primes_eq_difference L hp hq hr hpq hpr hqr]
  exact tripleDifference_bounds (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q)
    (Real.log_natCast_nonneg r) hmid

/-- The three-prime coefficient's Riesz factor also retains its exact
distance from the reflection midpoint as an independent allowance. -/
theorem neg_riesz_three_le_midpoint_gap {n : ℕ} (hsf : Squarefree n)
    (hcard : n.primeFactors.card = 3) {L : ℝ} (hmid : Real.log n ≤ 2 * L) :
    -VaughanLogAverage.riesz L n ≤ 2 * L - Real.log n := by
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr, rfl⟩ := exists_three_primes hsf hcard
  have hlog : Real.log (p * (q * r) : ℕ) = Real.log p + Real.log q + Real.log r := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast (Nat.mul_ne_zero hq.ne_zero hr.ne_zero)), Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hr.ne_zero)]
    ring
  rw [hlog] at hmid
  rw [riesz_three_primes_eq_difference L hp hq hr hpq hpr hqr, hlog]
  exact neg_tripleDifference_le_midpoint_gap (Real.log_natCast_nonneg p)
    (Real.log_natCast_nonneg q) (Real.log_natCast_nonneg r) hmid

/-- The actual three-prime coefficient has a known nonnegative sign and
costs at most one half-logarithm in the physical annulus. This is a bound
before applying the complex product phase, not a floor for its real sum. -/
theorem actual_three_prime_coefficient_bounds {n : ℕ}
    (hcard : n.primeFactors.card = 3) {L : ℝ} (hL : 0 < L)
    (hmid : Real.log n ≤ 2 * L) :
    0 ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤ Real.log n / 2 := by
  unfold SquarefreeVaughanLogSource.coefficient
  split_ifs with hn
  · have hr := riesz_of_three_primeFactors_bounds hn.1 hcard hmid
    have hlog := Real.log_natCast_nonneg n
    have hc : 0 ≤ -Real.log n * VaughanLogAverage.riesz L n / L :=
      div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) hr.2) hL.le
    refine ⟨by simpa only [Complex.ofReal_re] using hc, ?_⟩
    rw [Complex.norm_real, Real.norm_of_nonneg hc]
    apply (div_le_iff₀ hL).mpr
    nlinarith [mul_le_mul_of_nonneg_left hr.1 hlog]
  · simp only [Complex.zero_re, norm_zero, le_refl, true_and]
    exact div_nonneg (Real.log_natCast_nonneg n) (by norm_num)

/-- The same literal coefficient keeps the vanishing midpoint allowance,
including the full physical logarithm and its original normalization. -/
theorem norm_actual_three_prime_le_midpoint_gap {n : ℕ}
    (hcard : n.primeFactors.card = 3) {L : ℝ} (hL : 0 < L)
    (hmid : Real.log n ≤ 2 * L) :
    ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤
      Real.log n / L * (2 * L - Real.log n) := by
  unfold SquarefreeVaughanLogSource.coefficient
  split_ifs with hn
  · have hr := riesz_of_three_primeFactors_bounds hn.1 hcard hmid
    have hg := neg_riesz_three_le_midpoint_gap hn.1 hcard hmid
    have hlog := Real.log_natCast_nonneg n
    have hc : 0 ≤ -Real.log n * VaughanLogAverage.riesz L n / L :=
      div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) hr.2) hL.le
    rw [Complex.norm_real, Real.norm_of_nonneg hc]
    calc
      _ = Real.log n / L * (-VaughanLogAverage.riesz L n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (div_nonneg hlog hL.le)
  · simp only [norm_zero]
    exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (sub_nonneg.mpr hmid)

/-- The known arithmetic sign lets a three-prime atom pay only for
the negative real part of its full observation. Positive phases have
zero lower-bound cost, while the original complex kernel is retained. -/
theorem re_three_prime_atom_ge_negative_phase {n : ℕ}
    (hcard : n.primeFactors.card = 3) {L : ℝ} (hL : 0 < L)
    (hmid : Real.log n ≤ 2 * L) (z : ℂ) :
    -(Real.log n / 2) * max 0 (-z.re) ≤
      (SquarefreeVaughanLogSource.coefficient L n * z).re := by
  have hc := actual_three_prime_coefficient_bounds hcard hL hmid
  have hu : (SquarefreeVaughanLogSource.coefficient L n).re ≤ Real.log n / 2 :=
    (Complex.re_le_norm _).trans hc.2
  rw [Complex.mul_re, ZetaRieszCosineCarrier.coefficient_im_eq_zero, zero_mul, sub_zero]
  by_cases hz : 0 ≤ z.re
  · rw [max_eq_left (neg_nonpos.mpr hz), mul_zero]
    exact mul_nonneg hc.1 hz
  · rw [max_eq_right (by linarith : 0 ≤ -z.re)]
    nlinarith [mul_le_mul_of_nonpos_right hu (le_of_not_ge hz)]

/-- Every finite observed three-prime sum has an independent explicit
lower bound supported only on its negative phases. All integer masks,
filter weights and observations are allowed. The phase cost still needs
arithmetic control before it can yield a source-scale cofinal floor. -/
theorem re_three_prime_sum_ge_negative_phase (S : Finset ℕ) (f : ℕ → ℂ)
    {L : ℝ} (hL : 0 < L)
    (hcard : ∀ n ∈ S, n.primeFactors.card = 3)
    (hmid : ∀ n ∈ S, Real.log n ≤ 2 * L) :
    (∑ n ∈ S, -(Real.log n / 2) * max 0 (-(f n).re)) ≤
      (∑ n ∈ S, SquarefreeVaughanLogSource.coefficient L n * f n).re := by
  rw [Complex.re_sum]
  exact Finset.sum_le_sum (fun n hn =>
    re_three_prime_atom_ge_negative_phase (hcard n hn) hL (hmid n hn) (f n))

end

end RiemannGaussian.ZetaRieszTriplePrime

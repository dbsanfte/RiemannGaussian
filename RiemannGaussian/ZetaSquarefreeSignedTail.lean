/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeRieszCompletion

/-!
# Signed prime-subset tails and their full character correlations

Clipping retains a finite signed tail above the cutoff, with every prime
count, shifted insertion ramp and shared-prime correlation. The finite
character product isolates an uncontrolled first-order prime-phase core
and a bounded nonlinear remainder at fixed Re(s)>1/2. A bound for the
remainder alone is not a bound for the exponential or the original filter.
-/

namespace RiemannGaussian.ZetaSquarefreeSignedTail
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open MeasureTheory Set Filter Topology
open ZetaArithmeticAffine
open ZetaArithmeticBandCorrelation
open ZetaSquarefreeRieszWindows
open ZetaSquarefreeRieszCompletion
open scoped ArithmeticFunction.Moebius

/-- Summing every signed prime subset gives the reciprocal local Euler
product. This holds for arbitrary complex local factors, retaining phase. -/
theorem signed_subset_euler_product {ι : Type*} (Q : Finset ι) (q : ι → ℂ)
    (hq : ∀ p ∈ Q, 1 + q p ≠ 0) :
    (∑ S ∈ Q.powerset, ∏ p ∈ S, (-q p / (1 + q p))) =
      ∏ p ∈ Q, (1 + q p)⁻¹ := by
  rw [← Finset.prod_one_add]
  apply Finset.prod_congr rfl
  intro p hp
  field_simp [hq p hp]
  ring

/-- The complete signed subset interaction with an additive logarithmic
weight has a closed form. No pairwise truncation is used. -/
theorem signed_subset_log_complete {ι : Type*} (Q : Finset ι) (q ell : ι → ℂ)
    (L : ℂ) (hq : ∀ p ∈ Q, 1 + q p ≠ 0) :
    (∑ S ∈ Q.powerset, (L - ∑ p ∈ S, ell p) *
      ∏ p ∈ S, (-q p / (1 + q p))) =
      (∏ p ∈ Q, (1 + q p)⁻¹) * (L + ∑ p ∈ Q, ell p * q p) := by
  induction Q using Finset.induction_on generalizing L with
  | empty => simp
  | @insert p Q hp ih =>
    have hQ : ∀ a ∈ Q, 1 + q a ≠ 0 := fun a ha ↦ hq a (Finset.mem_insert_of_mem ha)
    have hqp := hq p (Finset.mem_insert_self p Q)
    rw [Finset.sum_powerset_insert hp]
    have hi : (∑ S ∈ Q.powerset, (L - ∑ a ∈ insert p S, ell a) *
        ∏ a ∈ insert p S, (-q a / (1 + q a))) =
        (-q p / (1 + q p)) * ∑ S ∈ Q.powerset,
          (L - ell p - ∑ a ∈ S, ell a) * ∏ a ∈ S, (-q a / (1 + q a)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      have hpS : p ∉ S := fun h ↦ hp (Finset.mem_powerset.mp hS h)
      rw [Finset.sum_insert hpS, Finset.prod_insert hpS]
      ring
    rw [hi, ih L hQ, ih (L - ell p) hQ, Finset.prod_insert hp, Finset.sum_insert hp]
    generalize (∏ a ∈ Q, (1 + q a)⁻¹) = A
    generalize (∑ a ∈ Q, ell a * q a) = B
    field_simp [hqp]
    ring

/-- Riesz clipping leaves an explicit signed subset tail above the
cutoff. Completing the Euler product does not discard this tail. -/
theorem signed_subset_riesz_eq_complete_add_tail {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (L : ℝ) (hq : ∀ p ∈ Q, 1 + q p ≠ 0) :
    (∑ S ∈ Q.powerset, ((max 0 (L - ∑ p ∈ S, ell p) : ℝ) : ℂ) *
      ∏ p ∈ S, (-q p / (1 + q p))) =
      (∏ p ∈ Q, (1 + q p)⁻¹) *
        ((L : ℂ) + ∑ p ∈ Q, (ell p : ℂ) * q p) +
      ∑ S ∈ Q.powerset, ((max 0 ((∑ p ∈ S, ell p) - L) : ℝ) : ℂ) *
        ∏ p ∈ S, (-q p / (1 + q p)) := by
  have hmax (x : ℝ) : max 0 (L - x) = L - x + max 0 (x - L) := by
    rcases le_total L x with h | h
    · rw [max_eq_left (by linarith : L - x ≤ 0),
        max_eq_right (by linarith : 0 ≤ x - L)]
      ring
    · rw [max_eq_right (by linarith : 0 ≤ L - x),
        max_eq_left (by linarith : x - L ≤ 0)]
      ring
  simp_rw [hmax, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_sum,
    add_mul, Finset.sum_add_distrib]
  rw [signed_subset_log_complete Q q (fun p ↦ (ell p : ℂ)) (L : ℂ) hq]

/-- The full signed prime-subset tail, with the additive cutoff retained. -/
def signedSubsetTail {ι : Type*} (Q : Finset ι) (a : ι → ℂ) (ell : ι → ℝ)
    (L : ℝ) : ℂ :=
  ∑ S ∈ Q.powerset, ((max 0 ((∑ p ∈ S, ell p) - L) : ℝ) : ℂ) *
    ∏ p ∈ S, (-a p)

/-- Inserting one prime couples the same tail at two exact cutoffs.
It cannot be replaced by independent signs at the two cutoffs. -/
theorem signedSubsetTail_insert {ι : Type*} (Q : Finset ι) (a : ι → ℂ)
    (ell : ι → ℝ) (L : ℝ) {p : ι} (hp : p ∉ Q) :
    signedSubsetTail (insert p Q) a ell L =
      signedSubsetTail Q a ell L + (-a p) * signedSubsetTail Q a ell (L - ell p) := by
  unfold signedSubsetTail
  rw [Finset.sum_powerset_insert hp]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hpS : p ∉ S := fun h ↦ hp (Finset.mem_powerset.mp hS h)
  rw [Finset.sum_insert hpS, Finset.prod_insert hpS,
    show ell p + (∑ x ∈ S, ell x) - L = (∑ x ∈ S, ell x) - (L - ell p) by ring]
  ring

/-- A single eligible prime cannot cross the cutoff; neither can the
empty subset. The physical tail begins with higher prime interactions. -/
theorem signedSubsetTail_singleton_eq_zero {ι : Type*} (a : ι → ℂ) (ell : ι → ℝ)
    (L : ℝ) (p : ι) (hL : 0 ≤ L) (hp : ell p ≤ L) :
    signedSubsetTail {p} a ell L = 0 := by
  rw [show ({p} : Finset ι) = insert p ∅ by rfl,
    signedSubsetTail_insert ∅ a ell L (by simp)]
  simp [signedSubsetTail, max_eq_left (by linarith : -L ≤ 0), hp]

/-- Every multiplicative observation of the complete subset measure
factorizes exactly, including complex Fourier characters and all orders. -/
theorem signed_subset_character_product {ι : Type*} (Q : Finset ι)
    (a z : ι → ℂ) :
    (∑ S ∈ Q.powerset, (∏ p ∈ S, (-a p)) * ∏ p ∈ S, z p) =
      ∏ p ∈ Q, (1 - a p * z p) := by
  simp_rw [← Finset.prod_mul_distrib]
  simpa only [neg_mul, sub_eq_add_neg] using
    (Finset.prod_one_add (f := fun p ↦ (-a p) * z p) Q).symm

/-- Shared primes contribute a nonnegative squared modulus to a pair
correlation. Their phases cancel exactly; relative phase is carried by
the remaining prime factors. The cutoff weights can still be coupled. -/
theorem signed_subset_shared_prime_factor {ι : Type*} (G A B : Finset ι)
    (a : ι → ℂ) (hGA : Disjoint G A) (hGB : Disjoint G B) :
    (∏ p ∈ G ∪ A, (-a p)) * conj (∏ p ∈ G ∪ B, (-a p)) =
      (Complex.normSq (∏ p ∈ G, (-a p)) : ℂ) *
        (∏ p ∈ A, (-a p)) * conj (∏ p ∈ B, (-a p)) := by
  rw [Finset.prod_union hGA, Finset.prod_union hGB, map_mul, ← Complex.mul_conj]
  ring

/-- Dividing a local signed measure by its total mass exposes the
ordinary-prime phase difference, without discarding the local factor. -/
theorem normalized_prime_character_factor (q z : ℂ) (hq : 1 + q ≠ 0) :
    1 - q / (1 + q) * z = (1 + q * (1 - z)) / (1 + q) := by
  field_simp
  ring

/-- The nonlinear part of a normalized local prime character costs
only a prime-square weight, uniformly in every bounded character z. -/
theorem norm_normalized_prime_character_log_error (q z : ℂ)
    (hq : ‖q‖ ≤ 1 / 4) (hz : ‖z‖ ≤ 1) :
    ‖Complex.log (1 + q * (1 - z)) - q * (1 - z)‖ ≤ 4 * ‖q‖ ^ 2 := by
  let w := q * (1 - z)
  have hw : ‖w‖ ≤ 2 * ‖q‖ := by
    dsimp [w]
    rw [norm_mul]
    have h := norm_sub_le (1 : ℂ) z
    rw [norm_one] at h
    nlinarith [norm_nonneg q, mul_le_mul_of_nonneg_left h (norm_nonneg q)]
  have hw1 : ‖w‖ < 1 := by linarith
  have hi : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - ‖w‖)).mpr
    linarith
  have h := Complex.norm_log_one_add_sub_self_le hw1
  have hsq : ‖w‖ ^ 2 ≤ 4 * ‖q‖ ^ 2 := by
    nlinarith [norm_nonneg w, norm_nonneg q]
  have hb : ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ ‖w‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg ‖w‖)]
  exact h.trans (hb.trans hsq)

/-- The entire nonlinear prime-phase remainder is bounded before any
cutoff-frequency integration, with a sum of prime-square weights. -/
theorem norm_sum_normalized_prime_character_log_error {ι : Type*} (Q : Finset ι)
    (q z : ι → ℂ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4)
    (hz : ∀ p ∈ Q, ‖z p‖ ≤ 1) :
    ‖(∑ p ∈ Q, Complex.log (1 + q p * (1 - z p))) -
      ∑ p ∈ Q, q p * (1 - z p)‖ ≤ 4 * ∑ p ∈ Q, ‖q p‖ ^ 2 := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum
    (fun p hp ↦ norm_normalized_prime_character_log_error (q p) (z p) (hq p hp) (hz p hp)))

/-- Away from the finitely many smallest labels, the actual prime
feature satisfies the local logarithm bound throughout Re(s)>=1/2. -/
theorem norm_primeFeature_le_quarter {s : ℂ} (hs : 1 / 2 ≤ s.re)
    {p : ℕ} (hp : 16 ≤ p) : ‖zetaPrimeFeature s p‖ ≤ 1 / 4 := by
  rw [norm_zetaPrimeFeature]
  have hl : Real.log 16 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp)
  have hn := Real.log_natCast_nonneg p
  calc
    Real.exp (-s.re * Real.log p) ≤ Real.exp (-(1 / 2 : ℝ) * Real.log 16) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hs) hn]
    _ = 1 / 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      rw [show -(1 / 2 : ℝ) * (2 * Real.log 4) = -Real.log 4 by ring,
        Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      norm_num

/-- The actual prime-character nonlinear remainder has one uniform
bound for every finite prime set and every unit phase in Re(s)>1/2.
The finitely many small primes are kept outside this estimate. -/
theorem norm_sum_actual_prime_character_error_le (Q : Finset ℕ) (z : ℕ → ℂ)
    (hQ : ∀ p ∈ Q, 16 ≤ p) (hz : ∀ p ∈ Q, ‖z p‖ ≤ 1)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖(∑ p ∈ Q, Complex.log (1 + zetaPrimeFeature s p * (1 - z p))) -
      ∑ p ∈ Q, zetaPrimeFeature s p * (1 - z p)‖ ≤
      4 * ∑' n, zetaPrimeExpWeight (2 * s.re) n := by
  have h := norm_sum_normalized_prime_character_log_error Q (zetaPrimeFeature s) z
    (fun p hp ↦ norm_primeFeature_le_quarter hs.le (hQ p hp)) hz
  have he (p : ℕ) : ‖zetaPrimeFeature s p‖ ^ 2 = zetaPrimeExpWeight (2 * s.re) p := by
    rw [norm_zetaPrimeFeature, pow_two]
    unfold zetaPrimeExpWeight
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (summable_zetaPrimeExpWeight (by linarith : 1 < 2 * s.re)).sum_le_tsum Q
    (fun n _ ↦ (Real.exp_pos _).le)

/-- The two-variable deformed Euler factor separates its first-order
zeta quotient from an explicit quadratic local correction. -/
theorem deformed_euler_local_factor (q v : ℂ) (hq : 1 - q ≠ 0) (hv : 1 - v ≠ 0) :
    1 + q - v = ((1 - v) / (1 - q)) *
      (1 + (q * v - q ^ 2) / (1 - v)) := by
  field_simp
  ring

/-- A normalized real signed-prime character is not a probability
characteristic function: its squared modulus has the opposite sign. -/
theorem normalized_real_prime_character_normSq (q : ℝ) (z : ℂ)
    (hz : Complex.normSq z = 1) :
    Complex.normSq (1 + (q : ℂ) * (1 - z)) =
      1 + 2 * q * (1 + q) * (1 - z.re) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.mul_re, Complex.ofReal_re, Complex.sub_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_im, Complex.one_im, Complex.mul_im,
    Complex.sub_im, zero_sub, zero_add] at hz ⊢
  linear_combination q ^ 2 * hz

/-- For nonnegative real local weight, normalization gives expansion
or equality in every unit phase, rather than probabilistic contraction. -/
theorem one_le_normalized_real_prime_character_normSq (q : ℝ) (hq : 0 ≤ q)
    (z : ℂ) (hz : Complex.normSq z = 1) :
    1 ≤ Complex.normSq (1 + (q : ℂ) * (1 - z)) := by
  rw [normalized_real_prime_character_normSq q z hz]
  have h := hz
  rw [Complex.normSq_apply] at h
  have hre : 0 ≤ 1 - z.re := by nlinarith [sq_nonneg z.im, sq_nonneg (z.re - 1)]
  have hp : 0 ≤ 2 * q * (1 + q) * (1 - z.re) := by positivity
  linarith

/-- The exponential cost from absolute tail summation and a Cauchy
circle confined to Re(s)>1 is at least 2u. For u>1/2 this cost exceeds
one, so this particular bound cannot supply decay. This audits the
exponent expression; it is not a lower bound on the arithmetic carrier. -/
theorem absolute_completion_exponential_cost (u r delta : ℝ)
    (hu : 1 / 2 ≤ u) (hu1 : u ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1 / 2)
    (hdelta : delta ≤ 1 / 2 - r) :
    2 * u ≤ u ^ (1 + 2 * delta) / r := by
  have hu0 : 0 < u := by linarith
  have hloghalf : -1 ≤ Real.log (1 / 2 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog : -1 ≤ Real.log u := hloghalf.trans
    (Real.log_le_log (by norm_num) hu)
  have ha : 0 ≤ 1 - 2 * r := by linarith
  have hx : 2 * r ≤ u ^ (1 - 2 * r) := by
    rw [Real.rpow_def_of_pos hu0]
    have h := Real.add_one_le_exp (Real.log u * (1 - 2 * r))
    have hm := mul_le_mul_of_nonneg_right hlog ha
    nlinarith
  have he : u ^ (2 - 2 * r) = u * u ^ (1 - 2 * r) := by
    rw [show (2 - 2 * r : ℝ) = 1 + (1 - 2 * r) by ring, Real.rpow_add hu0,
      Real.rpow_one]
  apply (le_div_iff₀ hr).mpr
  calc
    2 * u * r = u * (2 * r) := by ring
    _ ≤ u * u ^ (1 - 2 * r) := mul_le_mul_of_nonneg_left hx hu0.le
    _ = u ^ (2 - 2 * r) := he.symm
    _ ≤ u ^ (1 + 2 * delta) :=
      Real.rpow_le_rpow_of_exponent_ge hu0 hu1 (by linarith)

end
end RiemannGaussian.ZetaSquarefreeSignedTail

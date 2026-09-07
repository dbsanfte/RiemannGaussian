import RiemannGaussian.MoebiusFiniteCancellation
import RiemannGaussian.EtaOddPowerQuadrature

/-!
# Finite Möbius sums with the original complex divisor weights

The actual finite Möbius prefix is transported to its complex Mellin weights
by an exact discrete Abel identity. The signed coefficients, endpoint term,
and full complex weight differences are retained before norms are taken.
-/

open Complex Filter
open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The literal finite Möbius sum with its full complex Dirichlet weight. -/
def complexMoebiusFinitePrefix (s : ℂ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.range M, ((μ (n + 1) : ℤ) : ℂ) * (n + 1 : ℂ) ^ (-s)

/-- The exact norm of an original complex divisor weight retains its real Mellin exponent. -/
theorem norm_moebiusMellinWeight (s : ℂ) (n : ℕ) :
    ‖(n + 1 : ℂ) ^ (-s)‖ = (n + 1 : ℝ) ^ (-s.re) := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos (y := -s) (by positivity : (0 : ℝ) < n + 1)
  simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Complex.neg_re] using h

/-- Exact finite summation by parts retains the endpoint and every complex difference of the original divisor weights. -/
theorem complexMoebiusFinitePrefix_eq_abel (s : ℂ) (M : ℕ) :
    complexMoebiusFinitePrefix s M =
      (moebiusFinitePrefix M : ℂ) * (M + 1 : ℂ) ^ (-s) +
        ∑ n ∈ Finset.range M, (moebiusFinitePrefix (n + 1) : ℂ) *
          ((n + 1 : ℂ) ^ (-s) - (n + 2 : ℂ) ^ (-s)) := by
  induction M with
  | zero => simp [complexMoebiusFinitePrefix, moebiusFinitePrefix]
  | succ M ih =>
    have hP : (moebiusFinitePrefix (M + 1) : ℂ) =
        (moebiusFinitePrefix M : ℂ) + ((μ (M + 1) : ℤ) : ℂ) := by
      simp [moebiusFinitePrefix, Finset.sum_range_succ]
    have hF : complexMoebiusFinitePrefix s (M + 1) =
        complexMoebiusFinitePrefix s M + ((μ (M + 1) : ℤ) : ℂ) * (M + 1 : ℂ) ^ (-s) := by
      simp [complexMoebiusFinitePrefix, Finset.sum_range_succ]
    rw [hF, ih, Finset.sum_range_succ, hP]
    push_cast
    ring_nf

/-- The original complex divisor-weight difference has a quantitative derivative bound at its genuine positive integer base. -/
theorem norm_moebiusMellinWeight_sub_succ_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖(n + 1 : ℂ) ^ (-s) - (n + 2 : ℂ) ^ (-s)‖ ≤
      ‖s‖ * (n + 1 : ℝ) ^ (-s.re - 1) := by
  have h := norm_cpow_sub_cpow_le_above (-s) (a := (n + 1 : ℝ))
    (x := (n + 2 : ℝ)) (y := (n + 1 : ℝ)) (by positivity)
    (by simp only [Complex.neg_re]; linarith) (by linarith) le_rfl
  simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.ofReal_ofNat, norm_neg, Complex.neg_re,
    show (n + 1 : ℝ) - (n + 2) = -1 by ring, abs_neg, abs_one, mul_one] using h

/-- The summable derivative mass of the actual positive-integer Mellin weights. -/
def moebiusMellinDerivativeMass (s : ℂ) : ℝ :=
  ∑' n : ℕ, (n + 1 : ℝ) ^ (-s.re - 1)

/-- The complete derivative mass converges for every complex weight in the positive half-plane. -/
theorem summable_moebiusMellinDerivativeMass {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ ↦ (n + 1 : ℝ) ^ (-s.re - 1)) := by
  have h := Real.summable_nat_rpow.mpr (show -s.re - 1 < -1 by linarith)
  have hshift := h.comp_injective
    (show Function.Injective (fun n : ℕ ↦ n + 1) by intro n m h; change n + 1 = m + 1 at h; omega)
  change Summable (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1)) at hshift
  simpa only [Nat.cast_add, Nat.cast_one] using hshift

/-- The actual derivative mass is nonnegative. -/
theorem moebiusMellinDerivativeMass_nonneg (s : ℂ) : 0 ≤ moebiusMellinDerivativeMass s :=
  tsum_nonneg fun n ↦ Real.rpow_nonneg (by positivity) _

/-- The original finite derivative-weight mass is bounded by its proved convergent whole series. -/
theorem sum_moebiusMellinDerivative_le {s : ℂ} (hs : 0 < s.re) (M : ℕ) :
    (∑ n ∈ Finset.range M, (n + 1 : ℝ) ^ (-s.re - 1)) ≤ moebiusMellinDerivativeMass s :=
  (summable_moebiusMellinDerivativeMass hs).sum_le_tsum _
    (fun n _ ↦ Real.rpow_nonneg (by positivity) _)

/-- The exact finite Abel identity gives a bound with the actual signed prefix sizes and the complete derivative-weight sum. -/
theorem norm_complexMoebiusFinitePrefix_le_abel {s : ℂ} (hs : 0 < s.re) (M : ℕ) :
    ‖complexMoebiusFinitePrefix s M‖ ≤ |moebiusFinitePrefix M| * (M + 1 : ℝ) ^ (-s.re) +
      ‖s‖ * ∑ n ∈ Finset.range M,
        |moebiusFinitePrefix (n + 1)| * (n + 1 : ℝ) ^ (-s.re - 1) := by
  rw [complexMoebiusFinitePrefix_eq_abel]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_moebiusMellinWeight]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ n ∈ Finset.range M, ‖(moebiusFinitePrefix (n + 1) : ℂ) *
        ((n + 1 : ℂ) ^ (-s) - (n + 2 : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range M, ‖s‖ *
        (|moebiusFinitePrefix (n + 1)| * (n + 1 : ℝ) ^ (-s.re - 1)) := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply (mul_le_mul_of_nonneg_left (norm_moebiusMellinWeight_sub_succ_le hs n) (abs_nonneg _)).trans_eq
      ring
    _ = _ := (Finset.mul_sum ..).symm

end

end RiemannGaussian

import RiemannGaussian.FiniteCircleEnergy

/-!
# Sampling a finite band of circle frequencies

The exact forward-difference multipliers of the finite Fourier polynomial
have an explicit norm bound. Orthogonality evaluates both complete-period
energies before the disjoint sampling estimate is applied. An integer grid
with period equal to block length times band budget gives a concrete bound.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

variable {Q : ℕ} [NeZero Q]

/-- The exact finite-circle increment has a bound in its unreduced
nonnegative integer frequency, with the literal period denominator. -/
theorem norm_stdAddChar_natCast_sub_one_le (r : ℕ) :
    ‖ZMod.stdAddChar (r : ZMod Q) - 1‖ ≤ 2 * Real.pi * r / (Q : ℝ) := by
  have heq : ZMod.stdAddChar (r : ZMod Q) =
      Complex.exp (Complex.I * ((2 * Real.pi * r / (Q : ℝ) : ℝ) : ℂ)) := by
    rw [← Int.cast_natCast, ZMod.stdAddChar_coe]
    push_cast
    congr 1
    ring
  rw [heq]
  have hp : 0 ≤ 2 * Real.pi * r / (Q : ℝ) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * r / (Q : ℝ)))

omit [NeZero Q] in
/-- The integer band embeds injectively into the finite circle when
its length does not exceed the literal period. -/
theorem natCast_zmod_injectiveOn_range {L : ℕ} (hLQ : L ≤ Q) :
    Set.InjOn (fun r : ℕ ↦ (r : ZMod Q)) (Finset.range L) := by
  intro r hr s hs heq
  have hrQ : r < Q := (Finset.mem_range.mp hr).trans_le hLQ
  have hsQ : s < Q := (Finset.mem_range.mp hs).trans_le hLQ
  have h := congrArg ZMod.val heq
  simpa only [ZMod.val_natCast_of_lt hrQ, ZMod.val_natCast_of_lt hsQ] using h

/-- Orthogonality evaluates the complete energy of the actual integer
frequency band with no aliasing between its columns. -/
theorem sum_range_finiteCircleBand_norm_sq {L : ℕ} (hLQ : L ≤ Q) (a : ℕ → ℂ) :
    (∑ n ∈ Finset.range Q,
      ‖finiteCircleSynthesis (Finset.range L) (fun r : ℕ ↦ (r : ZMod Q)) a n‖ ^ 2) =
      (Q : ℝ) * ∑ r ∈ Finset.range L, ‖a r‖ ^ 2 :=
  sum_range_finiteCircleSynthesis_norm_sq _ _ _ (natCast_zmod_injectiveOn_range hLQ)

/-- The full difference energy of the finite band is bounded using
the exact circle multipliers, retaining the period and band length. -/
theorem sum_range_finiteCircleBand_difference_sq_le {L : ℕ} (hLQ : L ≤ Q) (a : ℕ → ℂ) :
    (∑ n ∈ Finset.range Q,
      ‖finiteCircleSynthesis (Finset.range L) (fun r : ℕ ↦ (r : ZMod Q)) a (n + 1) -
        finiteCircleSynthesis (Finset.range L) (fun r : ℕ ↦ (r : ZMod Q)) a n‖ ^ 2) ≤
      (Q : ℝ) * (2 * Real.pi * L / (Q : ℝ)) ^ 2 * ∑ r ∈ Finset.range L, ‖a r‖ ^ 2 := by
  simp_rw [finiteCircleSynthesis_forward_difference]
  rw [sum_range_finiteCircleBand_norm_sq hLQ]
  calc
    _ ≤ (Q : ℝ) * ∑ r ∈ Finset.range L,
        (2 * Real.pi * L / (Q : ℝ)) ^ 2 * ‖a r‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Q)
      apply Finset.sum_le_sum
      intro r hr
      have hc : ‖ZMod.stdAddChar (r : ZMod Q) - 1‖ ≤ 2 * Real.pi * L / (Q : ℝ) := by
        apply (norm_stdAddChar_natCast_sub_one_le r).trans
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg Q)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Finset.mem_range.mp hr).le) (by positivity)
      rw [norm_mul, mul_pow]
      have h := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hc) (sq_nonneg ‖a r‖)
      simpa only [mul_comm] using h
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The separated samples of the finite band have an explicit bound
in the complete coefficient energy and the actual integer scales. -/
theorem sum_norm_sq_finiteCircleBand_separated_le {L h : ℕ} (a : ℕ → ℂ)
    (s : Finset ℕ) (hh : 0 < h) (hhQ : h ≤ Q) (hLQ : L ≤ Q)
    (hsQ : ∀ n ∈ s, n < Q)
    (hsep : ∀ n ∈ s, ∀ m ∈ s, n < m → n + h ≤ m) :
    (∑ n ∈ s, ‖finiteCircleSynthesis (Finset.range L) (fun r : ℕ ↦ (r : ZMod Q)) a n‖ ^ 2) ≤
      (4 * Q / (h : ℝ) + 4 * h * Q * (2 * Real.pi * L / (Q : ℝ)) ^ 2) *
        ∑ r ∈ Finset.range L, ‖a r‖ ^ 2 := by
  apply (sum_norm_sq_separated_sampling_le _ s hh hhQ
    (finiteCircleSynthesis_periodic _ _ _) hsQ hsep).trans
  rw [sum_range_finiteCircleBand_norm_sq hLQ]
  have hd := mul_le_mul_of_nonneg_left (sum_range_finiteCircleBand_difference_sq_le hLQ a)
    (by positivity : (0 : ℝ) ≤ 4 * h)
  calc
    _ ≤ (4 / (h : ℝ)) * ((Q : ℝ) * ∑ r ∈ Finset.range L, ‖a r‖ ^ 2) +
        (4 * h) * ((Q : ℝ) * (2 * Real.pi * L / (Q : ℝ)) ^ 2 *
          ∑ r ∈ Finset.range L, ‖a r‖ ^ 2) := add_le_add le_rfl hd
    _ = _ := by ring

/-- A conservative explicit constant for the finite circle sampling bound. -/
def finiteCircleSamplingConstant : ℝ := 4 + 16 * Real.pi ^ 2

/-- The finite sampling constant is strictly positive. -/
theorem finiteCircleSamplingConstant_pos : 0 < finiteCircleSamplingConstant := by
  unfold finiteCircleSamplingConstant
  positivity

/-- Choosing the period as block length times a band budget removes
the auxiliary grid size from the separated sampling bound. -/
theorem sum_norm_sq_finiteCircleBand_grid_le {L h T : ℕ} (a : ℕ → ℂ)
    (s : Finset ℕ) (hh : 0 < h) (hT : 0 < T) (hQT : Q = h * T) (hLT : L ≤ T)
    (hsQ : ∀ n ∈ s, n < Q)
    (hsep : ∀ n ∈ s, ∀ m ∈ s, n < m → n + h ≤ m) :
    (∑ n ∈ s, ‖finiteCircleSynthesis (Finset.range L) (fun r : ℕ ↦ (r : ZMod Q)) a n‖ ^ 2) ≤
      finiteCircleSamplingConstant * T * ∑ r ∈ Finset.range L, ‖a r‖ ^ 2 := by
  have hhQ : h ≤ Q := by rw [hQT]; nlinarith
  have hLQ : L ≤ Q := by rw [hQT]; nlinarith
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hQTR : (Q : ℝ) = (h : ℝ) * T := by exact_mod_cast hQT
  have hLTR : (L : ℝ) ≤ T := by exact_mod_cast hLT
  apply (sum_norm_sq_finiteCircleBand_separated_le a s hh hhQ hLQ hsQ hsep).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun r _ ↦ sq_nonneg _))
  have heq : 4 * Q / (h : ℝ) + 4 * h * Q * (2 * Real.pi * L / (Q : ℝ)) ^ 2 =
      4 * T + 16 * Real.pi ^ 2 * ((L : ℝ) ^ 2 / T) := by
    rw [hQTR]
    field_simp
    ring
  rw [heq]
  have hsq : (L : ℝ) ^ 2 / T ≤ T := by
    apply (div_le_iff₀ hTR).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  unfold finiteCircleSamplingConstant
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 16 * Real.pi ^ 2)]

end

end RiemannGaussian

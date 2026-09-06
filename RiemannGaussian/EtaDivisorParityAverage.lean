import RiemannGaussian.EtaDivisorParityGcd

/-!
# Arbitrary-window covariance of literal eta divisor phases

Every divisor pair has its exact gcd covariance, including the reduced
parity colours. The uncompleted last arithmetic period has an explicit
error depending on both divisors and the actual averaging length.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The full gcd covariance keeps the two reduced parity colours. -/
def pairedEtaDivisorParityCovariance (d e : ℕ) : ℝ :=
  if Odd (d / Nat.gcd d e) ∧ Odd (e / Nat.gcd d e) then
    (Nat.gcd d e : ℝ) ^ 2 / ((d : ℝ) * e) else 0

/-- The exact phase covariance is nonnegative. -/
theorem pairedEtaDivisorParityCovariance_nonneg (d e : ℕ) :
    0 ≤ pairedEtaDivisorParityCovariance d e := by
  unfold pairedEtaDivisorParityCovariance
  split_ifs <;> positivity

/-- Keeping the parity selector never increases the full gcd majorant. -/
theorem pairedEtaDivisorParityCovariance_le_gcd (d e : ℕ) :
    pairedEtaDivisorParityCovariance d e ≤ (Nat.gcd d e : ℝ) ^ 2 / ((d : ℝ) * e) := by
  unfold pairedEtaDivisorParityCovariance
  split_ifs
  · rfl
  · positivity

/-- The exact covariance of positive divisor phases is at most one. -/
theorem pairedEtaDivisorParityCovariance_le_one {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    pairedEtaDivisorParityCovariance d e ≤ 1 := by
  apply (pairedEtaDivisorParityCovariance_le_gcd d e).trans
  have hgd : (Nat.gcd d e : ℝ) ≤ d := by exact_mod_cast Nat.le_of_dvd hd (Nat.gcd_dvd_left d e)
  have hge : (Nat.gcd d e : ℝ) ≤ e := by exact_mod_cast Nat.le_of_dvd he (Nat.gcd_dvd_right d e)
  rw [div_le_iff₀ (by positivity : 0 < (d : ℝ) * e)]
  nlinarith [mul_le_mul hgd hge (Nat.cast_nonneg _) (Nat.cast_nonneg d)]

/-- The signed raw product has absolute value exactly one. -/
theorem abs_pairedEtaDivisorParityProduct (d e M : ℕ) :
    |(pairedEtaDivisorParityProduct d e M : ℝ)| = 1 := by
  rw [pairedEtaDivisorParityProduct, Int.cast_mul, abs_mul]
  have hd := congrArg (fun z : ℤ ↦ (z : ℝ)) (abs_pairedEtaDirichletSign (M / d))
  have he := congrArg (fun z : ℤ ↦ (z : ℝ)) (abs_pairedEtaDirichletSign (M / e))
  simp only [Int.cast_abs, Int.cast_one] at hd he
  rw [hd, he]
  norm_num

/-- Every complete period has the exact real gcd covariance as its
mean, preserving all same-colour correlations. -/
theorem sum_range_pairedEtaDivisorParity_eq_period_mul_covariance (d e : ℕ)
    (hd : 0 < d) (he : 0 < e) :
    (∑ M ∈ Finset.range (2 * d * e), (pairedEtaDivisorParityProduct d e M : ℝ)) =
      (2 * d * e : ℕ) * pairedEtaDivisorParityCovariance d e := by
  rw [← Int.cast_sum, sum_range_pairedEtaDivisorParity_eq_gcd d e hd he,
    pairedEtaDivisorParityCovariance]
  split_ifs
  · push_cast
    field_simp
  · simp

/-- On any actual averaging window, the unfinished period has a
uniform error with both divisor sizes explicitly retained. -/
theorem abs_sum_pairedEtaDivisorParity_sub_covariance_le (A L d e : ℕ)
    (hd : 0 < d) (he : 0 < e) :
    |(∑ r ∈ Finset.range L, (pairedEtaDivisorParityProduct d e (A + r) : ℝ)) -
      (L : ℝ) * pairedEtaDivisorParityCovariance d e| ≤ 4 * d * e := by
  let P : ℕ := 2 * d * e
  let c := pairedEtaDivisorParityCovariance d e
  let f : ℕ → ℝ := fun r ↦ (pairedEtaDivisorParityProduct d e (A + r) : ℝ) - c
  have hP : 0 < P := by dsimp [P]; positivity
  have hper : Function.Periodic f P := by
    intro r
    dsimp [f]
    rw [← Nat.add_assoc, pairedEtaDivisorParityProduct_periodic hd he (A + r)]
  have hrawper : Function.Periodic (fun r ↦ (pairedEtaDivisorParityProduct d e r : ℝ)) P :=
    fun r ↦ congrArg (fun z : ℤ ↦ (z : ℝ)) (pairedEtaDivisorParityProduct_periodic hd he r)
  have hzero : (∑ r ∈ Finset.range P, f r) = 0 := by
    dsimp [f]
    rw [Finset.sum_sub_distrib, sum_range_nat_periodic_shift hrawper,
      sum_range_pairedEtaDivisorParity_eq_period_mul_covariance d e hd he]
    simp [c, P]
  have hwhole : (∑ r ∈ Finset.range (P * (L / P)), f r) = 0 := by
    rw [sum_range_nat_periodic_mul hper, hzero, smul_zero]
  have hbound (r : ℕ) : |f r| ≤ 2 := by
    have hc := pairedEtaDivisorParityCovariance_nonneg d e
    have hc1 := pairedEtaDivisorParityCovariance_le_one hd he
    apply (abs_sub _ _).trans
    rw [abs_pairedEtaDivisorParityProduct, abs_of_nonneg hc]
    linarith
  have hsum : |∑ r ∈ Finset.range L, f r| ≤ 4 * d * e := by
    conv_lhs => rw [← Nat.mod_add_div L P, Nat.add_comm]
    rw [Finset.sum_range_add, hwhole, zero_add]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _r ∈ Finset.range (L % P), (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        exact hbound _
      _ = (L % P : ℕ) * (2 : ℝ) := by simp
      _ ≤ (P : ℝ) * 2 := mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.mod_lt L hP).le) (by norm_num)
      _ = _ := by dsimp [P]; push_cast; ring
  simpa only [f, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum

/-- The exact averaged raw phase product over a literal integer window. -/
def pairedEtaDivisorParityAverage (A L d e : ℕ) : ℝ :=
  (∑ r ∈ Finset.range L, (pairedEtaDivisorParityProduct d e (A + r) : ℝ)) / L

/-- The arbitrary-window covariance error decays with the averaging
length, while keeping the complete divisor dependence. -/
theorem abs_pairedEtaDivisorParityAverage_sub_covariance_le (A : ℕ) {L d e : ℕ}
    (hL : 0 < L) (hd : 0 < d) (he : 0 < e) :
    |pairedEtaDivisorParityAverage A L d e - pairedEtaDivisorParityCovariance d e| ≤
      4 * d * e / (L : ℝ) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have heq : pairedEtaDivisorParityAverage A L d e - pairedEtaDivisorParityCovariance d e =
      ((∑ r ∈ Finset.range L, (pairedEtaDivisorParityProduct d e (A + r) : ℝ)) -
        (L : ℝ) * pairedEtaDivisorParityCovariance d e) / L := by
    unfold pairedEtaDivisorParityAverage
    field_simp
  rw [heq, abs_div, abs_of_pos hLp]
  exact div_le_div_of_nonneg_right (abs_sum_pairedEtaDivisorParity_sub_covariance_le A L d e hd he) hLp.le

end

end RiemannGaussian

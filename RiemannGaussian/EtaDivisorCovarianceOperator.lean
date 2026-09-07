import RiemannGaussian.NatRectangleEnergy

/-!
# A coefficient-energy bound for the literal divisor covariance

The exact gcd covariance is symmetric and nonnegative entrywise. A
common-divisor expansion controls each complete row by a squared harmonic
sum. The resulting operator estimate can therefore keep arbitrary signed
product coefficients in a divisor convolution.
-/

open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Complementary actual divisors identify their normalized sum with
the reciprocal-divisor sum, without extending the divisor support. -/
theorem sum_divisors_div_self_eq_inv {d : ℕ} (hd : 0 < d) :
    (∑ g ∈ d.divisors, (g : ℝ) / d) = ∑ g ∈ d.divisors, 1 / (g : ℝ) := by
  calc
    _ = ∑ g ∈ d.divisors, 1 / ((d / g : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro g hg
      have hgp : 0 < g := Nat.pos_of_mem_divisors hg
      have hgd := (Nat.mem_divisors.mp hg).1
      have hq : 0 < d / g := (Nat.one_le_div_iff hgp).mpr (Nat.le_of_dvd hd hgd)
      have hgR : (0 : ℝ) < g := by exact_mod_cast hgp
      have hqR : (0 : ℝ) < (d / g : ℕ) := by exact_mod_cast hq
      rw [show (d : ℝ) = (g : ℝ) * (d / g : ℕ) by exact_mod_cast (Nat.mul_div_cancel' hgd).symm]
      field_simp
    _ = _ := Nat.sum_div_divisors d (fun n ↦ 1 / (n : ℝ))

/-- Every complete gcd-covariance row is bounded by the squared
harmonic interval sum. Both coordinates and all common divisors remain
in the proof until the row is estimated. -/
theorem sum_Icc_gcd_sq_div_row_le_harmonic_sq {T d : ℕ} (hd : d ∈ Finset.Icc 1 T) :
    (∑ e ∈ Finset.Icc 1 T, (Nat.gcd d e : ℝ) ^ 2 / ((d : ℝ) * e)) ≤
      (∑ g ∈ Finset.Icc 1 T, 1 / (g : ℝ)) ^ 2 := by
  have hdp : 0 < d := (Finset.mem_Icc.mp hd).1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdp
  let H := ∑ g ∈ Finset.Icc 1 T, 1 / (g : ℝ)
  have hH : 0 ≤ H := Finset.sum_nonneg (fun g _ ↦ by positivity)
  calc
    _ ≤ ∑ e ∈ Finset.Icc 1 T, ∑ g ∈ d.divisors,
        ((g : ℝ) ^ 2 / d) * (if g ∣ e then 1 / (e : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro e he
      have hgm : Nat.gcd d e ∈ d.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left d e, hdp.ne'⟩
      have h := Finset.single_le_sum (f := fun g : ℕ ↦
        ((g : ℝ) ^ 2 / d) * (if g ∣ e then 1 / (e : ℝ) else 0))
        (fun g _ ↦ by split_ifs <;> positivity) hgm
      simpa only [if_pos (Nat.gcd_dvd_right d e), div_eq_mul_inv, one_mul, mul_inv, mul_assoc] using h
    _ = ∑ g ∈ d.divisors, ((g : ℝ) ^ 2 / d) *
        ∑ e ∈ Finset.Icc 1 T, if g ∣ e then 1 / (e : ℝ) else 0 := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ g ∈ d.divisors, ((g : ℝ) / d) *
        ∑ e ∈ Finset.Icc 1 (T / g), 1 / (e : ℝ) := by
      apply Finset.sum_congr rfl
      intro g hg
      have hgp := Nat.pos_of_mem_divisors hg
      have hgR : (0 : ℝ) < g := by exact_mod_cast hgp
      rw [sum_Icc_dvd_inv_eq hgp]
      field_simp
    _ ≤ ∑ g ∈ d.divisors, ((g : ℝ) / d) * H := by
      apply Finset.sum_le_sum
      intro g hg
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc le_rfl (Nat.div_le_self T g)) (fun e _ _ ↦ by positivity)
    _ = (∑ g ∈ d.divisors, 1 / (g : ℝ)) * H := by
      rw [← Finset.sum_mul, sum_divisors_div_self_eq_inv hdp]
    _ ≤ H * H := by
      apply mul_le_mul_of_nonneg_right _ hH
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun g _ _ ↦ by positivity)
      intro g hg
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hg,
        (Nat.le_of_dvd hdp (Nat.mem_divisors.mp hg).1).trans (Finset.mem_Icc.mp hd).2⟩
    _ = _ := by dsimp [H]; ring

/-- The actual quotient-parity covariance inherits the complete
row bound without an independence assumption on its divisor colours. -/
theorem sum_Icc_pairedEtaDivisorParityCovariance_row_le {T d : ℕ}
    (hd : d ∈ Finset.Icc 1 T) :
    (∑ e ∈ Finset.Icc 1 T, pairedEtaDivisorParityCovariance d e) ≤
      (∑ g ∈ Finset.Icc 1 T, 1 / (g : ℝ)) ^ 2 := by
  apply le_trans _ (sum_Icc_gcd_sq_div_row_le_harmonic_sq hd)
  exact Finset.sum_le_sum (fun e _ ↦ pairedEtaDivisorParityCovariance_le_gcd d e)

/-- Exchanging the actual divisor coordinates preserves both reduced
parity conditions and the complete gcd covariance. -/
theorem pairedEtaDivisorParityCovariance_comm (d e : ℕ) :
    pairedEtaDivisorParityCovariance d e = pairedEtaDivisorParityCovariance e d := by
  simp [pairedEtaDivisorParityCovariance, Nat.gcd_comm, and_comm, mul_comm]

/-- The full signed covariance form is controlled by the coefficient
energy, retaining every off-diagonal entry until the row bound is used. -/
theorem sum_Icc_weighted_pairedEtaDivisorParityCovariance_le_harmonic_sq
    (w : ℕ → ℝ) (T : ℕ) :
    (∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
      w d * w e * pairedEtaDivisorParityCovariance d e) ≤
      (∑ g ∈ Finset.Icc 1 T, 1 / (g : ℝ)) ^ 2 *
        ∑ d ∈ Finset.Icc 1 T, w d ^ 2 := by
  let s := Finset.Icc 1 T
  let E := ∑ d ∈ s, w d ^ 2 * ∑ e ∈ s, pairedEtaDivisorParityCovariance d e
  have hleft : (∑ d ∈ s, ∑ e ∈ s, w d ^ 2 * pairedEtaDivisorParityCovariance d e) = E := by
    simp only [E, Finset.mul_sum]
  have hright : (∑ d ∈ s, ∑ e ∈ s, w e ^ 2 * pairedEtaDivisorParityCovariance d e) = E := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [pairedEtaDivisorParityCovariance_comm, Finset.mul_sum]
  calc
    _ ≤ ∑ d ∈ s, ∑ e ∈ s,
        (w d ^ 2 * pairedEtaDivisorParityCovariance d e +
          w e ^ 2 * pairedEtaDivisorParityCovariance d e) / 2 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      have h := mul_le_mul_of_nonneg_right
        (show 2 * w d * w e ≤ w d ^ 2 + w e ^ 2 by nlinarith [sq_nonneg (w d - w e)])
        (pairedEtaDivisorParityCovariance_nonneg d e)
      nlinarith
    _ = ((∑ d ∈ s, ∑ e ∈ s, w d ^ 2 * pairedEtaDivisorParityCovariance d e) +
        (∑ d ∈ s, ∑ e ∈ s, w e ^ 2 * pairedEtaDivisorParityCovariance d e)) / 2 := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
    _ = E := by rw [hleft, hright]; ring
    _ ≤ (∑ g ∈ Finset.Icc 1 T, 1 / (g : ℝ)) ^ 2 *
        ∑ d ∈ Finset.Icc 1 T, w d ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      have h := mul_le_mul_of_nonneg_left
        (sum_Icc_pairedEtaDivisorParityCovariance_row_le hd) (sq_nonneg (w d))
      simpa only [mul_comm] using h

/-- An explicit logarithmic operator bound applies to arbitrary signed
divisor coefficients, including the actual inverse product fibers. -/
theorem sum_Icc_weighted_pairedEtaDivisorParityCovariance_le_log_sq
    (w : ℕ → ℝ) (T : ℕ) :
    (∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
      w d * w e * pairedEtaDivisorParityCovariance d e) ≤
      (1 + Real.log T) ^ 2 * ∑ d ∈ Finset.Icc 1 T, w d ^ 2 := by
  apply (sum_Icc_weighted_pairedEtaDivisorParityCovariance_le_harmonic_sq w T).trans
  have hH : 0 ≤ ∑ g ∈ Finset.Icc 1 T, 1 / (g : ℝ) :=
    Finset.sum_nonneg (fun g _ ↦ by positivity)
  have h : (∑ g ∈ Finset.Icc 1 T, 1 / (g : ℝ)) ≤ 1 + Real.log T := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
      using harmonic_le_one_add_log T
  exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ hH (hH.trans h)).mpr h)
    (Finset.sum_nonneg (fun d _ ↦ sq_nonneg (w d)))

end

end RiemannGaussian

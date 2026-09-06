import RiemannGaussian.EtaDivisorParityAverage
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A growing-family bound for the full gcd covariance

The complete covariance is retained before its scalar majorant. A common
divisor decomposition and a finite Cauchy--Schwarz estimate bound the whole
gcd matrix by a linear times harmonic cost, rather than a quadratic count
of unrelated divisor pairs.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The finite inverse-square sum has an explicit telescoping bound. -/
theorem sum_Icc_inv_sq_le_two (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) ^ 2) ≤ 2 := by
  have h (n : ℕ) : (∑ k ∈ Finset.range n, (1 / ((k : ℝ) + 1)) ^ 2) ≤ 2 - 2 / ((n : ℝ) + 1) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have ht : (1 / ((n : ℝ) + 1)) ^ 2 ≤ 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 2) := by
        field_simp
        nlinarith
      push_cast
      rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
      linarith
  have he : (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) ^ 2) =
      ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1)) ^ 2 := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  rw [he]
  exact (h N).trans (sub_le_self _ (by positivity))

/-- A finite harmonic sum has square at most twice its length. -/
theorem sum_Icc_inv_sq_sum_le_two_mul (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)) ^ 2 ≤ 2 * N := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N)
    (fun n ↦ 1 / (n : ℝ)) (fun _ ↦ (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul] at h
  have hs := mul_le_mul_of_nonneg_right (sum_Icc_inv_sq_le_two N) (Nat.cast_nonneg (α := ℝ) N)
  simpa only [mul_one] using h.trans hs

/-- Multiples of one positive divisor retain an exact divided-cutoff
harmonic sum, including every endpoint of the finite range. -/
theorem sum_Icc_dvd_inv_eq {g : ℕ} (hg : 0 < g) (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, if g ∣ d then 1 / (d : ℝ) else 0) =
      (1 / (g : ℝ)) * (∑ a ∈ Finset.Icc 1 (D / g), 1 / (a : ℝ)) := by
  rw [← Finset.sum_filter, Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun a _ ↦ g * a)
  · intro a ha
    rw [Finset.mem_Icc] at ha
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by nlinarith [ha.1], (Nat.mul_le_mul_left g ha.2).trans (Nat.mul_div_le D g)⟩, dvd_mul_right g a⟩
  · intro a ha b hb heq
    exact Nat.eq_of_mul_eq_mul_left hg heq
  · intro d hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    refine ⟨d / g, ?_, Nat.mul_div_cancel' hd.2⟩
    rw [Finset.mem_Icc]
    have hgd : g ≤ d := Nat.le_of_dvd hd.1.1 hd.2
    exact ⟨(Nat.one_le_div_iff hg).mpr hgd, Nat.div_le_div_right hd.1.2⟩
  · intro a ha
    push_cast
    simp only [one_div, mul_inv]

/-- Keeping every common divisor bounds the full gcd matrix before
estimating its divided-cutoff harmonic sums. -/
theorem sum_Icc_gcd_sq_div_le_common_divisors (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      (Nat.gcd d e : ℝ) ^ 2 / ((d : ℝ) * e)) ≤
    ∑ g ∈ Finset.Icc 1 D, (g : ℝ) ^ 2 *
      (∑ d ∈ Finset.Icc 1 D, if g ∣ d then 1 / (d : ℝ) else 0) ^ 2 := by
  let s := Finset.Icc 1 D
  let w : ℕ → ℕ → ℝ := fun g d ↦ if g ∣ d then 1 / (d : ℝ) else 0
  have hw (g d : ℕ) : 0 ≤ w g d := by dsimp [w]; split_ifs <;> positivity
  calc
    _ ≤ ∑ d ∈ s, ∑ e ∈ s, ∑ g ∈ s, (g : ℝ) ^ 2 * w g d * w g e := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      have hdp : 0 < d := (Finset.mem_Icc.mp hd).1
      have hgp : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hdp
      have hgm : Nat.gcd d e ∈ s := Finset.mem_Icc.mpr
        ⟨hgp, (Nat.le_of_dvd hdp (Nat.gcd_dvd_left d e)).trans (Finset.mem_Icc.mp hd).2⟩
      have h := Finset.single_le_sum (f := fun g : ℕ ↦ (g : ℝ) ^ 2 * w g d * w g e)
        (fun g _ ↦ mul_nonneg (mul_nonneg (sq_nonneg _) (hw g d)) (hw g e)) hgm
      simpa only [w, if_pos (Nat.gcd_dvd_left d e), if_pos (Nat.gcd_dvd_right d e),
        div_eq_mul_inv, one_mul, mul_inv, mul_assoc] using h
    _ = ∑ d ∈ s, ∑ g ∈ s, ∑ e ∈ s, (g : ℝ) ^ 2 * w g d * w g e := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ g ∈ s, ∑ d ∈ s, ∑ e ∈ s, (g : ℝ) ^ 2 * w g d * w g e := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g hg
      simp only [← Finset.mul_sum, ← Finset.sum_mul, w]
      ring

/-- The whole gcd matrix has linear times harmonic cost, uniformly in
the number of divisor columns. -/
theorem sum_Icc_gcd_sq_div_le_two_mul_harmonic (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      (Nat.gcd d e : ℝ) ^ 2 / ((d : ℝ) * e)) ≤
      2 * D * (∑ g ∈ Finset.Icc 1 D, 1 / (g : ℝ)) := by
  apply (sum_Icc_gcd_sq_div_le_common_divisors D).trans
  calc
    _ = ∑ g ∈ Finset.Icc 1 D, (∑ a ∈ Finset.Icc 1 (D / g), 1 / (a : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro g hg
      have hgp : 0 < g := (Finset.mem_Icc.mp hg).1
      rw [sum_Icc_dvd_inv_eq hgp]
      field_simp
    _ ≤ ∑ g ∈ Finset.Icc 1 D, (2 : ℝ) * (D / g : ℕ) := by
      apply Finset.sum_le_sum
      intro g hg
      exact sum_Icc_inv_sq_sum_le_two_mul _
    _ ≤ ∑ g ∈ Finset.Icc 1 D, 2 * D * (1 / (g : ℝ)) := by
      apply Finset.sum_le_sum
      intro g hg
      have hgp : (0 : ℝ) < g := by exact_mod_cast (Finset.mem_Icc.mp hg).1
      have hdiv : (D / g : ℕ) ≤ (D : ℝ) / g := by
        apply (le_div_iff₀ hgp).mpr
        exact_mod_cast Nat.div_mul_le_self D g
      simpa only [div_eq_mul_inv, one_mul, mul_assoc] using
        mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
    _ = _ := by rw [Finset.mul_sum]

/-- The literal phase covariance matrix is bounded by the same full
gcd sum, with no independence assumption on divisor colours. -/
theorem sum_Icc_pairedEtaDivisorParityCovariance_le (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      pairedEtaDivisorParityCovariance d e) ≤
      2 * D * (∑ g ∈ Finset.Icc 1 D, 1 / (g : ℝ)) := by
  apply le_trans _ (sum_Icc_gcd_sq_div_le_two_mul_harmonic D)
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro e he
  exact pairedEtaDivisorParityCovariance_le_gcd d e

/-- An explicit logarithmic bound for the complete growing phase
covariance matrix. -/
theorem sum_Icc_pairedEtaDivisorParityCovariance_le_log (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      pairedEtaDivisorParityCovariance d e) ≤ 2 * D * (1 + Real.log D) := by
  apply (sum_Icc_pairedEtaDivisorParityCovariance_le D).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    using harmonic_le_one_add_log D

end

end RiemannGaussian

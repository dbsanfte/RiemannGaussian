import RiemannGaussian.MoebiusFiniteMellin
import RiemannGaussian.EtaCurrentPowerSum

/-!
# Cancellation bounds for the actual finite complex Möbius sums

The proved ordinary finite cancellation is inserted into the exact complex
Abel formula. Both its endpoint term and its full derivative sum are bounded.
For each complex weight in the open critical strip, every prescribed
coefficient of the natural power scale has one finite all-cutoff remainder.
-/

open Complex

namespace RiemannGaussian

noncomputable section

/-- Finite cancellation survives the original complex Mellin weights, with one remainder valid at every arithmetic cutoff. -/
theorem exists_complexMoebiusFinitePrefix_power_remainder {s : ℂ}
    (hs : 0 < s.re) (hsone : s.re < 1) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ,
      ‖complexMoebiusFinitePrefix s M‖ ≤ eps * (M + 1 : ℝ) ^ (1 - s.re) + C := by
  let A := 1 + ‖s‖ / (1 - s.re)
  have hA : 0 < A := by dsimp [A]; positivity
  let delta := eps / A
  have hd : 0 < delta := div_pos heps hA
  have hdA : delta * A = eps := by dsimp [delta]; field_simp
  obtain ⟨B, hB, hprefix⟩ := exists_moebiusFinitePrefix_linear_remainder hd
  let C := B * (1 + ‖s‖ * moebiusMellinDerivativeMass s)
  have hZ := moebiusMellinDerivativeMass_nonneg s
  refine ⟨C, by dsimp [C]; positivity, fun M ↦ ?_⟩
  have hMpos : (0 : ℝ) < M + 1 := by positivity
  have hMone : (1 : ℝ) ≤ M + 1 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  have hneg : (M + 1 : ℝ) ^ (-s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hMone (by linarith)
  have hpower (n : ℕ) :
      (n + 1 : ℝ) * (n + 1 : ℝ) ^ (-s.re) = (n + 1 : ℝ) ^ (1 - s.re) := by
    rw [show 1 - s.re = 1 + (-s.re) by ring, Real.rpow_add (by positivity), Real.rpow_one]
  have hendpoint : |moebiusFinitePrefix M| * (M + 1 : ℝ) ^ (-s.re) ≤
      delta * (M + 1 : ℝ) ^ (1 - s.re) + B := by
    calc
      _ ≤ (delta * M + B) * (M + 1 : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (hprefix M) (Real.rpow_nonneg hMpos.le _)
      _ ≤ (delta * (M + 1 : ℝ)) * (M + 1 : ℝ) ^ (-s.re) + B := by
        have hfirst := mul_le_mul_of_nonneg_right
          (show delta * M ≤ delta * (M + 1 : ℝ) by nlinarith) (Real.rpow_nonneg hMpos.le (-s.re))
        have hlast := mul_le_mul_of_nonneg_left hneg hB
        nlinarith
      _ = _ := by rw [mul_assoc, hpower]
  have hweight (n : ℕ) :
      (n + 1 : ℝ) * (n + 1 : ℝ) ^ (-s.re - 1) = (n + 1 : ℝ) ^ (-s.re) := by
    calc
      _ = (n + 1 : ℝ) ^ (1 : ℝ) * (n + 1 : ℝ) ^ (-s.re - 1) := by rw [Real.rpow_one]
      _ = (n + 1 : ℝ) ^ (1 + (-s.re - 1)) := (Real.rpow_add (by positivity) _ _).symm
      _ = _ := by congr 1; ring
  have hsum : (∑ n ∈ Finset.range M,
      |moebiusFinitePrefix (n + 1)| * (n + 1 : ℝ) ^ (-s.re - 1)) ≤
        delta * ((M + 1 : ℝ) ^ (1 - s.re) / (1 - s.re)) + B * moebiusMellinDerivativeMass s := by
    calc
      _ ≤ ∑ n ∈ Finset.range M,
          (delta * (n + 1 : ℝ) ^ (-s.re) + B * (n + 1 : ℝ) ^ (-s.re - 1)) := by
        apply Finset.sum_le_sum
        intro n _
        have hp := hprefix (n + 1)
        simp only [Nat.cast_add, Nat.cast_one] at hp
        apply (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (by positivity) _)).trans_eq
        rw [add_mul, mul_assoc, hweight]
      _ = delta * (∑ n ∈ Finset.range M, (n + 1 : ℝ) ^ (-s.re)) +
          B * (∑ n ∈ Finset.range M, (n + 1 : ℝ) ^ (-s.re - 1)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hd.le
          simpa only [neg_add_eq_sub] using
            sum_range_nat_add_one_rpow_le (by linarith : -1 < -s.re) (by linarith : -s.re ≤ 0) M
        · exact mul_le_mul_of_nonneg_left (sum_moebiusMellinDerivative_le hs M) hB
  calc
    _ ≤ |moebiusFinitePrefix M| * (M + 1 : ℝ) ^ (-s.re) +
        ‖s‖ * ∑ n ∈ Finset.range M, |moebiusFinitePrefix (n + 1)| * (n + 1 : ℝ) ^ (-s.re - 1) :=
      norm_complexMoebiusFinitePrefix_le_abel hs M
    _ ≤ (delta * (M + 1 : ℝ) ^ (1 - s.re) + B) +
        ‖s‖ * (delta * ((M + 1 : ℝ) ^ (1 - s.re) / (1 - s.re)) +
          B * moebiusMellinDerivativeMass s) :=
      add_le_add hendpoint (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))
    _ = (delta * A) * (M + 1 : ℝ) ^ (1 - s.re) + C := by dsimp [A, C]; ring
    _ = _ := by rw [hdA]

end

end RiemannGaussian

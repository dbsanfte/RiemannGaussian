import RiemannGaussian.EtaMoebiusLogHarmonicBound

/-!
# Signed harmonic Möbius tails against monotone finite weights

Finite summation by parts retains the original harmonic Möbius prefixes
at both endpoints and every weight increment. A uniform small bound on
those actual prefixes then controls any nonnegative decreasing weight
on the same physical interval. No infinite rearrangement is used.
-/

open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

private theorem harmonic_eq_range (N : ℕ) :
    moebiusHarmonicPrefix N = ∑ n ∈ Finset.range (N + 1), (μ n : ℝ) / n := by
  rw [moebiusHarmonicPrefix,
    show Finset.range (N + 1) = Finset.Icc 1 N ∪ {0} by ext n; simp; omega,
    Finset.sum_union (by simp)]
  simp

/-- The complete finite weighted harmonic Möbius tail has its exact signed endpoint and increment formula. -/
theorem sum_moebiusHarmonic_weight_eq_by_parts {D M : ℕ} (hDM : D < M) (b : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc D M, (μ n : ℝ) / n * b n) =
      b M * moebiusHarmonicPrefix M - b (D + 1) * moebiusHarmonicPrefix D -
        ∑ n ∈ Finset.Ioc D (M - 1), (b (n + 1) - b n) * moebiusHarmonicPrefix n := by
  have h := Finset.sum_Ioc_by_parts b (fun n : ℕ ↦ (μ n : ℝ) / n) hDM
  simp only [smul_eq_mul, ← harmonic_eq_range] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro n _
  ring

private theorem sum_decreasing_steps {D M : ℕ} (hDM : D < M) (b : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc D (M - 1), (b n - b (n + 1))) = b (D + 1) - b M := by
  have he : Finset.Ioc D (M - 1) = Finset.Ico (D + 1) M := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [he]
  calc
    _ = -(∑ n ∈ Finset.Ico (D + 1) M, (b (n + 1) - b n)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := by rw [Finset.sum_Ico_sub b (by omega : D + 1 ≤ M)]; ring

/-- Uniform smallness of the actual harmonic prefixes controls a whole decreasing-weight tail by its first weight, after the complete signed Abel identity is retained. -/
theorem abs_sum_moebiusHarmonic_antitone_le {D M : ℕ} (hDM : D < M) {b : ℕ → ℝ}
    (hb : ∀ n ∈ Finset.Icc (D + 1) M, 0 ≤ b n)
    (hanti : AntitoneOn b (Set.Icc (D + 1) M)) {e : ℝ}
    (hm : ∀ n ∈ Finset.Icc D M, |moebiusHarmonicPrefix n| ≤ e) :
    |∑ n ∈ Finset.Ioc D M, (μ n : ℝ) / n * b n| ≤ 2 * e * b (D + 1) := by
  have hbM := hb M (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hbD := hb (D + 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hM : |b M * moebiusHarmonicPrefix M| ≤ e * b M := by
    rw [abs_mul, abs_of_nonneg hbM]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hm M (Finset.mem_Icc.mpr ⟨hDM.le, le_rfl⟩)) hbM
  have hD : |b (D + 1) * moebiusHarmonicPrefix D| ≤ e * b (D + 1) := by
    rw [abs_mul, abs_of_nonneg hbD]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hm D (Finset.mem_Icc.mpr ⟨le_rfl, hDM.le⟩)) hbD
  have hstep (n : ℕ) (hn : n ∈ Finset.Ioc D (M - 1)) : b (n + 1) ≤ b n := by
    have hh := Finset.mem_Ioc.mp hn
    exact hanti ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
  have hsum : |∑ n ∈ Finset.Ioc D (M - 1), (b (n + 1) - b n) * moebiusHarmonicPrefix n| ≤
      e * (b (D + 1) - b M) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ n ∈ Finset.Ioc D (M - 1), e * (b n - b (n + 1)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hh := Finset.mem_Ioc.mp hn
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hstep n hn))]
        have h := mul_le_mul_of_nonneg_left (hm n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
          (sub_nonneg.mpr (hstep n hn))
        convert h using 1 <;> ring
      _ = _ := by rw [← Finset.mul_sum, sum_decreasing_steps hDM]
  rw [sum_moebiusHarmonic_weight_eq_by_parts hDM]
  apply (abs_sub _ _).trans
  have hfirst := (abs_sub (b M * moebiusHarmonicPrefix M)
    (b (D + 1) * moebiusHarmonicPrefix D)).trans (add_le_add hM hD)
  nlinarith

end

end RiemannGaussian

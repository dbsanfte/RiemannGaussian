import RiemannGaussian.MoebiusFiniteQuantitativeCancellation
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Exact finite Möbius hyperbola identities

The full Möbius convolution is split at two literal integer cutoffs.
The transpose of the remaining divisor region retains all divided
cutoffs, giving a joint identity for an entire family of finite prefixes.
No absolute values or limiting rearrangements enter these identities.
-/

open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The original finite signed prefix agrees exactly with its positive closed integer interval. -/
theorem moebiusFinitePrefix_eq_sum_Icc (M : ℕ) :
    moebiusFinitePrefix M = ∑ d ∈ Finset.Icc 1 M, ((μ d : ℤ) : ℝ) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, add_comm 1, moebiusFinitePrefix]

/-- Subtracting two ordered original prefixes retains their exact open-closed integer interval. -/
theorem moebiusFinitePrefix_sub_eq_sum_Ioc {D M : ℕ} (hDM : D ≤ M) :
    moebiusFinitePrefix M - moebiusFinitePrefix D =
      ∑ d ∈ Finset.Ioc D M, ((μ d : ℤ) : ℝ) := by
  have hsub : Finset.Icc 1 D ⊆ Finset.Icc 1 M := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hDM⟩
  have he : Finset.Icc 1 M \ Finset.Icc 1 D = Finset.Ioc D M := by
    ext d
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [moebiusFinitePrefix_eq_sum_Icc, moebiusFinitePrefix_eq_sum_Icc]
  have hs := Finset.sum_sdiff (f := fun d ↦ ((μ d : ℤ) : ℝ)) hsub
  rw [he] at hs
  exact (eq_sub_iff_add_eq.mpr hs).symm

/-- The full finite Möbius convolution has its literal integer-floor identity. -/
theorem sum_moebius_mul_nat_div_eq_one {M : ℕ} (hM : 0 < M) :
    (∑ d ∈ Finset.Icc 1 M, ((μ d : ℤ) : ℝ) * (M / d : ℕ)) = 1 := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) M
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta] at h
  have hI : Finset.Ioc 0 M = Finset.Icc 1 M := by ext n; simp; omega
  rw [hI] at h
  have hM1 : 1 ≤ M := hM
  simpa [ArithmeticFunction.one_apply, ArithmeticFunction.intCoe_apply,
    Finset.sum_ite_eq', Finset.mem_Icc, hM1] using h.symm

/-- Transposing the full remaining divisor region retains both original integer cutoffs. -/
theorem sum_moebius_hyperbola_tail_transpose {D Q : ℕ} (hD : 0 < D) :
    (∑ d ∈ Finset.Ioc D (D * Q), ∑ _q ∈ Finset.Icc 1 ((D * Q) / d), ((μ d : ℤ) : ℝ)) =
      ∑ q ∈ Finset.Icc 1 Q, ∑ d ∈ Finset.Ioc D ((D * Q) / q), ((μ d : ℤ) : ℝ) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ ↦ (⟨p.2, p.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hd, hq⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hDd, hdM⟩ := Finset.mem_Ioc.mp hd
    obtain ⟨hqpos, hqdiv⟩ := Finset.mem_Icc.mp hq
    have hdpos : 0 < p.1 := by omega
    have hprod := (Nat.le_div_iff_mul_le hdpos).mp hqdiv
    have hsmall : p.2 ≤ (D * Q) / D := (Nat.le_div_iff_mul_le hD).mpr
      ((Nat.mul_le_mul_left p.2 (show D ≤ p.1 by omega)).trans hprod)
    have hqQ : p.2 ≤ Q := by simpa only [Nat.mul_div_cancel_left Q hD] using hsmall
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hqpos, hqQ⟩,
      Finset.mem_Ioc.mpr ⟨hDd, (Nat.le_div_iff_mul_le hqpos).mpr (by simpa only [Nat.mul_comm] using hprod)⟩⟩
  · intro p hp r hr he
    exact Sigma.ext (congrArg Sigma.snd he) (heq_of_eq (congrArg Sigma.fst he))
  · intro p hp
    obtain ⟨hq, hd⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hqpos, hqQ⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hDd, hddiv⟩ := Finset.mem_Ioc.mp hd
    have hdpos : 0 < p.2 := by omega
    have hprod := (Nat.le_div_iff_mul_le hqpos).mp hddiv
    refine ⟨⟨p.2, p.1⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Finset.mem_Ioc.mpr ⟨hDd, hddiv.trans (Nat.div_le_self _ _)⟩
    · exact Finset.mem_Icc.mpr ⟨hqpos,
        (Nat.le_div_iff_mul_le hdpos).mpr (by simpa only [Nat.mul_comm] using hprod)⟩
  · intro p hp
    rfl

/-- The complete quotient-prefix family equals the low-cutoff rectangle plus the exact complementary floor-weighted tail. -/
theorem sum_moebiusFinitePrefix_div_eq_hyperbola_tail {D Q : ℕ} (hD : 0 < D) :
    (∑ q ∈ Finset.Icc 1 Q, moebiusFinitePrefix ((D * Q) / q)) =
      (Q : ℝ) * moebiusFinitePrefix D +
        ∑ d ∈ Finset.Ioc D (D * Q), ((μ d : ℤ) : ℝ) * ((D * Q) / d : ℕ) := by
  have hp (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) : D ≤ (D * Q) / q :=
    (Nat.le_div_iff_mul_le (Finset.mem_Icc.mp hq).1).mpr
      (Nat.mul_le_mul_left D (Finset.mem_Icc.mp hq).2)
  calc
    _ = ∑ q ∈ Finset.Icc 1 Q, (moebiusFinitePrefix D +
        ∑ d ∈ Finset.Ioc D ((D * Q) / q), ((μ d : ℤ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro q hq
      have he := moebiusFinitePrefix_sub_eq_sum_Ioc (hp q hq)
      linarith
    _ = (Q : ℝ) * moebiusFinitePrefix D +
        ∑ q ∈ Finset.Icc 1 Q, ∑ d ∈ Finset.Ioc D ((D * Q) / q), ((μ d : ℤ) : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = _ := by
      rw [← sum_moebius_hyperbola_tail_transpose hD]
      simp [mul_comm]

/-- The full finite hyperbola identity controls all quotient prefixes jointly and retains the low-cutoff floor error exactly. -/
theorem moebiusFinitePrefix_hyperbola_identity {D Q : ℕ} (hD : 0 < D) (hQ : 0 < Q) :
    (∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) * ((D * Q) / d : ℕ)) +
      (∑ q ∈ Finset.Icc 1 Q, moebiusFinitePrefix ((D * Q) / q)) =
        1 + (Q : ℝ) * moebiusFinitePrefix D := by
  have hDM : D ≤ D * Q := by nlinarith
  have hsub : Finset.Icc 1 D ⊆ Finset.Icc 1 (D * Q) := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hDM⟩
  have he : Finset.Icc 1 (D * Q) \ Finset.Icc 1 D = Finset.Ioc D (D * Q) := by
    ext d
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hs := Finset.sum_sdiff (f := fun d ↦ ((μ d : ℤ) : ℝ) * ((D * Q) / d : ℕ)) hsub
  rw [he, sum_moebius_mul_nat_div_eq_one (Nat.mul_pos hD hQ)] at hs
  rw [sum_moebiusFinitePrefix_div_eq_hyperbola_tail hD]
  linarith

end

end RiemannGaussian

import RiemannGaussian.EtaMoebiusLogArithmetic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Prime arithmetic in the exact logarithmic residual

The signed logarithmic divisor correction is evaluated using the classical
Möbius-von Mangoldt convolution while retaining the even complementary
divisors. Its harmonic prefix is a dyadic prime-power shell. This identifies
the cancellation required inside the arithmetic cutoff; it does not assume
that cancellation controls the full residual square sum.
-/

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

namespace RiemannGaussian

noncomputable section

private theorem sum_even_complementary_divisor (l : ℕ) (f : ℕ → ℝ) :
    (∑ p ∈ l.divisorsAntidiagonal, if Even p.2 then f p.1 else 0) =
      if Even l then ∑ d ∈ (l / 2).divisors, f d else 0 := by
  by_cases hl : Even l
  · rw [if_pos hl]
    obtain ⟨r, rfl⟩ := even_iff_two_dvd.mp hl
    by_cases hr : r = 0
    · subst r
      simp
    · rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2), ← Finset.sum_filter,
        ← Nat.sum_divisorsAntidiagonal (fun d _ ↦ f d)]
      symm
      apply Finset.sum_bij (fun p _ ↦ (p.1, 2 * p.2))
      · intro p hp
        apply Finset.mem_filter.mpr
        refine ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨?_, by omega⟩, ?_⟩
        · have hh := (Nat.mem_divisorsAntidiagonal.mp hp).1
          nlinarith
        · exact even_iff_two_dvd.mpr ⟨p.2, rfl⟩
      · intro p _ q _ hpq
        apply Prod.ext
        · have h := congrArg (fun z : ℕ × ℕ ↦ z.1) hpq
          exact h
        · have h := congrArg Prod.snd hpq
          dsimp only at h
          omega
      · intro p hp
        obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
        obtain ⟨e, he⟩ := even_iff_two_dvd.mp he
        have hh := (Nat.mem_divisorsAntidiagonal.mp hp).1
        refine ⟨(p.1, e), Nat.mem_divisorsAntidiagonal.mpr ⟨?_, hr⟩, ?_⟩
        · dsimp only
          rw [he] at hh
          nlinarith
        · exact Prod.ext rfl he.symm
      · intro p _
        rfl
  · rw [if_neg hl]
    apply Finset.sum_eq_zero
    intro p hp
    have he : ¬ Even p.2 := by
      intro he
      obtain ⟨e, he⟩ := even_iff_two_dvd.mp he
      have hh := (Nat.mem_divisorsAntidiagonal.mp hp).1
      apply hl
      apply even_iff_two_dvd.mpr
      refine ⟨p.1 * e, ?_⟩
      rw [he] at hh
      nlinarith
    simp [he]

/-- The complete logarithmic Möbius-eta divisor coefficient is exactly the signed prime-power coefficient and its even rescaling. -/
theorem pairedEtaMoebiusLogDivisor_eq_vonMangoldt (l : ℕ) :
    pairedEtaMoebiusLogDivisor l = -Λ l + 2 * (if Even l then Λ (l / 2) else 0) := by
  calc
    _ = (∑ p ∈ l.divisorsAntidiagonal, (μ p.1 : ℝ) * Real.log p.1) -
        2 * ∑ p ∈ l.divisorsAntidiagonal,
          if Even p.2 then (μ p.1 : ℝ) * Real.log p.1 else 0 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : Even p.2 <;> simp [pairedEtaDirichletSign, hp]
      ring
    _ = (∑ d ∈ l.divisors, (μ d : ℝ) * Real.log d) -
        2 * (if Even l then ∑ d ∈ (l / 2).divisors, (μ d : ℝ) * Real.log d else 0) := by
      rw [Nat.sum_divisorsAntidiagonal (fun d _ ↦ (μ d : ℝ) * Real.log d),
        sum_even_complementary_divisor l (fun d ↦ (μ d : ℝ) * Real.log d)]
    _ = _ := by
      have hlog (n : ℕ) : (∑ d ∈ n.divisors, (μ d : ℝ) * Real.log d) = -Λ n := by
        simpa only [ArithmeticFunction.log_apply] using
          (ArithmeticFunction.sum_moebius_mul_log_eq (n := n))
      rw [hlog l, hlog (l / 2)]
      split_ifs <;> ring

private theorem sum_Icc_even (L : ℕ) (f : ℕ → ℝ) :
    (∑ l ∈ Finset.Icc 1 L, if Even l then f l else 0) =
      ∑ n ∈ Finset.Icc 1 (L / 2), f (2 * n) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun n _ ↦ 2 * n)
  · intro n hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hn).1; omega, ?_⟩,
      even_iff_two_dvd.mpr ⟨n, rfl⟩⟩
    have h := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp (Finset.mem_Icc.mp hn).2
    omega
  · intro n _ m _ h
    omega
  · intro l hl
    obtain ⟨hl, he⟩ := Finset.mem_filter.mp hl
    obtain ⟨n, rfl⟩ := even_iff_two_dvd.mp he
    refine ⟨n, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · have := (Finset.mem_Icc.mp hl).1
      omega
    · apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
      have := (Finset.mem_Icc.mp hl).2
      omega
  · intro n _
    rfl

/-- The exact dyadic harmonic prime-power shell in the logarithmic arithmetic residual. -/
def pairedEtaPrimeHarmonicShell (L : ℕ) : ℝ :=
  (∑ l ∈ Finset.Icc 1 L, Λ l / l) - ∑ l ∈ Finset.Icc 1 (L / 2), Λ l / l

/-- The full signed logarithmic cell correction is exactly the negative prime-power shell, with every even endpoint contribution included. -/
theorem pairedEtaMoebiusLogCellCorrection_eq_primeShell (L : ℕ) :
    pairedEtaMoebiusLogCellCorrection L = -pairedEtaPrimeHarmonicShell L := by
  unfold pairedEtaMoebiusLogCellCorrection
  simp_rw [pairedEtaMoebiusLogDivisor_eq_vonMangoldt, add_div, neg_div]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have he : (∑ l ∈ Finset.Icc 1 L, (2 * (if Even l then Λ (l / 2) else 0)) / (l : ℝ)) =
      ∑ l ∈ Finset.Icc 1 (L / 2), Λ l / l := by
    simp only [mul_ite, mul_zero, ite_div, zero_div]
    rw [sum_Icc_even]
    apply Finset.sum_congr rfl
    intro n _
    rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2), Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [he]
  unfold pairedEtaPrimeHarmonicShell
  ring

/-- On every cell up to the arithmetic cutoff, the actual logarithmic residual is the signed difference between the harmonic correction and the normalized prime-power shell. -/
theorem pairedEtaMoebiusArithmeticCellResidual_log_eq_primeShell {M L : ℕ} (hM : 1 < M)
    (hL : 1 ≤ L) (hLM : L ≤ M) :
    pairedEtaMoebiusArithmeticCellResidual M (pairedEtaMoebiusTrialLogWeight M) L =
      pairedEtaMoebiusLogHarmonic M * pairedEtaArithmeticHarmonicPrefix L -
        pairedEtaPrimeHarmonicShell L / Real.log M := by
  rw [pairedEtaMoebiusArithmeticCellResidual_log_eq hM hL hLM,
    pairedEtaMoebiusLogCellCorrection_eq_primeShell]
  ring

end

end RiemannGaussian

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ChebyshevMoebiusCancellation
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Retaining the scale of the signed Möbius quotient blocks

The complementary factorial convolution is first transposed exactly into
signed differences of the original Möbius prefixes. Each difference retains
its own divided cutoff and the common lower boundary. Only the downstream
estimate takes absolute values.

Keeping the pointwise prefix bound at that divided cutoff replaces the
factorial-sized allowance by a quadratic logarithmic allowance. This is a
quantitative improvement of the actual factorial correction, not a proof of
the independent signed Suzuki-work bound required by the RH chain.
-/

open Filter
open scoped Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Transposition of the complete complementary hyperbola retains its exact
lower boundary, every integer quotient, and arbitrary signed weights. -/
theorem sum_high_divided_prefix_transpose (N D : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Ioc D N, ∑ k ∈ Finset.Icc 1 (N / d), f d k) =
      ∑ k ∈ Finset.Icc 1 (N / (D + 1)), ∑ d ∈ Finset.Ioc D (N / k), f d k := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ ↦ (⟨p.2, p.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hd, hk⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hDd, _⟩ := Finset.mem_Ioc.mp hd
    obtain ⟨hkpos, hkdiv⟩ := Finset.mem_Icc.mp hk
    have hdpos : 0 < p.1 := by omega
    have hprod := (Nat.le_div_iff_mul_le hdpos).mp hkdiv
    have hkQ : p.2 ≤ N / (D + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr
      ((Nat.mul_le_mul_left p.2 (show D + 1 ≤ p.1 by omega)).trans hprod)
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hkpos, hkQ⟩,
      Finset.mem_Ioc.mpr ⟨hDd, (Nat.le_div_iff_mul_le hkpos).mpr
        (by simpa only [Nat.mul_comm] using hprod)⟩⟩
  · intro p _ r _ he
    exact Sigma.ext (congrArg Sigma.snd he) (heq_of_eq (congrArg Sigma.fst he))
  · intro p hp
    obtain ⟨hk, hd⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hkpos, _⟩ := Finset.mem_Icc.mp hk
    obtain ⟨hDd, hddiv⟩ := Finset.mem_Ioc.mp hd
    have hdpos : 0 < p.2 := by omega
    have hprod := (Nat.le_div_iff_mul_le hkpos).mp hddiv
    refine ⟨⟨p.2, p.1⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Finset.mem_Ioc.mpr ⟨hDd, hddiv.trans (Nat.div_le_self _ _)⟩
    · exact Finset.mem_Icc.mpr ⟨hkpos, (Nat.le_div_iff_mul_le hdpos).mpr
        (by simpa only [Nat.mul_comm] using hprod)⟩
  · intro p _
    rfl

/-- The factorial tail is exactly a logarithmically weighted family of signed
prefix differences; the shared boundary is retained inside every block. -/
theorem sum_moebius_logFactorial_high_eq_signed_quotient_blocks (N D : ℕ) :
    (∑ d ∈ Finset.Ioc D N, (μ d : ℝ) * chebyshevLogFactorial (N / d)) =
      ∑ k ∈ Finset.Icc 1 (N / (D + 1)), Real.log k *
        (moebiusFinitePrefix (N / k) - moebiusFinitePrefix D) := by
  simp only [chebyshevLogFactorial, Finset.mul_sum]
  rw [sum_high_divided_prefix_transpose]
  apply Finset.sum_congr rfl
  intro k hk
  have hkp := (Finset.mem_Icc.mp hk).1
  have hprod := (Nat.le_div_iff_mul_le (by omega : 0 < D + 1)).mp
    (Finset.mem_Icc.mp hk).2
  have hDk : D ≤ N / k := (Nat.le_div_iff_mul_le hkp).mpr (by nlinarith)
  rw [moebiusFinitePrefix_sub_eq_sum_Ioc hDk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

private theorem logFactorial_le_mul_log {q Q : ℕ} (hqQ : q ≤ Q) :
    chebyshevLogFactorial q ≤ (q : ℝ) * Real.log Q := by
  calc
    _ ≤ ∑ _k ∈ Finset.Icc 1 q, Real.log Q := by
      apply Finset.sum_le_sum
      intro k hk
      exact Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp hk).1)
        (by exact_mod_cast (Finset.mem_Icc.mp hk).2.trans hqQ)
    _ = _ := by simp

private theorem sum_log_div_le {q Q : ℕ} (hqQ : q ≤ Q) (hQ : 0 < Q) :
    (∑ k ∈ Finset.Icc 1 q, Real.log k / k) ≤ Real.log Q * (1 + Real.log Q) := by
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ)
  have hh : (∑ k ∈ Finset.Icc 1 Q, (1 : ℝ) / k) ≤ 1 + Real.log Q := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, one_div] using harmonic_le_one_add_log Q
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 q, Real.log Q * (1 / k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hl : Real.log k ≤ Real.log Q := Real.log_le_log hkR
        (by exact_mod_cast (Finset.mem_Icc.mp hk).2.trans hqQ)
      simpa only [mul_one_div] using div_le_div_of_nonneg_right hl hkR.le
    _ ≤ ∑ k ∈ Finset.Icc 1 Q, Real.log Q * (1 / k) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hqQ)
        (fun _ _ _ ↦ by positivity)
    _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hh hlog

/-- Keeping each signed quotient prefix at its own scale gives a quadratic
logarithmic budget instead of the earlier factorial-sized budget. -/
theorem abs_sum_moebius_logFactorial_high_div_le {N D Q : ℕ}
    (hDN : D < N) (hQ : 0 < Q) (hquot : N / (D + 1) ≤ Q)
    {e : ℝ} (he : 0 ≤ e)
    (hm : ∀ n ∈ Finset.Icc D N, |moebiusFinitePrefix n| ≤ e * n) :
    |(∑ d ∈ Finset.Ioc D N, (μ d : ℝ) * chebyshevLogFactorial (N / d)) / N| ≤
      e * Real.log Q * (2 + Real.log Q) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ)
  let q := N / (D + 1)
  have hboundary : (D : ℝ) / N * chebyshevLogFactorial q ≤ Real.log Q := by
    have hprod : (D : ℝ) * q ≤ N := by
      have h := (Nat.mul_le_mul_left q (show D ≤ D + 1 by omega)).trans
        (Nat.div_mul_le_self N (D + 1))
      exact_mod_cast (by simpa only [mul_comm] using h : D * q ≤ N)
    calc
      _ ≤ (D : ℝ) / N * ((q : ℝ) * Real.log Q) :=
        mul_le_mul_of_nonneg_left (logFactorial_le_mul_log hquot) (by positivity)
      _ = ((D : ℝ) * q / N) * Real.log Q := by ring
      _ ≤ 1 * Real.log Q := mul_le_mul_of_nonneg_right
        ((div_le_one hNR).mpr hprod) hlog
      _ = _ := one_mul _
  rw [sum_moebius_logFactorial_high_eq_signed_quotient_blocks, Finset.sum_div]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 q, e * (Real.log k / k + (D : ℝ) / N * Real.log k) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hkp, hkq⟩ := Finset.mem_Icc.mp hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hkp
      have hl : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hkp)
      have hprod := (Nat.le_div_iff_mul_le (by omega : 0 < D + 1)).mp hkq
      have hDk : D ≤ N / k := (Nat.le_div_iff_mul_le hkp).mpr (by nlinarith)
      have hnN := Nat.div_le_self N k
      have hprefix := (abs_sub _ _).trans (add_le_add
        (hm (N / k) (Finset.mem_Icc.mpr ⟨hDk, hnN⟩))
        (hm D (Finset.mem_Icc.mpr ⟨le_rfl, hDN.le⟩)))
      have hfloor : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := by
        apply (le_div_iff₀ hkR).mpr
        exact_mod_cast Nat.div_mul_le_self N k
      have hscaled : e * (N / k : ℕ) ≤ e * N / k := by
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hfloor he
      rw [abs_div, abs_mul, abs_of_nonneg hl, abs_of_pos hNR]
      calc
        _ ≤ Real.log k * (e * (N : ℝ) / k + e * D) / N :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (hprefix.trans (add_le_add hscaled le_rfl)) hl) hNR.le
        _ = _ := by field_simp
    _ = e * ((∑ k ∈ Finset.Icc 1 q, Real.log k / k) +
        (D : ℝ) / N * chebyshevLogFactorial q) := by
      simp only [chebyshevLogFactorial, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    _ ≤ e * (Real.log Q * (1 + Real.log Q) + Real.log Q) :=
      mul_le_mul_of_nonneg_left (add_le_add (sum_log_div_le hquot hQ) hboundary) he
    _ = _ := by ring

/-- The whole complementary remainder retains the signed quotient blocks and
both harmonic terms in one exact identity, before taking any absolute value. -/
theorem sum_moebiusFactorialRemainder_high_eq_signed_quotient_blocks {N D : ℕ}
    (hN : 0 < N) :
    (∑ d ∈ Finset.Ioc D N, (μ d : ℝ) / d * moebiusFactorialRemainder N d) =
      (∑ k ∈ Finset.Icc 1 (N / (D + 1)), Real.log k *
        (moebiusFinitePrefix (N / k) - moebiusFinitePrefix D)) / N -
      (∑ d ∈ Finset.Ioc D N, (μ d : ℝ) / d * Real.log ((N : ℝ) / d)) +
      ∑ d ∈ Finset.Ioc D N, (μ d : ℝ) / d := by
  rw [← sum_moebius_logFactorial_high_eq_signed_quotient_blocks, Finset.sum_div,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < d := by
    exact_mod_cast (by have := (Finset.mem_Ioc.mp hd).1; omega : 0 < d)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold moebiusFactorialRemainder
  field_simp

/-- The full complementary remainder has only quadratic logarithmic growth
in the quotient cutoff. Ordinary and harmonic prefix allowances stay separate. -/
theorem abs_sum_moebiusFactorialRemainder_high_le_quotient_coupled {N D Q : ℕ}
    (hDN : D < N) (hQ : 0 < Q) (hquot : (N : ℝ) / (D + 1 : ℝ) ≤ Q)
    {eF eH : ℝ} (heF : 0 ≤ eF) (heH : 0 ≤ eH)
    (hm : ∀ n ∈ Finset.Icc D N, |moebiusFinitePrefix n| ≤ eF * n)
    (hh : ∀ n ∈ Finset.Icc D N, |moebiusHarmonicPrefix n| ≤ eH) :
    |∑ d ∈ Finset.Ioc D N, (μ d : ℝ) / d * moebiusFactorialRemainder N d| ≤
      eF * Real.log Q * (2 + Real.log Q) + 2 * eH * (1 + Real.log Q) := by
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hqQ : N / (D + 1) ≤ Q := by
    have hlo : ((N / (D + 1) : ℕ) : ℝ) ≤ (N : ℝ) / (D + 1 : ℝ) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < D + 1)).mpr
      exact_mod_cast Nat.div_mul_le_self N (D + 1)
    exact_mod_cast hlo.trans hquot
  have hF := abs_sum_moebius_logFactorial_high_div_le hDN hQ hqQ heF hm
  have hlpos (n : ℕ) (hn : n ∈ Finset.Icc (D + 1) N) :
      0 ≤ Real.log ((N : ℝ) / n) := by
    have hnR : (0 : ℝ) < n := by
      exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : 0 < n)
    exact Real.log_nonneg ((one_le_div hnR).mpr (by exact_mod_cast (Finset.mem_Icc.mp hn).2))
  have hlanti : AntitoneOn (fun n : ℕ ↦ Real.log ((N : ℝ) / n))
      (Set.Icc (D + 1) N) := by
    intro a ha b hb hab
    have haR : (0 : ℝ) < a := by exact_mod_cast (by have := ha.1; omega : 0 < a)
    have hbR : (0 : ℝ) < b := by exact_mod_cast (by have := hb.1; omega : 0 < b)
    exact Real.log_le_log (div_pos hNR hbR)
      (div_le_div_of_nonneg_left hNR.le haR (by exact_mod_cast hab))
  have hl := abs_sum_moebiusHarmonic_antitone_le hDN hlpos hlanti hh
  have hlu : |∑ n ∈ Finset.Ioc D N, (μ n : ℝ) / n * Real.log ((N : ℝ) / n)| ≤
      2 * eH * Real.log Q := hl.trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (div_pos hNR (by positivity)) (by simpa using hquot)) (by positivity))
  have hc := abs_sum_moebiusHarmonic_antitone_le hDN (b := fun _ ↦ (1 : ℝ))
    (fun _ _ ↦ by norm_num) (fun _ _ _ _ _ ↦ le_rfl) hh
  simp only [mul_one] at hc
  rw [sum_moebiusFactorialRemainder_high_eq_signed_quotient_blocks hN,
    ← sum_moebius_logFactorial_high_eq_signed_quotient_blocks]
  apply (abs_add_le _ _).trans
  have hf := (abs_sub _ _).trans (add_le_add hF hlu)
  nlinarith

/-- The complete correction, including the low-divisor part and every boundary,
inherits the sharper quotient allowance at its original split. -/
theorem abs_moebiusFactorialCorrection_le_quotient_coupled {N Q : ℕ}
    (hN : 0 < N) (hQ : 1 < Q) {eF eH : ℝ} (heF : 0 ≤ eF) (heH : 0 ≤ eH)
    (hm : ∀ n ∈ Finset.Icc (N / Q) N, |moebiusFinitePrefix n| ≤ eF * n)
    (hh : ∀ n ∈ Finset.Icc (N / Q) N, |moebiusHarmonicPrefix n| ≤ eH) :
    |moebiusFactorialCorrection N| ≤ 4 / Real.sqrt Q +
      eF * Real.log Q * (2 + Real.log Q) + 2 * eH * (1 + Real.log Q) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hDN : N / Q < N := Nat.div_lt_self hN hQ
  have hquot : (N : ℝ) / ((N / Q : ℕ) + 1 : ℝ) ≤ Q := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N / Q : ℕ) + 1)).mpr
    exact_mod_cast (Nat.lt_mul_div_succ N (by omega : 0 < Q)).le
  have hlow : 4 * Real.sqrt (N / Q : ℕ) / Real.sqrt N ≤ 4 / Real.sqrt Q := by
    have hratio : ((N / Q : ℕ) : ℝ) / N ≤ 1 / (Q : ℝ) := by
      apply (div_le_div_iff₀ hNR hQR).mpr
      simpa using (show ((N / Q : ℕ) : ℝ) * Q ≤ N by exact_mod_cast Nat.div_mul_le_self N Q)
    calc
      _ = 4 * Real.sqrt (((N / Q : ℕ) : ℝ) / N) := by
        rw [Real.sqrt_div (by positivity)]
        ring
      _ ≤ 4 * Real.sqrt (1 / (Q : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hratio) (by norm_num)
      _ = _ := by rw [Real.sqrt_div (by norm_num), Real.sqrt_one]; ring
  have hsplit : moebiusFactorialCorrection N =
      (∑ d ∈ Finset.Icc 1 (N / Q), (μ d : ℝ) / d * moebiusFactorialRemainder N d) +
        ∑ d ∈ Finset.Ioc (N / Q) N, (μ d : ℝ) / d * moebiusFactorialRemainder N d := by
    have hs : Finset.Icc 1 (N / Q) ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc le_rfl hDN.le
    have hd : Finset.Icc 1 N \ Finset.Icc 1 (N / Q) = Finset.Ioc (N / Q) N := by
      ext n
      simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
      have := Nat.zero_le (N / Q)
      omega
    have h := Finset.sum_sdiff
      (f := fun d ↦ (μ d : ℝ) / d * moebiusFactorialRemainder N d) hs
    rw [hd] at h
    exact ((add_comm _ _).trans h).symm
  rw [hsplit]
  have hb := (abs_add_le _ _).trans (add_le_add
    ((abs_sum_moebiusFactorialRemainder_low_le hN hDN.le).trans hlow)
    (abs_sum_moebiusFactorialRemainder_high_le_quotient_coupled hDN (by omega)
      hquot heF heH hm hh))
  linarith

/-- The repository's proved Gaussian Möbius estimates discharge both prefix
allowances simultaneously, giving a quantitative bound on the actual complete
factorial correction for every admissible quotient cutoff. -/
theorem exists_moebiusFactorialCorrection_cubic_quotient_bound :
    ∃ H : ℝ, 22 ≤ H ∧ ∀ h : ℝ, H ≤ h → ∀ N Q : ℕ, 1 < Q →
      Real.exp (2 * moebiusFiniteContourCenter h) ≤ ((N / Q : ℕ) : ℝ) →
      |moebiusFactorialCorrection N| ≤ 4 / Real.sqrt Q +
        (moebiusFiniteCancellationConstant + 1) * Real.exp (-h / 2) *
          Real.log Q * (2 + Real.log Q) +
        2 * moebiusHarmonicCancellationConstant * Real.exp (-h / 8) * (1 + Real.log Q) := by
  obtain ⟨HF, hHF, hfinite⟩ := exists_moebiusFinitePrefix_cubic_tail_bound
  obtain ⟨HH, hHH, hharmonic⟩ := exists_moebiusHarmonicPrefix_cubic_rate
  refine ⟨max HF HH, hHF.trans (le_max_left _ _), fun h hh N Q hQ hsize ↦ ?_⟩
  have hhF : HF ≤ h := (le_max_left _ _).trans hh
  have hhH : HH ≤ h := (le_max_right _ _).trans hh
  have hDpos : (0 : ℝ) < (N / Q : ℕ) := (Real.exp_pos _).trans_le hsize
  have hN : 0 < N := (by exact_mod_cast hDpos : 0 < N / Q).trans_le (Nat.div_le_self N Q)
  have heF : 0 ≤ (moebiusFiniteCancellationConstant + 1) * Real.exp (-h / 2) := by
    have := moebiusFiniteCancellationConstant_pos
    positivity
  have heH : 0 ≤ moebiusHarmonicCancellationConstant * Real.exp (-h / 8) :=
    mul_nonneg moebiusHarmonicCancellationConstant_pos.le (Real.exp_pos _).le
  have hb := abs_moebiusFactorialCorrection_le_quotient_coupled hN hQ heF heH
    (fun n hn ↦ hfinite h hhF (N / Q) hsize n (Finset.mem_Icc.mp hn).1)
    (fun n hn ↦ hharmonic h hhH n (hsize.trans (by exact_mod_cast (Finset.mem_Icc.mp hn).1)))
  convert hb using 1
  ring

end

end RiemannGaussian

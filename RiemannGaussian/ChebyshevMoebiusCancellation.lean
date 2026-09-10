/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaMoebiusNormalizationMainTerm
import RiemannGaussian.MoebiusFiniteCancellation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Transferring the proved Möbius cancellation to the Chebyshev function

The finite logarithmic factorial convolution retains every divided cutoff.
Its remainder is split into a small-divisor part and a complete complementary
tail. The former has an explicit square-root budget; the latter uses the
already proved ordinary and harmonic Möbius cancellation.

This transfer concerns the actual arithmetic Chebyshev function. Qualitative
prime-number-theorem cancellation does not supply the stronger signed-work
bound required by the Suzuki-to-RH chain.
-/

open Filter MeasureTheory
open scoped Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The logarithm of the finite factorial, written as its complete sum. -/
def chebyshevLogFactorial (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, Real.log n

private theorem logFactorial_nonneg (N : ℕ) : 0 ≤ chebyshevLogFactorial N := by
  apply Finset.sum_nonneg
  intro n hn
  exact Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hn).1)

private theorem logFactorial_mono : Monotone chebyshevLogFactorial := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hab)
    (fun n hn _ ↦ Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hn).1))

/-- Integral comparison bounds the full logarithmic factorial with its last atom retained. -/
theorem chebyshevLogFactorial_bounds {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * Real.log N - N + 1 ≤ chebyshevLogFactorial N ∧
      chebyshevLogFactorial N ≤ (N : ℝ) * Real.log N - N + 1 + Real.log N := by
  have hmono : MonotoneOn Real.log (Set.Icc (1 : ℝ) N) := by
    intro a ha b _ hab
    exact Real.log_le_log (by linarith [ha.1]) hab
  have hlo := MonotoneOn.integral_le_sum_Ico (a := 1) (b := N) hN (by simpa using hmono)
  have hhi := MonotoneOn.sum_le_integral_Ico (a := 1) (b := N) hN (by simpa using hmono)
  rw [integral_log] at hlo hhi
  norm_num only [Real.log_one, one_mul] at hlo hhi
  have hshift : (∑ n ∈ Finset.Ico 1 N, Real.log (n + 1 : ℕ)) =
      chebyshevLogFactorial N := by
    rw [Finset.sum_Ico_add' (fun n : ℕ ↦ Real.log (n : ℝ)) 1 N 1]
    unfold chebyshevLogFactorial
    rw [← Finset.Ico_succ_right_eq_Icc 1 N]
    change (∑ n ∈ Finset.Ico 2 (N + 1), Real.log (n : ℝ)) =
      ∑ n ∈ Finset.Ico 1 (N + 1), Real.log (n : ℝ)
    simpa using Finset.sum_Ico_consecutive (fun n : ℕ ↦ Real.log (n : ℝ))
      (by omega : 1 ≤ 2) (by omega : 2 ≤ N + 1)
  have hlast : (∑ n ∈ Finset.Ico 1 N, Real.log (n : ℝ)) + Real.log N =
      chebyshevLogFactorial N := by
    rw [Finset.sum_Ico_add_eq_sum_Ico_add_one hN]
    exact congrArg (fun s : Finset ℕ ↦ ∑ n ∈ s, Real.log (n : ℝ))
      (Finset.Ico_succ_right_eq_Icc 1 N)
  rw [hshift] at hlo
  constructor <;> linarith

/-- The exact normalized logarithmic factorial remainder at the original divided cutoff. -/
def moebiusFactorialRemainder (N d : ℕ) : ℝ :=
  chebyshevLogFactorial (N / d) / ((N : ℝ) / d) - Real.log ((N : ℝ) / d) + 1

private theorem logFactorial_real_remainder {q : ℕ} {y : ℝ}
    (hq : 0 < q) (hqy : (q : ℝ) ≤ y) (hyq : y < q + 1) :
    |chebyshevLogFactorial q - y * Real.log y + y| ≤ 1 + Real.log y := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hyp : 0 < y := hqp.trans_le hqy
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (hq1.trans hqy)
  have hlog := Real.log_le_log hqp hqy
  have hlow := Real.one_sub_inv_le_log_of_pos (div_pos hyp hqp)
  have hhigh := Real.log_le_sub_one_of_pos (div_pos hyp hqp)
  rw [Real.log_div hyp.ne' hqp.ne'] at hlow hhigh
  have hl : y - q ≤ y * (Real.log y - Real.log q) := by
    have h := mul_le_mul_of_nonneg_left hlow hyp.le
    field_simp at h
    nlinarith
  have hu : (q : ℝ) * (Real.log y - Real.log q) ≤ y - q := by
    have h := mul_le_mul_of_nonneg_left hhigh hqp.le
    field_simp at h
    nlinarith
  have helo : (q : ℝ) * Real.log q - q ≤ y * Real.log y - y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqy) hlogq]
  have hehi : y * Real.log y - y - ((q : ℝ) * Real.log q - q) ≤ Real.log y := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (q : ℝ) + 1 - y) hlogy]
  obtain ⟨hlo, hhi⟩ := chebyshevLogFactorial_bounds hq
  rw [abs_le]
  constructor <;> linarith

/-- The full quotient remainder, including its floor endpoint, is bounded by twice its reciprocal square-root scale. -/
theorem abs_moebiusFactorialRemainder_le {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    |moebiusFactorialRemainder N d| ≤ 2 / Real.sqrt ((N : ℝ) / d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (0 : ℝ) < N := by exact_mod_cast hd.trans_le hdN
  have hy : 0 < (N : ℝ) / d := div_pos hNR hdR
  have hq : 0 < N / d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdN)
  have hlo : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by
    apply (le_div_iff₀ hdR).mpr
    exact_mod_cast Nat.div_mul_le_self N d
  have hhi : (N : ℝ) / d < (N / d : ℕ) + 1 := by
    apply (div_lt_iff₀ hdR).mpr
    exact_mod_cast (show N < (N / d + 1) * d by simpa only [mul_comm] using Nat.lt_mul_div_succ N hd)
  have hb := logFactorial_real_remainder hq hlo hhi
  have hs := Real.sqrt_pos.mpr hy
  have hlog := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hy.le] at hlog
  have he : moebiusFactorialRemainder N d =
      (chebyshevLogFactorial (N / d) - ((N : ℝ) / d) * Real.log ((N : ℝ) / d) +
        (N : ℝ) / d) / ((N : ℝ) / d) := by
    unfold moebiusFactorialRemainder
    field_simp
  rw [he, abs_div, abs_of_pos hy]
  apply (div_le_iff₀ hy).mpr
  calc
    _ ≤ 1 + Real.log ((N : ℝ) / d) := hb
    _ ≤ 2 * Real.sqrt ((N : ℝ) / d) := by linarith
    _ = 2 / Real.sqrt ((N : ℝ) / d) * ((N : ℝ) / d) := by
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hs.ne').mpr
      nlinarith [Real.sq_sqrt hy.le]

/-- Telescoping consecutive square roots bounds the full reciprocal
square-root prefix, including the empty prefix at cutoff zero. -/
theorem sum_inv_sqrt_Icc_le (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, 1 / Real.sqrt d) ≤ 2 * Real.sqrt D := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hp : 0 < Real.sqrt (D + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hd : Real.sqrt (D : ℝ) ≤ Real.sqrt (D + 1 : ℕ) := Real.sqrt_le_sqrt (by norm_cast; omega)
    have hstep : 1 / Real.sqrt (D + 1 : ℕ) ≤
        2 * (Real.sqrt (D + 1 : ℕ) - Real.sqrt D) := by
      apply (div_le_iff₀ hp).mpr
      have h0 := Real.sq_sqrt (show (0 : ℝ) ≤ D by positivity)
      have h1 : Real.sqrt (D + 1 : ℕ) ^ 2 = (D : ℝ) + 1 := by
        rw [Real.sq_sqrt (by positivity)]
        push_cast
        rfl
      nlinarith [sq_nonneg (Real.sqrt (D + 1 : ℕ) - Real.sqrt D)]
    linarith

/-- The complete low-divisor remainder has a vanishing budget as the quotient split grows. -/
theorem abs_sum_moebiusFactorialRemainder_low_le {N D : ℕ}
    (hN : 0 < N) (hDN : D ≤ N) :
    |∑ d ∈ Finset.Icc 1 D, (μ d : ℝ) / d * moebiusFactorialRemainder N d| ≤
      4 * Real.sqrt D / Real.sqrt N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN := Real.sqrt_pos.mpr hNR
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, (2 / Real.sqrt N) * (1 / Real.sqrt d) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos := (Finset.mem_Icc.mp hd).1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
      have hsd := Real.sqrt_pos.mpr hdR
      rw [abs_mul, abs_div, abs_of_pos hdR]
      calc
        _ ≤ (1 / (d : ℝ)) * (2 / Real.sqrt ((N : ℝ) / d)) :=
          mul_le_mul (div_le_div_of_nonneg_right (abs_real_moebius_le_one d) hdR.le)
            (abs_moebiusFactorialRemainder_le hdpos ((Finset.mem_Icc.mp hd).2.trans hDN))
            (abs_nonneg _) (by positivity)
        _ = _ := by
          rw [Real.sqrt_div hNR.le]
          field_simp
          nlinarith [Real.sq_sqrt hdR.le]
    _ = 2 / Real.sqrt N * ∑ d ∈ Finset.Icc 1 D, 1 / Real.sqrt d := by
      rw [Finset.mul_sum]
    _ ≤ 2 / Real.sqrt N * (2 * Real.sqrt D) :=
      mul_le_mul_of_nonneg_left (sum_inv_sqrt_Icc_le D) (by positivity)
    _ = _ := by ring

/-- Möbius inversion identifies the literal Chebyshev sum with full factorial prefixes at the exact divided cutoffs. -/
theorem chebyshevPsi_eq_moebius_logFactorial (N : ℕ) :
    Chebyshev.psi N = ∑ d ∈ Finset.Icc 1 N, (μ d : ℝ) * chebyshevLogFactorial (N / d) := by
  have hconv (n : ℕ) :
      (∑ p ∈ n.divisorsAntidiagonal, (μ p.1 : ℝ) * Real.log p.2) =
        ArithmeticFunction.vonMangoldt n := by
    simpa only [ArithmeticFunction.mul_apply, ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.log_apply] using congrArg
        (fun f : ArithmeticFunction ℝ ↦ f n) ArithmeticFunction.moebius_mul_log_eq_vonMangoldt
  have hsum := sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix N
    (fun d m ↦ ((μ d : ℝ) * Real.log m : ℂ))
  have hreal : (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n) =
      ∑ d ∈ Finset.Icc 1 N, (μ d : ℝ) * chebyshevLogFactorial (N / d) := by
    simp only [chebyshevLogFactorial, Finset.mul_sum]
    simp_rw [← hconv]
    exact_mod_cast hsum
  convert hreal using 1
  unfold Chebyshev.psi
  rw [Nat.floor_natCast]
  congr 1

/-- The full factorial remainder in the finite Möbius convolution. -/
def moebiusFactorialCorrection (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (μ d : ℝ) / d * moebiusFactorialRemainder N d

/-- The actual normalized Chebyshev function retains the proved eta normalization, the harmonic prefix, and the entire factorial correction. -/
theorem chebyshevPsi_div_eq_moebiusFactorialCorrection {N : ℕ} (hN : 1 < N) :
    Chebyshev.psi N / N = pairedEtaMoebiusLogHarmonic N * Real.log N -
      moebiusHarmonicPrefix N + moebiusFactorialCorrection N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [chebyshevPsi_eq_moebius_logFactorial]
  simp only [pairedEtaMoebiusLogHarmonic, moebiusHarmonicPrefix, moebiusFactorialCorrection,
    Finset.sum_div, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  simp only [pairedEtaMoebiusTrialLogWeight, if_pos hN, moebiusFactorialRemainder,
    Real.log_div hNR.ne' hdR.ne']
  field_simp
  ring

private theorem finite_prefix_eq_range (N : ℕ) :
    moebiusFinitePrefix N = ∑ n ∈ Finset.range (N + 1), (μ n : ℝ) := by
  rw [moebiusFinitePrefix_eq_sum_Icc,
    show Finset.range (N + 1) = Finset.Icc 1 N ∪ {0} by ext n; simp; omega,
    Finset.sum_union (by simp)]
  simp

private theorem finite_antitone_tail {D N : ℕ} (hDN : D < N) {b : ℕ → ℝ}
    (hb : ∀ n ∈ Finset.Icc (D + 1) N, 0 ≤ b n)
    (hanti : AntitoneOn b (Set.Icc (D + 1) N)) {e : ℝ}
    (hm : ∀ n ∈ Finset.Icc D N, |moebiusFinitePrefix n| ≤ e) :
    |∑ n ∈ Finset.Ioc D N, (μ n : ℝ) * b n| ≤ 2 * e * b (D + 1) := by
  have hbN := hb N (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hbD := hb (D + 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hN : |b N * moebiusFinitePrefix N| ≤ e * b N := by
    rw [abs_mul, abs_of_nonneg hbN]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (hm N (Finset.mem_Icc.mpr ⟨hDN.le, le_rfl⟩)) hbN
  have hD : |b (D + 1) * moebiusFinitePrefix D| ≤ e * b (D + 1) := by
    rw [abs_mul, abs_of_nonneg hbD]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (hm D (Finset.mem_Icc.mpr ⟨le_rfl, hDN.le⟩)) hbD
  have hstep (n : ℕ) (hn : n ∈ Finset.Ioc D (N - 1)) : b (n + 1) ≤ b n := by
    have hh := Finset.mem_Ioc.mp hn
    exact hanti ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
  have htel : (∑ n ∈ Finset.Ioc D (N - 1), (b n - b (n + 1))) = b (D + 1) - b N := by
    rw [show Finset.Ioc D (N - 1) = Finset.Ico (D + 1) N by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega]
    calc
      _ = -(∑ n ∈ Finset.Ico (D + 1) N, (b (n + 1) - b n)) := by
        rw [← Finset.sum_neg_distrib]
        congr 1
        ext n
        ring
      _ = _ := by rw [Finset.sum_Ico_sub b (by omega : D + 1 ≤ N)]; ring
  have hsum : |∑ n ∈ Finset.Ioc D (N - 1), (b (n + 1) - b n) * moebiusFinitePrefix n| ≤
      e * (b (D + 1) - b N) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ n ∈ Finset.Ioc D (N - 1), e * (b n - b (n + 1)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hh := Finset.mem_Ioc.mp hn
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hstep n hn))]
        have h := mul_le_mul_of_nonneg_left
          (hm n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
          (sub_nonneg.mpr (hstep n hn))
        convert h using 1 <;> ring
      _ = _ := by rw [← Finset.mul_sum, htel]
  have hp := Finset.sum_Ioc_by_parts b (fun n : ℕ ↦ (μ n : ℝ)) hDN
  simp only [smul_eq_mul, ← finite_prefix_eq_range] at hp
  simp_rw [mul_comm (μ _ : ℝ)]
  rw [hp]
  apply (abs_sub _ _).trans
  have hf := (abs_sub (b N * moebiusFinitePrefix N)
    (b (D + 1) * moebiusFinitePrefix D)).trans (add_le_add hN hD)
  linarith

/-- Both Möbius cancellation estimates control the full complementary factorial tail, including every quotient jump. -/
theorem abs_sum_moebiusFactorialRemainder_high_le {N D Q : ℕ}
    (hDN : D < N) (hQ : 0 < Q) (hquot : (N : ℝ) / (D + 1 : ℝ) ≤ Q)
    {e : ℝ} (he : 0 ≤ e)
    (hm : ∀ n ∈ Finset.Icc D N, |moebiusFinitePrefix n| ≤ e * N)
    (hh : ∀ n ∈ Finset.Icc D N, |moebiusHarmonicPrefix n| ≤ e) :
    |∑ d ∈ Finset.Ioc D N, (μ d : ℝ) / d * moebiusFactorialRemainder N d| ≤
      2 * e * (chebyshevLogFactorial Q + Real.log Q + 1) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hFanti : AntitoneOn (fun n : ℕ ↦ chebyshevLogFactorial (N / n))
      (Set.Icc (D + 1) N) := by
    intro a ha b _ hab
    exact logFactorial_mono (Nat.div_le_div_left hab (by have := ha.1; omega))
  have hF := finite_antitone_tail hDN (b := fun n ↦ chebyshevLogFactorial (N / n))
    (fun _ _ ↦ logFactorial_nonneg _) hFanti hm
  have hqQ : N / (D + 1) ≤ Q := by
    have hlo : ((N / (D + 1) : ℕ) : ℝ) ≤ (N : ℝ) / (D + 1 : ℝ) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < D + 1)).mpr
      exact_mod_cast Nat.div_mul_le_self N (D + 1)
    exact_mod_cast hlo.trans hquot
  have hFu : |(∑ n ∈ Finset.Ioc D N, (μ n : ℝ) * chebyshevLogFactorial (N / n)) / N| ≤
      2 * e * chebyshevLogFactorial Q := by
    rw [abs_div, abs_of_pos hNR]
    apply (div_le_iff₀ hNR).mpr
    calc
      _ ≤ 2 * (e * N) * chebyshevLogFactorial (N / (D + 1)) := hF
      _ ≤ 2 * (e * N) * chebyshevLogFactorial Q :=
        mul_le_mul_of_nonneg_left (logFactorial_mono hqQ) (by positivity)
      _ = _ := by ring
  have hlpos (n : ℕ) (hn : n ∈ Finset.Icc (D + 1) N) :
      0 ≤ Real.log ((N : ℝ) / n) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : 0 < n)
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
      2 * e * Real.log Q := hl.trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (div_pos hNR (by positivity)) (by simpa using hquot)) (by positivity))
  have hc := abs_sum_moebiusHarmonic_antitone_le hDN (b := fun _ ↦ (1 : ℝ))
    (fun _ _ ↦ by norm_num) (fun _ _ _ _ _ ↦ le_rfl) hh
  simp only [mul_one] at hc
  have hid : (∑ d ∈ Finset.Ioc D N, (μ d : ℝ) / d * moebiusFactorialRemainder N d) =
      (∑ d ∈ Finset.Ioc D N, (μ d : ℝ) * chebyshevLogFactorial (N / d)) / N -
      (∑ d ∈ Finset.Ioc D N, (μ d : ℝ) / d * Real.log ((N : ℝ) / d)) +
      ∑ d ∈ Finset.Ioc D N, (μ d : ℝ) / d := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast (by have := (Finset.mem_Ioc.mp hd).1; omega : 0 < d)
    unfold moebiusFactorialRemainder
    field_simp
  rw [hid]
  apply (abs_add_le _ _).trans
  have hf := (abs_sub _ _).trans (add_le_add hFu hlu)
  nlinarith

/-- The whole factorial correction has a uniform divided-cutoff estimate with both actual Möbius prefixes retained. -/
theorem abs_moebiusFactorialCorrection_le_split {N Q : ℕ} (hN : 0 < N) (hQ : 1 < Q)
    {e : ℝ} (he : 0 ≤ e)
    (hm : ∀ n ∈ Finset.Icc (N / Q) N, |moebiusFinitePrefix n| ≤ e * N)
    (hh : ∀ n ∈ Finset.Icc (N / Q) N, |moebiusHarmonicPrefix n| ≤ e) :
    |moebiusFactorialCorrection N| ≤ 4 / Real.sqrt Q +
      2 * e * (chebyshevLogFactorial Q + Real.log Q + 1) := by
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
      _ ≤ 4 * Real.sqrt (1 / (Q : ℝ)) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hratio) (by norm_num)
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
    have h := Finset.sum_sdiff (f := fun d ↦ (μ d : ℝ) / d * moebiusFactorialRemainder N d) hs
    rw [hd] at h
    exact ((add_comm _ _).trans h).symm
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_sum_moebiusFactorialRemainder_low_le hN hDN.le).trans hlow)
    (abs_sum_moebiusFactorialRemainder_high_le hDN (by omega) hquot he hm hh))

/-- The full signed factorial correction tends to zero using the proved ordinary and harmonic Möbius cancellation, with no uncontrolled growing tail. -/
theorem moebiusFactorialCorrection_tendsto_zero :
    Tendsto moebiusFactorialCorrection atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  have hz : Tendsto (fun Q : ℕ ↦ 4 / Real.sqrt Q) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨Q0, hQ0⟩ := Metric.tendsto_atTop.mp hz (eps / 2) (by linarith)
  let Q := max Q0 2
  have hQ : 1 < Q := lt_of_lt_of_le (by decide : 1 < 2) (le_max_right _ _)
  have hsmall : 4 / Real.sqrt Q < eps / 2 := by
    have h := hQ0 Q (le_max_left _ _)
    rw [Real.dist_eq, sub_zero] at h
    exact (le_abs_self _).trans_lt h
  let C := chebyshevLogFactorial Q + Real.log Q + 1
  have hC : 0 < C := by
    have hl := Real.log_nonneg (show (1 : ℝ) ≤ Q by exact_mod_cast hQ.le)
    have hf := logFactorial_nonneg Q
    dsimp [C]
    linarith
  let e := eps / (4 * C)
  have he : 0 < e := div_pos heps (by positivity)
  obtain ⟨NF, hNF⟩ := Metric.tendsto_atTop.mp moebiusFinitePrefix_div_tendsto_zero e he
  obtain ⟨NH, hNH⟩ := Metric.tendsto_atTop.mp moebiusHarmonicPrefix_tendsto_zero e he
  let A := max (max NF NH) 1
  refine ⟨max 1 (A * Q), fun N hN ↦ ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 1) ((le_max_left _ _).trans hN)
  have hDA : A ≤ N / Q := (Nat.le_div_iff_mul_le (by omega : 0 < Q)).mpr
    ((le_max_right _ _).trans hN)
  have hm (n : ℕ) (hn : n ∈ Finset.Icc (N / Q) N) : |moebiusFinitePrefix n| ≤ e * N := by
    have hAn : A ≤ n := hDA.trans (Finset.mem_Icc.mp hn).1
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) ((le_max_right _ _).trans hAn)
    have h := hNF n ((le_max_left NF NH).trans ((le_max_left _ _).trans hAn))
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos] at h
    exact h.le.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast (Finset.mem_Icc.mp hn).2) he.le)
  have hh (n : ℕ) (hn : n ∈ Finset.Icc (N / Q) N) : |moebiusHarmonicPrefix n| ≤ e := by
    have hAn : A ≤ n := hDA.trans (Finset.mem_Icc.mp hn).1
    have h := hNH n ((le_max_right NF NH).trans ((le_max_left _ _).trans hAn))
    simpa only [Real.dist_eq, sub_zero] using h.le
  have heq : 2 * e * C = eps / 2 := by dsimp [e]; field_simp; ring
  rw [Real.dist_eq, sub_zero]
  apply (abs_moebiusFactorialCorrection_le_split hNpos hQ he.le hm hh).trans_lt
  change 4 / Real.sqrt Q + 2 * e * C < eps
  rw [heq]
  linarith

/-- The actual Chebyshev prime-power sum satisfies the prime number theorem at integer cutoffs, derived from the repository's Gaussian Möbius cancellation. -/
theorem chebyshevPsi_nat_div_tendsto_one :
    Tendsto (fun N : ℕ ↦ Chebyshev.psi N / N) atTop (𝓝 1) := by
  have h := (pairedEtaMoebiusLogHarmonic_mul_log_tendsto_one.sub
    moebiusHarmonicPrefix_tendsto_zero).add moebiusFactorialCorrection_tendsto_zero
  norm_num only [sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  exact (chebyshevPsi_div_eq_moebiusFactorialCorrection hN).symm

/-- The same unconditional Chebyshev cancellation holds at every real cutoff, with the floor ratio proved to tend to one. -/
theorem chebyshevPsi_div_tendsto_one :
    Tendsto (fun x : ℝ ↦ Chebyshev.psi x / x) atTop (𝓝 1) := by
  have h := (chebyshevPsi_nat_div_tendsto_one.comp tendsto_nat_floor_atTop).mul
    (tendsto_nat_floor_div_atTop (R := ℝ))
  norm_num only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hf : (0 : ℝ) < (⌊x⌋₊ : ℕ) := by
    exact_mod_cast (Nat.le_floor (by simpa using hx) : 1 ≤ ⌊x⌋₊)
  change Chebyshev.psi (⌊x⌋₊ : ℕ) / (⌊x⌋₊ : ℕ) * ((⌊x⌋₊ : ℕ) / x) = _
  have he : Chebyshev.psi (⌊x⌋₊ : ℕ) = Chebyshev.psi x := by
    simp only [Chebyshev.psi, Nat.floor_natCast]
  rw [he]
  field_simp

/-- The original real Chebyshev error is sublinear; this is qualitative decay, without an RH-strength power rate. -/
theorem chebyshevPsi_error_div_tendsto_zero :
    Tendsto (fun x : ℝ ↦ (Chebyshev.psi x - x) / x) atTop (𝓝 0) := by
  have h := chebyshevPsi_div_tendsto_one.sub_const 1
  norm_num only [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

end

end RiemannGaussian

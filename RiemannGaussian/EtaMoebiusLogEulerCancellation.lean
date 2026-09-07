import RiemannGaussian.MoebiusHarmonicMonotoneTail

/-!
# Cancellation of the complete Euler quotient correction

The original signed Euler correction is split at a genuine divided
cutoff. Its low-divisor part has a uniform reciprocal-cutoff bound.
Finite summation by parts controls the entire remaining part by the
actual harmonic Möbius prefixes and the two monotone quotient weights.
Their proved cancellation makes the complete correction tend to zero.
-/

open Filter
open scoped Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The complete signed Euler quotient correction in the original logarithmic normalization. -/
def pairedEtaMoebiusLogEulerCorrection (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) / n * pairedEtaMoebiusLogEulerRemainder M n

/-- The actual Euler correction splits exactly at any genuine lower divisor cutoff, retaining both signed sums. -/
theorem pairedEtaMoebiusLogEulerCorrection_eq_split {M D : ℕ} (hDM : D ≤ M) :
    pairedEtaMoebiusLogEulerCorrection M =
      (∑ n ∈ Finset.Icc 1 D, (μ n : ℝ) / n * pairedEtaMoebiusLogEulerRemainder M n) +
        ∑ n ∈ Finset.Ioc D M, (μ n : ℝ) / n * pairedEtaMoebiusLogEulerRemainder M n := by
  have hs : Finset.Icc 1 D ⊆ Finset.Icc 1 M := Finset.Icc_subset_Icc le_rfl hDM
  have he : Finset.Icc 1 M \ Finset.Icc 1 D = Finset.Ioc D M := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h := Finset.sum_sdiff (f := fun n ↦ (μ n : ℝ) / n * pairedEtaMoebiusLogEulerRemainder M n) hs
  rw [he] at h
  exact (add_comm _ _).trans h |>.symm

/-- Every low-divisor Euler remainder is retained, with total absolute cost proportional to the physical cutoff ratio. -/
theorem abs_sum_moebius_logEuler_low_le {M D : ℕ} (hM : 0 < M) (hDM : D ≤ M) :
    |∑ n ∈ Finset.Icc 1 D, (μ n : ℝ) / n * pairedEtaMoebiusLogEulerRemainder M n| ≤
      2 * D / (M : ℝ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 1 D, 2 / (M : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [abs_mul, abs_div, abs_of_pos hnR]
      calc
        _ ≤ (1 / (n : ℝ)) * (2 * n / (M : ℝ)) := mul_le_mul
          (div_le_div_of_nonneg_right (abs_real_moebius_le_one n) hnR.le)
          (abs_pairedEtaMoebiusLogEulerRemainder_le (Finset.mem_Icc.mp hn).1
            ((Finset.mem_Icc.mp hn).2.trans hDM)) (abs_nonneg _) (by positivity)
        _ = _ := by field_simp
    _ = _ := by simp; ring

private theorem unpaired_mono : Monotone etaUnpairedArithmeticHarmonicPrefix := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hab)
    (fun _ _ _ ↦ by positivity)

private theorem unpaired_le_log {q : ℕ} (hq : 0 < q) {Q : ℝ} (hqQ : (q : ℝ) ≤ Q) :
    etaUnpairedArithmeticHarmonicPrefix q ≤ 1 + Real.log Q := by
  have he : etaUnpairedArithmeticHarmonicPrefix q = (harmonic q : ℝ) := by
    simp only [etaUnpairedArithmeticHarmonicPrefix, harmonic_eq_sum_Icc,
      Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [he]
  exact (harmonic_le_one_add_log q).trans
    (by linarith [Real.log_le_log (by exact_mod_cast hq : (0 : ℝ) < q) hqQ])

/-- The complete upper-divisor Euler correction is small when the original harmonic Möbius prefixes are small on that same interval; all quotient jumps are included. -/
theorem abs_sum_moebius_logEuler_high_le {M D : ℕ} (hDM : D < M) {Q e : ℝ}
    (he : 0 ≤ e) (hquot : (M : ℝ) / (D + 1 : ℝ) ≤ Q)
    (hm : ∀ n ∈ Finset.Icc D M, |moebiusHarmonicPrefix n| ≤ e) :
    |∑ n ∈ Finset.Ioc D M, (μ n : ℝ) / n * pairedEtaMoebiusLogEulerRemainder M n| ≤
      4 * e * (1 + Real.log Q) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hHanti : AntitoneOn (fun n : ℕ ↦ etaUnpairedArithmeticHarmonicPrefix (M / n)) (Set.Icc (D + 1) M) := by
    intro a ha b _ hab
    exact unpaired_mono (Nat.div_le_div_left hab (by have := ha.1; omega))
  have hH := abs_sum_moebiusHarmonic_antitone_le hDM
    (b := fun n ↦ etaUnpairedArithmeticHarmonicPrefix (M / n))
    (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ by positivity)) hHanti hm
  have hqpos : 0 < M / (D + 1) := (Nat.le_div_iff_mul_le (by omega : 0 < D + 1)).mpr (by omega)
  have hqQ : ((M / (D + 1) : ℕ) : ℝ) ≤ Q := by
    apply le_trans _ hquot
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < D + 1)).mpr
    exact_mod_cast Nat.div_mul_le_self M (D + 1)
  have hHu : |∑ n ∈ Finset.Ioc D M, (μ n : ℝ) / n * etaUnpairedArithmeticHarmonicPrefix (M / n)| ≤
      2 * e * (1 + Real.log Q) :=
    hH.trans (mul_le_mul_of_nonneg_left (unpaired_le_log hqpos hqQ) (by positivity))
  have hlognonneg (n : ℕ) (hn : n ∈ Finset.Icc (D + 1) M) : 0 ≤ Real.log ((M : ℝ) / n) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega)
    apply Real.log_nonneg
    apply (one_le_div hnR).mpr
    exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hloganti : AntitoneOn (fun n : ℕ ↦ Real.log ((M : ℝ) / n)) (Set.Icc (D + 1) M) := by
    intro a ha b hb hab
    have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by have := ha.1; omega)
    have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by have := hb.1; omega)
    apply Real.log_le_log (div_pos hMR hbR)
    exact div_le_div_of_nonneg_left hMR.le haR (by exact_mod_cast hab)
  have hlog := abs_sum_moebiusHarmonic_antitone_le hDM hlognonneg hloganti hm
  have hlogu : |∑ n ∈ Finset.Ioc D M, (μ n : ℝ) / n * Real.log ((M : ℝ) / n)| ≤
      2 * e * Real.log Q := hlog.trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (div_pos hMR (by positivity))
          (by simpa only [Nat.cast_add, Nat.cast_one] using hquot)) (by positivity))
  have hc := abs_sum_moebiusHarmonic_antitone_le hDM (b := fun _ ↦ (1 : ℝ))
    (fun _ _ ↦ by norm_num) (fun _ _ _ _ _ ↦ le_rfl) hm
  simp only [mul_one] at hc
  have hg : |Real.eulerMascheroniConstant| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Real.one_half_lt_eulerMascheroniConstant, Real.eulerMascheroniConstant_lt_two_thirds]
  have hgu : |Real.eulerMascheroniConstant * ∑ n ∈ Finset.Ioc D M, (μ n : ℝ) / n| ≤ 2 * e := by
    rw [abs_mul]
    exact (mul_le_mul hg hc (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hid : (∑ n ∈ Finset.Ioc D M, (μ n : ℝ) / n * pairedEtaMoebiusLogEulerRemainder M n) =
      (∑ n ∈ Finset.Ioc D M, (μ n : ℝ) / n * etaUnpairedArithmeticHarmonicPrefix (M / n)) -
      (∑ n ∈ Finset.Ioc D M, (μ n : ℝ) / n * Real.log ((M : ℝ) / n)) -
        Real.eulerMascheroniConstant * ∑ n ∈ Finset.Ioc D M, (μ n : ℝ) / n := by
    simp only [pairedEtaMoebiusLogEulerRemainder, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul]
    ring
  rw [hid]
  apply (abs_sub _ _).trans
  have hfirst := (abs_sub _ _).trans (add_le_add hHu hlogu)
  nlinarith

/-- A genuine divided-cutoff split bounds the entire original Euler correction, uniformly in the physical cutoff. -/
theorem abs_pairedEtaMoebiusLogEulerCorrection_le_split {M Q : ℕ} (hM : 0 < M) (hQ : 1 < Q)
    {e : ℝ} (he : 0 ≤ e)
    (hm : ∀ n ∈ Finset.Icc (M / Q) M, |moebiusHarmonicPrefix n| ≤ e) :
    |pairedEtaMoebiusLogEulerCorrection M| ≤ 2 / (Q : ℝ) + 4 * e * (1 + Real.log Q) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hDM : M / Q < M := Nat.div_lt_self hM hQ
  have hquot : (M : ℝ) / (M / Q + 1 : ℕ) ≤ Q := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (M / Q + 1 : ℕ))).mpr
    exact_mod_cast (Nat.lt_mul_div_succ M (by omega : 0 < Q)).le
  have hlow : 2 * (M / Q : ℕ) / (M : ℝ) ≤ 2 / (Q : ℝ) := by
    apply (div_le_div_iff₀ hMR hQR).mpr
    have hh : ((M / Q : ℕ) : ℝ) * Q ≤ M := by exact_mod_cast Nat.div_mul_le_self M Q
    nlinarith
  rw [pairedEtaMoebiusLogEulerCorrection_eq_split hDM.le]
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_sum_moebius_logEuler_low_le hM hDM.le).trans hlow)
    (abs_sum_moebius_logEuler_high_le hDM he (by simpa using hquot) hm))

/-- The complete signed Euler correction tends to zero by actual harmonic Möbius cancellation, after the small-divisor and whole complementary tails have both been controlled. -/
theorem pairedEtaMoebiusLogEulerCorrection_tendsto_zero :
    Tendsto pairedEtaMoebiusLogEulerCorrection atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨Q, hQ⟩ := exists_nat_gt (max (1 : ℝ) (4 / eps))
  have hQ1 : 1 < Q := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hQ)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hlog : 0 < 1 + Real.log (Q : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Q by exact_mod_cast hQ1.le)
    linarith
  let e : ℝ := eps / (8 * (1 + Real.log Q))
  have he : 0 < e := div_pos heps (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp moebiusHarmonicPrefix_tendsto_zero e he
  refine ⟨max 1 (N * Q), fun M hM ↦ ?_⟩
  have hM1 : 0 < M := lt_of_lt_of_le (by decide : 0 < 1) ((le_max_left _ _).trans hM)
  have hDN : N ≤ M / Q := (Nat.le_div_iff_mul_le (by omega : 0 < Q)).mpr ((le_max_right _ _).trans hM)
  have hm (n : ℕ) (hn : n ∈ Finset.Icc (M / Q) M) : |moebiusHarmonicPrefix n| ≤ e := by
    have hh := hN n (hDN.trans (Finset.mem_Icc.mp hn).1)
    simpa only [Real.dist_eq, sub_zero] using hh.le
  have hsmall : 2 / (Q : ℝ) < eps / 2 := by
    have hh : 4 / eps < (Q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hQ
    have hp := (div_lt_iff₀ heps).mp hh
    apply (div_lt_iff₀ hQR).mpr
    nlinarith
  have heq : 4 * e * (1 + Real.log Q) = eps / 2 := by dsimp [e]; field_simp; ring
  rw [Real.dist_eq, sub_zero]
  apply (abs_pairedEtaMoebiusLogEulerCorrection_le_split hM1 hQ1 he.le hm).trans_lt
  rw [heq]
  linarith

end

end RiemannGaussian

import RiemannGaussian.MoebiusHarmonicHyperbola
import RiemannGaussian.MoebiusFiniteMellinRate

/-!
# Quantitative cancellation of the ordered harmonic Möbius sum

The full finite hyperbola identity combines every quotient prefix and
every integer remainder. The proved arithmetic decay controls this whole
family, giving an exponential bound on the cubic logarithmic scale for
the original harmonic inverse weight. Its ordered prefix limit is zero;
no unordered or absolute convergence of the Möbius harmonic series is used.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- A fixed constant for the complete harmonic inverse cancellation, including all quotient and rounding contributions. -/
def moebiusHarmonicCancellationConstant : ℝ := 6 + 4 * moebiusFiniteCancellationConstant

/-- The complete harmonic cancellation constant is positive. -/
theorem moebiusHarmonicCancellationConstant_pos : 0 < moebiusHarmonicCancellationConstant := by
  have hc := moebiusFiniteCancellationConstant_pos
  unfold moebiusHarmonicCancellationConstant
  positivity

/-- The quantitative finite arithmetic estimate controls every original prefix beyond one explicit cutoff simultaneously. -/
theorem exists_moebiusFinitePrefix_cubic_tail_bound :
    ∃ H : ℝ, 22 ≤ H ∧ ∀ h : ℝ, H ≤ h → ∀ D : ℕ,
      Real.exp (2 * moebiusFiniteContourCenter h) ≤ (D : ℝ) → ∀ n : ℕ, D ≤ n →
        |moebiusFinitePrefix n| ≤ (moebiusFiniteCancellationConstant + 1) * Real.exp (-h / 2) * n := by
  obtain ⟨H, hH, hprefix⟩ := exists_moebiusFinitePrefix_exponential_remainder
  refine ⟨H, hH, fun h hh D hD n hn ↦ ?_⟩
  have hsize : Real.exp (2 * moebiusFiniteContourCenter h) ≤ (n : ℝ) :=
    hD.trans (by exact_mod_cast hn)
  have hnp : (0 : ℝ) < n := (Real.exp_pos _).trans_le hsize
  have hrem := exp_moebiusFiniteContourCenter_le_saved_power (s := 0)
    (by norm_num) (hH.trans hh) hnp (by simpa using hsize)
  simp only [Complex.zero_re, sub_zero, Real.rpow_one] at hrem
  have hp := hprefix h hh n
  nlinarith

/-- The original harmonic Möbius prefix has a quantitative decay rate after all quotient cutoffs and floor errors are summed. -/
theorem exists_moebiusHarmonicPrefix_cubic_rate :
    ∃ H : ℝ, 22 ≤ H ∧ ∀ h : ℝ, H ≤ h → ∀ D : ℕ,
      Real.exp (2 * moebiusFiniteContourCenter h) ≤ (D : ℝ) →
        |moebiusHarmonicPrefix D| ≤ moebiusHarmonicCancellationConstant * Real.exp (-h / 8) := by
  obtain ⟨H, hH, hprefix⟩ := exists_moebiusFinitePrefix_cubic_tail_bound
  refine ⟨H, hH, fun h hh D hsize ↦ ?_⟩
  have hhh : 22 ≤ h := hH.trans hh
  have hDp : (0 : ℝ) < D := (Real.exp_pos _).trans_le hsize
  have hD : 0 < D := by exact_mod_cast hDp
  let Q := ⌈Real.exp (h / 8)⌉₊
  have hQ : 0 < Q := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hQp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQlo : Real.exp (h / 8) ≤ (Q : ℝ) := Nat.le_ceil _
  have hQhi : (Q : ℝ) ≤ Real.exp (h / 8 + 1) := by
    have hceil : (Q : ℝ) < Real.exp (h / 8) + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
    have he := Real.one_le_exp (show 0 ≤ h / 8 by linarith)
    have h1 : 2 ≤ Real.exp 1 := by have hh := Real.add_one_le_exp (1 : ℝ); norm_num at hh ⊢; exact hh
    rw [Real.exp_add]
    nlinarith
  have hlog : Real.log (Q : ℝ) ≤ h / 8 + 1 := by
    have hl := Real.log_le_log hQp hQhi
    simpa only [Real.log_exp] using hl
  have hinv : 2 / (Q : ℝ) ≤ 2 * Real.exp (-h / 8) := by
    have hi := mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (Real.exp_pos _) hQlo) (by norm_num : (0 : ℝ) ≤ 2)
    rw [show -h / 8 = -(h / 8) by ring, Real.exp_neg]
    simpa only [one_div, one_mul, div_eq_mul_inv] using hi
  let C := moebiusFiniteCancellationConstant + 1
  have hC : 0 < C := by dsimp [C]; linarith [moebiusFiniteCancellationConstant_pos]
  have hcoeff : 2 + Real.log (Q : ℝ) ≤ 4 * Real.exp (3 * h / 8) := by
    have he := Real.add_one_le_exp (3 * h / 8)
    linarith
  have hterm : C * Real.exp (-h / 2) * (2 + Real.log (Q : ℝ)) ≤
      4 * C * Real.exp (-h / 8) := by
    calc
      _ ≤ C * Real.exp (-h / 2) * (4 * Real.exp (3 * h / 8)) :=
        mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = 4 * C * (Real.exp (-h / 2) * Real.exp (3 * h / 8)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have hb := abs_moebiusHarmonicPrefix_le_hyperbola hD hQ
    (show 0 ≤ C * Real.exp (-h / 2) by positivity) (hprefix h hh D hsize)
  exact (hb.trans (add_le_add hinv hterm)).trans_eq (by
    unfold moebiusHarmonicCancellationConstant
    dsimp [C]
    ring)

/-- The literal ordered partial sums of the harmonic Möbius series tend to zero, with their complete finite hyperbola justification. -/
theorem moebiusHarmonicPrefix_tendsto_zero : Tendsto moebiusHarmonicPrefix atTop (𝓝 0) := by
  obtain ⟨H, _, hbound⟩ := exists_moebiusHarmonicPrefix_cubic_rate
  have hdiv : Tendsto (fun h : ℝ ↦ h / 8) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 8) tendsto_id
  have hz : Tendsto (fun h : ℝ ↦ moebiusHarmonicCancellationConstant * Real.exp (-h / 8)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, neg_div, mul_zero] using
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hdiv)).const_mul
        moebiusHarmonicCancellationConstant
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨h, hh, he⟩ := ((eventually_ge_atTop H).and (hz.eventually (gt_mem_nhds heps))).exists
  refine ⟨⌈Real.exp (2 * moebiusFiniteContourCenter h)⌉₊, fun D hD ↦ ?_⟩
  have hsize : Real.exp (2 * moebiusFiniteContourCenter h) ≤ (D : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hD)
  rw [Real.dist_eq, sub_zero]
  exact (hbound h hh D hsize).trans_lt he

end

end RiemannGaussian

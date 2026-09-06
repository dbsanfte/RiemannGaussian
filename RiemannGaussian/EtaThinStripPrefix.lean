import RiemannGaussian.EtaZetaPoleBounds
import RiemannGaussian.EtaMoebiusFinitePrefix
import RiemannGaussian.EtaCurrentPowerSum
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Height-adapted finite eta bounds near the pole line

The actual finite eta prefix and its proved positive-half-plane tail are
kept at the same integer cutoff. Choosing that cutoff above the height
replaces the earlier linear height loss by a small real power, with an
explicit dependence on the width of the strip about `Re s = 1`.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A finite eta prefix is bounded by the corresponding positive power
sum on every strip whose left edge is `1-epsilon`. -/
theorem norm_pairedEtaCorePartialSum_le_thinStrip {s : ℂ} {epsilon : ℝ}
    (he : 0 < epsilon) (hehi : epsilon ≤ 1 / 2) (hs : 1 - epsilon ≤ s.re) (N : ℕ) :
    ‖pairedEtaCorePartialSum N s‖ ≤ (2 * N + 1 : ℝ) ^ epsilon / epsilon := by
  rw [← pairedEtaUnpairedDirichletPrefix_even, pairedEtaUnpairedDirichletPrefix]
  have hsum : (∑ n ∈ Finset.Icc 1 (2 * N), (n : ℝ) ^ (epsilon - 1)) =
      ∑ n ∈ Finset.range (2 * N), (n + 1 : ℝ) ^ (epsilon - 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (2 * N), ‖(pairedEtaDirichletSign n : ℂ) * (n : ℂ) ^ (-s)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 (2 * N), (n : ℝ) ^ (epsilon - 1) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hsign : ‖(pairedEtaDirichletSign n : ℂ)‖ = 1 := by
        unfold pairedEtaDirichletSign
        split <;> norm_num
      rw [norm_mul, hsign, one_mul]
      have hn := Complex.norm_cpow_eq_rpow_re_of_pos hnp (-s)
      simp only [Complex.ofReal_natCast, Complex.neg_re] at hn
      rw [hn]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    _ = _ := hsum
    _ ≤ _ := by
      simpa using sum_range_nat_add_one_rpow_le
        (r := epsilon - 1) (by linarith) (by linarith) (2 * N)

/-- At any cutoff above `norm(s)`, the actual eta remainder gains the
same small height power as the finite prefix. -/
theorem norm_pairedEtaCore_sub_partialSum_le_thinStrip {s : ℂ} {epsilon : ℝ}
    (he : 0 < epsilon) (hehi : epsilon ≤ 1 / 2) (hs : 1 - epsilon ≤ s.re)
    (N : ℕ) (hN : ‖s‖ ≤ (2 * N + 1 : ℝ)) :
    ‖pairedEtaCore s - pairedEtaCorePartialSum N s‖ ≤ 2 * (2 * N + 1 : ℝ) ^ epsilon := by
  have hspos : 0 < s.re := by linarith
  have hu : (0 : ℝ) < 2 * N + 1 := by positivity
  have hu1 : (1 : ℝ) ≤ 2 * N + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hp : (2 * N + 1 : ℝ) ^ (-s.re) ≤ (2 * N + 1 : ℝ) ^ (epsilon - 1) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
  have hpow : (2 * N + 1 : ℝ) * (2 * N + 1 : ℝ) ^ (epsilon - 1) =
      (2 * N + 1 : ℝ) ^ epsilon := by
    conv_lhs => lhs; rw [← Real.rpow_one (2 * N + 1 : ℝ)]
    rw [← Real.rpow_add hu]
    congr 1
    ring
  calc
    _ ≤ ‖s‖ * ((2 * N + 1 : ℝ) ^ (-s.re) / s.re) := by
      simpa using norm_pairedEtaCore_sub_partialSum_le hspos N
    _ ≤ (2 * N + 1 : ℝ) * ((2 * N + 1 : ℝ) ^ (epsilon - 1) / s.re) := by
      gcongr
    _ = (2 * N + 1 : ℝ) ^ epsilon / s.re := by rw [← mul_div_assoc, hpow]
    _ ≤ _ := by
      rw [div_le_iff₀ hspos]
      nlinarith [Real.rpow_nonneg hu.le epsilon]

/-- Splitting the literal eta support at a height-adapted integer
cutoff gives a small-power bound uniform on the thin strip. -/
theorem norm_pairedEtaCore_le_thinStrip_height {s : ℂ} {epsilon T : ℝ}
    (he : 0 < epsilon) (hehi : epsilon ≤ 1 / 2) (hs : 1 - epsilon ≤ s.re)
    (hT : 3 ≤ T) (hsT : ‖s‖ ≤ T) :
    ‖pairedEtaCore s‖ ≤ 6 * T ^ epsilon / epsilon := by
  let N : ℕ := ⌈T⌉₊
  have hceil : T ≤ (N : ℝ) := Nat.le_ceil T
  have hceilhi : (N : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith : 0 ≤ T)
  have huhi : (2 * N + 1 : ℝ) ≤ 3 * T := by linarith
  have hp : (2 * N + 1 : ℝ) ^ epsilon ≤ 3 * T ^ epsilon := by
    calc
      _ ≤ (3 * T) ^ epsilon := Real.rpow_le_rpow (by positivity) huhi he.le
      _ = (3 : ℝ) ^ epsilon * T ^ epsilon := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 3 * T ^ epsilon := by
        gcongr
        exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
          (by linarith : epsilon ≤ 1)).trans_eq (Real.rpow_one 3)
  have hprefix := norm_pairedEtaCorePartialSum_le_thinStrip he hehi hs N
  have htail := norm_pairedEtaCore_sub_partialSum_le_thinStrip he hehi hs N
    ((hsT.trans hceil).trans (by linarith only [Nat.cast_nonneg (α := ℝ) N]))
  have htotal : ‖pairedEtaCore s‖ ≤
      (2 * N + 1 : ℝ) ^ epsilon / epsilon + 2 * (2 * N + 1 : ℝ) ^ epsilon :=
    (norm_le_norm_sub_add _ _).trans ((add_le_add htail hprefix).trans_eq (by ring))
  calc
    _ ≤ 2 * (2 * N + 1 : ℝ) ^ epsilon / epsilon := by
      apply htotal.trans
      rw [le_div_iff₀ he]
      rw [add_mul, div_mul_cancel₀ _ he.ne']
      nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * N + 1) epsilon]
    _ ≤ 2 * (3 * T ^ epsilon) / epsilon := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) he.le
    _ = _ := by ring

end

end RiemannGaussian

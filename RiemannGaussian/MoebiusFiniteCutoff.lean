import RiemannGaussian.GaussianMoebiusHeatScale
import Mathlib.MeasureTheory.Function.Floor

/-!
# Literal finite Möbius cutoffs and logarithmic displacement

The arithmetic carrier here is the ordinary finite signed sum, with no
Gaussian factor. Exact finite differences and the coefficient bound
control its displacement under a logarithmic cutoff shift. These estimates
retain the integer rounding error needed when smoothing is later removed.
-/

open Filter MeasureTheory
open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The literal signed Möbius sum over the positive integers up to a finite cutoff. -/
def moebiusFinitePrefix (M : ℕ) : ℝ := ∑ n ∈ Finset.range M, ((μ (n + 1) : ℤ) : ℝ)

/-- The actual finite prefix at a real logarithmic cutoff, with its integer floor retained. -/
def moebiusLogPrefix (a : ℝ) : ℝ := moebiusFinitePrefix ⌊Real.exp a⌋₊

/-- Every actual real Möbius coefficient has absolute value at most one. -/
theorem abs_real_moebius_le_one (n : ℕ) : |((μ n : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

/-- The complete finite signed prefix is bounded by its actual number of terms. -/
theorem abs_moebiusFinitePrefix_le (M : ℕ) : |moebiusFinitePrefix M| ≤ M := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.range M, (1 : ℝ) :=
      Finset.sum_le_sum fun n _ ↦ abs_real_moebius_le_one (n + 1)
    _ = _ := by simp

/-- Ordered finite cutoffs retain exactly the signed sum over their intervening interval. -/
theorem moebiusFinitePrefix_sub_eq_sum {M N : ℕ} (hMN : M ≤ N) :
    moebiusFinitePrefix N - moebiusFinitePrefix M =
      ∑ n ∈ Finset.Ico M N, ((μ (n + 1) : ℤ) : ℝ) :=
  (Finset.sum_Ico_eq_sub _ hMN).symm

/-- A difference of two actual finite prefixes costs at most the number of changed integer terms. -/
theorem abs_moebiusFinitePrefix_sub_le (M N : ℕ) :
    |moebiusFinitePrefix M - moebiusFinitePrefix N| ≤ |(M : ℝ) - N| := by
  wlog hMN : N ≤ M generalizing M N
  · simpa only [abs_sub_comm] using this N M (by omega)
  rw [moebiusFinitePrefix_sub_eq_sum hMN, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hMN))]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.Ico N M, (1 : ℝ) :=
      Finset.sum_le_sum fun n _ ↦ abs_real_moebius_le_one (n + 1)
    _ = _ := by simp [Nat.cast_sub hMN]

/-- The ordinary finite sum has its literal exponential counting bound at every real logarithmic center. -/
theorem abs_moebiusLogPrefix_le (a : ℝ) : |moebiusLogPrefix a| ≤ Real.exp a :=
  (abs_moebiusFinitePrefix_le _).trans (Nat.floor_le (Real.exp_pos a).le)

/-- Changing a logarithmic cutoff retains the exact multiplicative displacement and one integer-rounding unit. -/
theorem abs_moebiusLogPrefix_sub_le (a v : ℝ) :
    |moebiusLogPrefix (a + v) - moebiusLogPrefix a| ≤ Real.exp a * |Real.exp v - 1| + 1 := by
  apply (abs_moebiusFinitePrefix_sub_le _ _).trans
  have ha := Nat.floor_le (Real.exp_pos a).le
  have hav := Nat.floor_le (Real.exp_pos (a + v)).le
  have ha' := Nat.lt_floor_add_one (Real.exp a)
  have hav' := Nat.lt_floor_add_one (Real.exp (a + v))
  have hb : |(⌊Real.exp (a + v)⌋₊ : ℝ) - ⌊Real.exp a⌋₊| ≤
      |Real.exp (a + v) - Real.exp a| + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self (Real.exp (a + v) - Real.exp a),
      neg_le_abs (Real.exp (a + v) - Real.exp a)]
  apply hb.trans_eq
  rw [Real.exp_add, ← mul_sub_one, abs_mul, abs_of_pos (Real.exp_pos a)]

/-- The actual finite prefix is measurable as a function of the logarithmic cutoff. -/
theorem measurable_moebiusLogPrefix : Measurable moebiusLogPrefix := by
  have hm : Measurable moebiusFinitePrefix := measurable_of_countable _
  exact hm.comp (Nat.measurable_floor.comp Real.measurable_exp)

/-- Each positive integer belongs to the finite logarithmic prefix precisely at its genuine logarithmic endpoint. -/
theorem lt_floor_exp_iff_log_succ_le (n : ℕ) (a : ℝ) :
    n < ⌊Real.exp a⌋₊ ↔ Real.log (n + 1 : ℝ) ≤ a := by
  rw [← Nat.succ_le_iff, Nat.le_floor_iff (Real.exp_pos a).le, Nat.cast_succ,
    Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < n + 1)]

/-- The finite prefix is exactly its endpoint-indicator series, with every signed coefficient retained. -/
theorem moebiusLogPrefix_eq_tsum (a : ℝ) :
    moebiusLogPrefix a =
      ∑' n : ℕ, if Real.log (n + 1 : ℝ) ≤ a then ((μ (n + 1) : ℤ) : ℝ) else 0 := by
  simp_rw [← lt_floor_exp_iff_log_succ_le]
  rw [tsum_eq_sum (s := Finset.range ⌊Real.exp a⌋₊)]
  · unfold moebiusLogPrefix moebiusFinitePrefix
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_range.mp hn, if_true]
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [hn, if_false]

end

end RiemannGaussian

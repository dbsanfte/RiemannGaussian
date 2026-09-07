import RiemannGaussian.EtaMoebiusTrialGridBlocks

/-!
# Actual logarithmic displacement inside a refined Möbius grid cell

The arithmetic primitive makes all artificial boundary coefficients zero.
On every active coefficient the fine and coarse physical points differ
by at most `2M/d`, independently of the refinement factor. The logarithmic
points below agree exactly with the original grid on all valid indices.
-/

namespace RiemannGaussian

noncomputable section

/-- The original physical-grid logarithm, extended nonnegatively beyond its zero-coefficient boundary. -/
def pairedEtaMoebiusTrialGridPoint (d m : ℕ) : ℝ := max 0 (Real.log ((d : ℝ) / m))

/-- Every extended grid point is a nonnegative actual eta translate. -/
theorem pairedEtaMoebiusTrialGridPoint_nonneg (d m : ℕ) :
    0 ≤ pairedEtaMoebiusTrialGridPoint d m := le_max_left _ _

/-- On each valid positive denominator the extension is the unchanged physical logarithm. -/
theorem pairedEtaMoebiusTrialGridPoint_eq_log {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    pairedEtaMoebiusTrialGridPoint d m = Real.log ((d : ℝ) / m) := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  apply max_eq_right
  apply Real.log_nonneg
  exact (le_div_iff₀ hmreal).mpr (by simpa using (show (m : ℝ) ≤ d by exact_mod_cast hmd))

/-- The logarithmic grid point agrees exactly with the original negative logarithm of the physical scale. -/
theorem pairedEtaMoebiusTrialGridPoint_eq_neg_log {d m : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    pairedEtaMoebiusTrialGridPoint d m = -Real.log ((m : ℝ) / d) := by
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hm)
  have hdreal : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (hm.trans_le hmd))
  rw [pairedEtaMoebiusTrialGridPoint_eq_log hm hmd,
    Real.log_div hdreal hmreal, Real.log_div hmreal hdreal]
  ring

/-- Every active refined coefficient lies within `2M/d` of its original coarse-grid point, with no refinement-factor cost. -/
theorem pairedEtaMoebiusTrialGridPoint_block_distance
    {d M q j l : ℕ} (hd : 0 < d) (hq : 0 < q) (hj : j < d) (hl : l < q)
    {w : ℕ → ℝ} (hc : pairedEtaMoebiusTrialEdgeCoefficient (d * q) M w (q * (j + 1) + l) ≠ 0) :
    |pairedEtaMoebiusTrialGridPoint d (j + 1) -
      pairedEtaMoebiusTrialGridPoint (d * q) (q * (j + 1) + l)| ≤ 2 * (M : ℝ) / d := by
  let m := q * (j + 1) + l
  have hm : 0 < m := by dsimp [m]; positivity
  have hmd : m ≤ d * q := by
    by_contra h
    exact hc (pairedEtaMoebiusTrialEdgeCoefficient_eq_zero_of_large (by omega) M w)
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hjreal : (0 : ℝ) < j + 1 := by positivity
  have hmcast : (m : ℝ) = (q : ℝ) * (j + 1 : ℝ) + l := by dsimp [m]; push_cast; rfl
  have horder : ((d * q : ℕ) : ℝ) / m ≤ (d : ℝ) / (j + 1 : ℝ) := by
    apply (div_le_div_iff₀ hmreal hjreal).mpr
    rw [Nat.cast_mul, hmcast]
    nlinarith [mul_nonneg hdreal.le (Nat.cast_nonneg (α := ℝ) l)]
  rw [pairedEtaMoebiusTrialGridPoint_eq_log (by omega) (by omega),
    pairedEtaMoebiusTrialGridPoint_eq_log hm hmd]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by positivity) horder))]
  have hidentity : Real.log ((d : ℝ) / (j + 1 : ℝ)) - Real.log (((d * q : ℕ) : ℝ) / m) =
      Real.log ((m : ℝ) / ((q : ℝ) * (j + 1 : ℝ))) := by
    rw [Nat.cast_mul, Real.log_div hdreal.ne' hjreal.ne',
      Real.log_div (mul_ne_zero hdreal.ne' hqreal.ne') hmreal.ne',
      Real.log_div hmreal.ne' (mul_ne_zero hqreal.ne' hjreal.ne'),
      Real.log_mul hdreal.ne' hqreal.ne', Real.log_mul hqreal.ne' hjreal.ne']
    ring
  rw [hidentity]
  have hquotient : (m : ℝ) / ((q : ℝ) * (j + 1 : ℝ)) - 1 =
      (l : ℝ) / ((q : ℝ) * (j + 1 : ℝ)) := by
    rw [hmcast]
    field_simp
    ring
  have hactive := pairedEtaMoebiusTrialEdgeCoefficient_active hm hc
  have hupper : m + 1 ≤ q * (j + 2) := by dsimp [m]; nlinarith
  have hprod : d * q < (M * (j + 2)) * q := by
    calc
      _ < M * (m + 1) := hactive
      _ ≤ M * (q * (j + 2)) := Nat.mul_le_mul_left M hupper
      _ = _ := by ring
  have hbase : d < M * (j + 2) := (Nat.mul_lt_mul_right hq).mp hprod
  have hbasereal : (d : ℝ) < (M : ℝ) * (j + 2 : ℝ) := by exact_mod_cast hbase
  calc
    _ ≤ (m : ℝ) / ((q : ℝ) * (j + 1 : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    _ = (l : ℝ) / ((q : ℝ) * (j + 1 : ℝ)) := hquotient
    _ ≤ 1 / (j + 1 : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) hjreal).mpr
      have hlreal : (l : ℝ) ≤ q := by exact_mod_cast hl.le
      nlinarith
    _ ≤ 2 * (M : ℝ) / d := by
      apply (div_le_div_iff₀ hjreal hdreal).mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) M) (Nat.cast_nonneg (α := ℝ) j)]

end

end RiemannGaussian

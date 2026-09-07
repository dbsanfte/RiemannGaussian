import RiemannGaussian.EtaMoebiusGridArithmetic

/-!
# The exact arithmetic primitive selected by arbitrarily fine physical grids

The rounded coordinate approaches the true physical coordinate strictly
from below. Its limit therefore selects strict arithmetic steps, including
at every integer endpoint. The signed primitive and its harmonic correction
are retained before taking this limit; no exceptional-time convention or
residual-decay premise is introduced.
-/

open Filter Set
open scoped Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The signed arithmetic atom with precisely the strict endpoints selected by the original grids in the limit. -/
def pairedEtaMoebiusContinuumAtom (n : ℕ) (x : ℝ) : ℝ :=
  x / n * ((if (n : ℝ) < x then 1 else 0) - (if 1 < x then 1 else 0))

/-- The exact signed continuum primitive, including the original complete harmonic correction and the limiting endpoint convention. -/
def pairedEtaMoebiusContinuumPrimitive (M : ℕ) (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * w n * pairedEtaMoebiusContinuumAtom n x

/-- At and below one the entire limiting arithmetic primitive vanishes, including the unit endpoint. -/
theorem pairedEtaMoebiusContinuumPrimitive_eq_zero_of_le_one (M : ℕ) (w : ℕ → ℝ)
    {x : ℝ} (hx : x ≤ 1) : pairedEtaMoebiusContinuumPrimitive M w x = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  simp [pairedEtaMoebiusContinuumAtom, show ¬ (n : ℝ) < x by linarith,
    show ¬ 1 < x by linarith]

/-- Every original rounded coordinate lies strictly below the physical coordinate, including at arithmetic endpoints. -/
theorem pairedEtaMoebiusTrialHeadCoordinate_lt_exp (d : ℕ) (t : ℝ) :
    pairedEtaMoebiusTrialHeadCoordinate d t < Real.exp t := by
  have h := (div_lt_iff₀ (Real.exp_pos t)).mp
    (Nat.lt_floor_add_one ((d : ℝ) / Real.exp t))
  unfold pairedEtaMoebiusTrialHeadCoordinate
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith

/-- Refining the original physical grid recovers the physical coordinate at every time, with no excluded endpoints. -/
theorem pairedEtaMoebiusTrialHeadCoordinate_tendsto (t : ℝ) :
    Tendsto (fun d : ℕ ↦ pairedEtaMoebiusTrialHeadCoordinate d t) atTop (𝓝 (Real.exp t)) := by
  have hz : Tendsto (fun d : ℕ ↦ Real.exp t - pairedEtaMoebiusTrialHeadCoordinate d t) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun d ↦ (sub_pos.mpr
      (pairedEtaMoebiusTrialHeadCoordinate_lt_exp d t)).le)
    · filter_upwards [eventually_ge_atTop 1] with d hd
      exact pairedEtaMoebiusTrialHeadCoordinate_error_le (by omega) t
    · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun _ : ℕ ↦ Real.exp t) atTop (𝓝 (Real.exp t)) := tendsto_const_nhds
  simpa only [sub_sub_cancel, sub_zero] using hc.sub hz

private theorem atom_eq_step_difference {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    pairedEtaMoebiusTrialAtom n x =
      x / n * ((if (n : ℝ) ≤ x then 1 else 0) - (if 1 ≤ x then 1 else 0)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hx : 1 ≤ x
  · by_cases hnx : (n : ℝ) ≤ x
    · rw [pairedEtaMoebiusTrialAtom_eq_zero_of_le hn hnx]
      simp [hx, hnx]
    · rw [pairedEtaMoebiusTrialAtom_eq_neg_div hx (lt_of_not_ge hnx)]
      simp [hx, hnx, neg_div]
  · rw [pairedEtaMoebiusTrialAtom_eq_zero_of_lt_one hn (lt_of_not_ge hx)]
    simp [hx, show ¬ (n : ℝ) ≤ x by linarith]

private theorem rounded_step_tendsto (r t : ℝ) :
    Tendsto (fun d : ℕ ↦ if r ≤ pairedEtaMoebiusTrialHeadCoordinate d t then (1 : ℝ) else 0)
      atTop (𝓝 (if r < Real.exp t then 1 else 0)) := by
  by_cases hr : r < Real.exp t
  · rw [if_pos hr]
    apply tendsto_const_nhds.congr'
    filter_upwards [(pairedEtaMoebiusTrialHeadCoordinate_tendsto t).eventually (lt_mem_nhds hr)] with d hd
    simp [hd.le]
  · rw [if_neg hr]
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun d ↦ by
      have h := (pairedEtaMoebiusTrialHeadCoordinate_lt_exp d t).trans_le (le_of_not_gt hr)
      simp [h.not_ge]

/-- Each original signed atom converges to its precise strict-endpoint arithmetic value, at every real time. -/
theorem pairedEtaMoebiusTrialAtom_tendsto_continuum {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    Tendsto (fun d : ℕ ↦ pairedEtaMoebiusTrialAtom n (pairedEtaMoebiusTrialHeadCoordinate d t))
      atTop (𝓝 (pairedEtaMoebiusContinuumAtom n (Real.exp t))) := by
  simp_rw [atom_eq_step_difference hn]
  exact ((pairedEtaMoebiusTrialHeadCoordinate_tendsto t).div_const n).mul
    ((rounded_step_tendsto n t).sub (rounded_step_tendsto 1 t))

/-- The complete finite signed arithmetic primitive has its exact limiting value before any norm, with every original harmonic correction retained. -/
theorem pairedEtaMoebiusTrialPrimitive_tendsto_continuum (M : ℕ) (w : ℕ → ℝ) (t : ℝ) :
    Tendsto (fun d : ℕ ↦ pairedEtaMoebiusTrialPrimitive M w (pairedEtaMoebiusTrialHeadCoordinate d t))
      atTop (𝓝 (pairedEtaMoebiusContinuumPrimitive M w (Real.exp t))) := by
  apply tendsto_finsetSum
  intro n hn
  exact tendsto_const_nhds.mul (pairedEtaMoebiusTrialAtom_tendsto_continuum (Finset.mem_Icc.mp hn).1 t)

end

end RiemannGaussian

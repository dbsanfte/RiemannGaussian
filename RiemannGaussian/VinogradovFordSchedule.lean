/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordScales

/-!
# Constructing Ford's original admissible scales

The finite backward recurrence is an explicit function, ending at 1/r.
Its stationary lower bound is Ford's phi-star from Lemma 3.5. Positivity,
the upper bound 1/r, the exact recurrence and every root-scale lower bound
are proved from the displayed scalar depth and defect restrictions.
-/

namespace RiemannGaussian.VinogradovFordSchedule
noncomputable section
open VinogradovFordScales

/-- The depth reserve in the original published iteration. -/
def depthReserve (k r : ℕ) (delta : ℝ) : ℝ :=
  2 * delta - ((k : ℝ) - r) * ((k : ℝ) - r + 1)

/-- Ford's stationary lower scale, denoted phi-star in Lemma 3.5. -/
def stationaryScale (k r : ℕ) (delta : ℝ) : ℝ :=
  2 * (k : ℝ) / (2 * r * k + depthReserve k r delta)

/-- The literal backward recurrence at starting depth d, with t steps left. -/
def backwardScale (k r : ℕ) (delta : ℝ) : ℕ → ℕ → ℝ
  | _d, 0 => 1 / (r : ℝ)
  | d, t + 1 => previousScale k (d + 1) r delta (backwardScale k r delta (d + 1) t)

/-- The whole scale schedule, extended constantly beyond its terminal depth. -/
def schedule (k r n : ℕ) (delta : ℝ) (d : ℕ) : ℝ :=
  backwardScale k r delta d (n - d)

/-- The natural triangular depth term is always nonnegative. -/
theorem depth_nonneg (d : ℕ) : 0 ≤ (d : ℝ) * ((d : ℝ) - 1) := by
  cases d with
  | zero => norm_num
  | succ d => push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) d, sq_nonneg (d : ℝ)]

/-- A terminal depth constraint pays every earlier triangular depth term. -/
theorem depth_mono {d e : ℕ} (hde : d ≤ e) :
    (d : ℝ) * ((d : ℝ) - 1) ≤ (e : ℝ) * ((e : ℝ) - 1) := by
  by_cases hd : d = 0
  · subst d
    simpa using depth_nonneg e
  · have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have heR : (d : ℝ) ≤ e := by exact_mod_cast hde
    exact mul_le_mul heR (by linarith) (by linarith) (Nat.cast_nonneg _)

/-- In the initial defect range every scale step is monotone in its successor. -/
theorem previousScale_mono {k r d : ℕ} (hk : 0 < k) (hr : 0 < r) {delta a b : ℝ}
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) (hab : a ≤ b) :
    previousScale k d r delta a ≤ previousScale k d r delta b := by
  have hn : 0 ≤ (k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r + (d : ℝ) ^ 2 - d - 2 * delta := by
    nlinarith [depth_nonneg d, depth_nonneg r, Nat.cast_nonneg (α := ℝ) k]
  unfold previousScale
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hab (div_nonneg hn (by positivity)))

/-- The stationary denominator is positive under the ordinary depth reserve. -/
theorem stationary_denominator_pos {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    {delta : ℝ} (hy : 0 ≤ depthReserve k r delta) :
    0 < 2 * (r : ℝ) * k + depthReserve k r delta := by positivity

/-- The stationary scale is positive and no larger than the terminal scale. -/
theorem stationary_bounds {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    {delta : ℝ} (hy : 0 ≤ depthReserve k r delta) :
    0 < stationaryScale k r delta ∧ stationaryScale k r delta ≤ 1 / (r : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hden := stationary_denominator_pos hk hr hy
  constructor
  · exact div_pos (by positivity) hden
  · unfold stationaryScale
    apply (div_le_iff₀ hden).mpr
    have hmul : 2 * (k : ℝ) * r ≤ 2 * r * k + depthReserve k r delta := by nlinarith
    apply (le_div_iff₀ hrR).mpr at hmul
    simpa only [one_div_mul_eq_div] using hmul

/-- The depth-zero affine recurrence fixes the stationary lower scale exactly. -/
theorem stationary_fixed {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    {delta : ℝ} (hy : 0 ≤ depthReserve k r delta) :
    previousScale k 0 r delta (stationaryScale k r delta) = stationaryScale k r delta := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hden := (stationary_denominator_pos hk hr hy).ne'
  unfold previousScale stationaryScale
  field_simp
  unfold depthReserve
  ring

/-- A later depth preserves the stationary lower bound with its complete
nonnegative triangular correction still present. -/
theorem stationary_le_previous {k r d : ℕ} (hk : 0 < k) (hr : 0 < r)
    {delta psi : ℝ} (hy : 0 ≤ depthReserve k r delta)
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2)
    (hpsi : stationaryScale k r delta ≤ psi) :
    stationaryScale k r delta ≤ previousScale k d r delta psi := by
  have hstar := (stationary_bounds hk hr hy).1.le
  have he : previousScale k d r delta (stationaryScale k r delta) =
      previousScale k 0 r delta (stationaryScale k r delta) +
        ((d : ℝ) * ((d : ℝ) - 1) / (4 * k * r)) * stationaryScale k r delta := by
    unfold previousScale
    push_cast
    ring
  have hl : stationaryScale k r delta ≤ previousScale k d r delta (stationaryScale k r delta) := by
    rw [he, stationary_fixed hk hr hy]
    exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (depth_nonneg d) (by positivity)) hstar)
  exact hl.trans (previousScale_mono hk hr hdelta hpsi)

/-- Every literal backward scale is strictly positive. -/
theorem backwardScale_pos {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    {delta : ℝ} (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) (d t : ℕ) :
    0 < backwardScale k r delta d t := by
  induction t generalizing d with
  | zero => exact one_div_pos.mpr (by exact_mod_cast hr)
  | succ t ih => exact previousScale_pos hk hr (ih (d + 1)).le hdelta

/-- The finite recurrence retains Ford's stationary lower scale at every step. -/
theorem stationary_le_backwardScale {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    {delta : ℝ} (hy : 0 ≤ depthReserve k r delta)
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) (d t : ℕ) :
    stationaryScale k r delta ≤ backwardScale k r delta d t := by
  induction t generalizing d with
  | zero => exact (stationary_bounds hk hr hy).2
  | succ t ih => exact stationary_le_previous hk hr hy hdelta (ih (d + 1))

/-- One terminal depth restriction bounds the complete backward recurrence
above by the diagonal scale. -/
theorem backwardScale_le_terminal {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    {delta : ℝ} (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) (d t : ℕ)
    (hdepth : ((d + t : ℕ) : ℝ) * (((d + t : ℕ) : ℝ) - 1) ≤ depthReserve k r delta) :
    backwardScale k r delta d t ≤ 1 / (r : ℝ) := by
  induction t generalizing d with
  | zero => exact le_rfl
  | succ t ih =>
    have hnext := ih (d + 1) (by simpa only [Nat.add_assoc, Nat.add_comm 1] using hdepth)
    have hd : ((d + 1 : ℕ) : ℝ) * (((d + 1 : ℕ) : ℝ) - 1) ≤ depthReserve k r delta :=
      (depth_mono (by omega : d + 1 ≤ d + (t + 1))).trans hdepth
    exact previousScale_le hk hr (backwardScale_pos hk hr hdelta _ _).le hnext hd

/-- The schedule is exactly terminal at and beyond the specified depth. -/
theorem schedule_terminal (k r n : ℕ) (delta : ℝ) {d : ℕ} (hd : n ≤ d) :
    schedule k r n delta d = 1 / (r : ℝ) := by
  simp only [schedule, Nat.sub_eq_zero_of_le hd, backwardScale]

/-- The constructed function obeys the original published recurrence. -/
theorem schedule_step (k r n : ℕ) (delta : ℝ) {d : ℕ} (hd : d < n) :
    schedule k r n delta d = previousScale k (d + 1) r delta (schedule k r n delta (d + 1)) := by
  unfold schedule
  rw [show n - d = (n - (d + 1)) + 1 by omega, backwardScale]

/-- Positivity, both admissible scale bounds, the terminal value and
the full recurrence hold for the explicitly constructed function. -/
theorem schedule_bounds {k r n : ℕ} (hk : 0 < k) (hr : 0 < r)
    {delta : ℝ} (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2)
    (hdepth : (n : ℝ) * ((n : ℝ) - 1) ≤ depthReserve k r delta)
    (hroot : 1 / ((k : ℝ) + 1) ≤ stationaryScale k r delta) (d : ℕ) :
    0 < schedule k r n delta d ∧
      1 / ((k : ℝ) + 1) ≤ schedule k r n delta d ∧
        schedule k r n delta d ≤ 1 / (r : ℝ) := by
  have hy := (depth_nonneg n).trans hdepth
  refine ⟨backwardScale_pos hk hr hdelta _ _,
    hroot.trans (stationary_le_backwardScale hk hr hy hdelta _ _), ?_⟩
  by_cases hd : d ≤ n
  · exact backwardScale_le_terminal hk hr hdelta d (n - d) (by
      simpa only [Nat.add_sub_of_le hd] using hdepth)
  · rw [schedule_terminal k r n delta (by omega)]

end
end RiemannGaussian.VinogradovFordSchedule

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRetainedFraction
import RiemannGaussian.ZetaRieszCycleCorrelation
import RiemannGaussian.ZetaRieszCycleSaving

/-!
# Separate oriented capacities of the original complex rays

Exact target profiles, original complex directions and separately retained
capacities give proved arithmetic cycle budgets. All failed tests and
remaining original terms stay accounted for. Sufficient aggregate saving
at source scale and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszCycleCapacity
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTransportPhase ZetaRieszConditionedEnergy
open ZetaRieszRetainedFraction

/-- Independent nonnegative retained fractions scale the signed area
by their exact product, preserving every nonzero orientation. -/
theorem area_smul (a b : ℝ) (z w : ℂ) :
    ZetaRieszCycleCore.area (a • z) (b • w) = a * b * ZetaRieszCycleCore.area z w := by
  simp only [ZetaRieszCycleCore.area, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

/-- A positive original cycle remains cancellable whenever all three
remaining fractions are positive. -/
theorem positiveCycle_smul {a b c : ℝ} {z w v : ℂ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : ZetaRieszCycleCore.positiveCycle z w v) :
    ZetaRieszCycleCore.positiveCycle (a • z) (b • w) (c • v) := by
  unfold ZetaRieszCycleCore.positiveCycle
  rw [area_smul, area_smul, area_smul]
  exact ⟨mul_pos (mul_pos hb hc) h.1, mul_pos (mul_pos hc ha) h.2.1,
    mul_pos (mul_pos ha hb) h.2.2⟩

/-- The minimum retained fraction pays all prior competition for mass.
Even exhausted vertices are covered by the zero-capacity branch. -/
theorem scaled_cycleSaving_ge_min {a b c : ℝ} {z w v : ℂ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : ZetaRieszCycleCore.positiveCycle z w v) :
    2 * (min a (min b c) * min ‖z‖ (min ‖w‖ ‖v‖)) ≤
      ZetaRieszCycleCore.cycleSaving (a • z) (b • w) (c • v) := by
  let d := min a (min b c)
  have hd0 : 0 ≤ d := le_min ha (le_min hb hc)
  have hda : d ≤ a := min_le_left _ _
  have hdb : d ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hdc : d ≤ c := (min_le_right _ _).trans (min_le_right _ _)
  by_cases hd : d = 0
  · change 2 * (d * _) ≤ _
    rw [hd, zero_mul, mul_zero]
    exact ZetaRieszCycleCore.cycleSaving_nonneg _ _ _
  · have hdp : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hd)
    have hscaled := positiveCycle_smul (hdp.trans_le hda) (hdp.trans_le hdb) (hdp.trans_le hdc) h
    have hm0 : 0 ≤ min ‖z‖ (min ‖w‖ ‖v‖) := le_min (norm_nonneg _) (le_min (norm_nonneg _) (norm_nonneg _))
    have hmz : min ‖z‖ (min ‖w‖ ‖v‖) ≤ ‖z‖ := min_le_left _ _
    have hmw : min ‖z‖ (min ‖w‖ ‖v‖) ≤ ‖w‖ := (min_le_right _ _).trans (min_le_left _ _)
    have hmv : min ‖z‖ (min ‖w‖ ‖v‖) ≤ ‖v‖ := (min_le_right _ _).trans (min_le_right _ _)
    have hmin : d * min ‖z‖ (min ‖w‖ ‖v‖) ≤ min ‖a • z‖ (min ‖b • w‖ ‖c • v‖) := by
      rw [norm_smul, norm_smul, norm_smul,
        Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, Real.norm_of_nonneg hc]
      exact le_min (mul_le_mul hda hmz hm0 ha)
        (le_min (mul_le_mul hdb hmw hm0 hb) (mul_le_mul hdc hmv hm0 hc))
    exact (mul_le_mul_of_nonneg_left hmin (by norm_num : (0 : ℝ) ≤ 2)).trans
      (ZetaRieszCycleSaving.twice_min_norm_le_cycleSaving hscaled)


/-- Any supported positive dependence of unit rays gives a lower bound
for the exact saving. The three separate angular capacities are retained. -/
theorem cycleSaving_ge_ray_budget {z w v : ℂ}
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (hv : ‖v‖ = 1)
    (hcycle : ZetaRieszCycleCore.positiveCycle z w v)
    {A B C m : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hma : m * ZetaRieszCycleCore.area w v ≤ A)
    (hmb : m * ZetaRieszCycleCore.area v z ≤ B)
    (hmc : m * ZetaRieszCycleCore.area z w ≤ C) :
    m * (ZetaRieszCycleCore.area w v + ZetaRieszCycleCore.area v z +
      ZetaRieszCycleCore.area z w) ≤
        ZetaRieszCycleCore.cycleSaving (A • z) (B • w) (C • v) := by
  by_cases hm0 : m = 0
  · rw [hm0, zero_mul]
    exact ZetaRieszCycleCore.cycleSaving_nonneg _ _ _
  · have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    have hAp := (mul_pos hmp hcycle.1).trans_le hma
    have hBp := (mul_pos hmp hcycle.2.1).trans_le hmb
    have hCp := (mul_pos hmp hcycle.2.2).trans_le hmc
    have hscaled := positiveCycle_smul hAp hBp hCp hcycle
    let D := max (B * C * ZetaRieszCycleCore.area w v)
      (max (C * A * ZetaRieszCycleCore.area v z) (A * B * ZetaRieszCycleCore.area z w))
    have hD : 0 < D := (mul_pos (mul_pos hBp hCp) hcycle.1).trans_le (le_max_left _ _)
    have hma' : m * (B * C * ZetaRieszCycleCore.area w v) ≤ A * B * C := by
      calc
        m * (B * C * ZetaRieszCycleCore.area w v) =
            (B * C) * (m * ZetaRieszCycleCore.area w v) := by ring
        _ ≤ (B * C) * A := mul_le_mul_of_nonneg_left hma (mul_nonneg hB hC)
        _ = A * B * C := by ring
    have hmb' : m * (C * A * ZetaRieszCycleCore.area v z) ≤ A * B * C := by
      calc
        m * (C * A * ZetaRieszCycleCore.area v z) =
            (C * A) * (m * ZetaRieszCycleCore.area v z) := by ring
        _ ≤ (C * A) * B := mul_le_mul_of_nonneg_left hmb (mul_nonneg hC hA)
        _ = A * B * C := by ring
    have hmc' : m * (A * B * ZetaRieszCycleCore.area z w) ≤ A * B * C := by
      calc
        m * (A * B * ZetaRieszCycleCore.area z w) =
            (A * B) * (m * ZetaRieszCycleCore.area z w) := by ring
        _ ≤ (A * B) * C := mul_le_mul_of_nonneg_left hmc (mul_nonneg hA hB)
        _ = A * B * C := by ring
    have hmD : m * D ≤ A * B * C := by
      dsimp [D]
      rw [mul_max_of_nonneg _ _ hm, mul_max_of_nonneg _ _ hm]
      exact max_le hma' (max_le hmb' hmc')
    have hscale : m ≤ D⁻¹ * (A * B * C) := by
      have he := (le_div_iff₀ hD).mpr hmD
      simpa only [div_eq_mul_inv, mul_comm] using he
    have hsum : 0 ≤ ZetaRieszCycleCore.area w v + ZetaRieszCycleCore.area v z +
        ZetaRieszCycleCore.area z w := add_nonneg (add_nonneg hcycle.1.le hcycle.2.1.le) hcycle.2.2.le
    have hsaving : ZetaRieszCycleCore.cycleSaving (A • z) (B • w) (C • v) =
        (D⁻¹ * (A * B * C)) * (ZetaRieszCycleCore.area w v +
          ZetaRieszCycleCore.area v z + ZetaRieszCycleCore.area z w) := by
      rw [ZetaRieszCycleCore.cycleSaving, ZetaRieszCycleCore.cycleScale, if_pos hscaled]
      simp only [area_smul, norm_smul, Real.norm_of_nonneg hA, Real.norm_of_nonneg hB,
        Real.norm_of_nonneg hC, hz, hw, hv, mul_one]
      dsimp [D]
      ring
    rw [hsaving]
    exact mul_le_mul_of_nonneg_right hscale hsum

/-- Keep each arithmetic lower mass divided by its own oriented area,
without collapsing all three amplitudes or retained fractions to minima. -/
def rayCapacity (z w v : ℂ) (A B C : ℝ) : ℝ :=
  min (A / ZetaRieszCycleCore.area w v)
    (min (B / ZetaRieszCycleCore.area v z) (C / ZetaRieszCycleCore.area z w))

/-- The three separate proved lower masses yield a complete oriented
saving bound for the actual larger amplitudes on the same unit rays. -/
theorem cycleSaving_ge_rayCapacity {z w v : ℂ}
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (hv : ‖v‖ = 1)
    (hcycle : ZetaRieszCycleCore.positiveCycle z w v)
    {A B C a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : a ≤ A) (hB : b ≤ B) (hC : c ≤ C) :
    rayCapacity z w v a b c *
      (ZetaRieszCycleCore.area w v + ZetaRieszCycleCore.area v z +
        ZetaRieszCycleCore.area z w) ≤
          ZetaRieszCycleCore.cycleSaving (A • z) (B • w) (C • v) := by
  have hm : 0 ≤ rayCapacity z w v a b c :=
    le_min (div_nonneg ha hcycle.1.le)
      (le_min (div_nonneg hb hcycle.2.1.le) (div_nonneg hc hcycle.2.2.le))
  have hma : rayCapacity z w v a b c ≤ a / ZetaRieszCycleCore.area w v := min_le_left _ _
  have hmb : rayCapacity z w v a b c ≤ b / ZetaRieszCycleCore.area v z :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hmc : rayCapacity z w v a b c ≤ c / ZetaRieszCycleCore.area z w :=
    (min_le_right _ _).trans (min_le_right _ _)
  exact cycleSaving_ge_ray_budget hz hw hv hcycle (ha.trans hA) (hb.trans hB) (hc.trans hC) hm
    (((le_div_iff₀ hcycle.1).mp hma).trans hA)
    (((le_div_iff₀ hcycle.2.1).mp hmb).trans hB)
    (((le_div_iff₀ hcycle.2.2).mp hmc).trans hC)


/-- Every positive original cycle has three nonzero complex amplitudes. -/
theorem positiveCycle_ne_zero {z w v : ℂ} (h : ZetaRieszCycleCore.positiveCycle z w v) :
    z ≠ 0 ∧ w ≠ 0 ∧ v ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hh := h.2.2
    simp [ZetaRieszCycleCore.area, hz] at hh
  · intro hw
    have hh := h.1
    simp [ZetaRieszCycleCore.area, hw] at hh
  · intro hv
    have hh := h.1
    simp [ZetaRieszCycleCore.area, hv] at hh

/-- Normalizing the original rays keeps every positive cycle orientation. -/
theorem positiveCycle_ray {z w v : ℂ} (h : ZetaRieszCycleCore.positiveCycle z w v) :
    ZetaRieszCycleCore.positiveCycle (ZetaRieszMassTransport.ray z)
      (ZetaRieszMassTransport.ray w) (ZetaRieszMassTransport.ray v) := by
  obtain ⟨hz, hw, hv⟩ := positiveCycle_ne_zero h
  exact positiveCycle_smul (inv_pos.mpr (norm_pos_iff.mpr hz))
    (inv_pos.mpr (norm_pos_iff.mpr hw)) (inv_pos.mpr (norm_pos_iff.mpr hv)) h

/-- Actual earlier cycles pay each vertex's retained fraction separately
inside its own oriented capacity. No common-minimum relaxation is made. -/
theorem cycleSaving_retained_rayCapacity (f : ℕ → ℂ) (es : List (ℕ × ℕ × ℕ))
    (i j k : ℕ) (h : ZetaRieszCycleCore.positiveCycle (f i) (f j) (f k))
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hai : a ≤ ‖f i‖) (hbj : b ≤ ‖f j‖) (hck : c ≤ ‖f k‖) :
    rayCapacity (ZetaRieszMassTransport.ray (f i)) (ZetaRieszMassTransport.ray (f j))
      (ZetaRieszMassTransport.ray (f k))
      (retainedFraction f es i * a) (retainedFraction f es j * b) (retainedFraction f es k * c) *
      (ZetaRieszCycleCore.area (ZetaRieszMassTransport.ray (f j)) (ZetaRieszMassTransport.ray (f k)) +
       ZetaRieszCycleCore.area (ZetaRieszMassTransport.ray (f k)) (ZetaRieszMassTransport.ray (f i)) +
       ZetaRieszCycleCore.area (ZetaRieszMassTransport.ray (f i)) (ZetaRieszMassTransport.ray (f j))) ≤
      ZetaRieszCycleCore.cycleSaving (ZetaRieszCycleIteration.cycleResidual f es i)
        (ZetaRieszCycleIteration.cycleResidual f es j) (ZetaRieszCycleIteration.cycleResidual f es k) := by
  obtain ⟨hi, hj, hk⟩ := positiveCycle_ne_zero h
  have hri := (retainedFraction_bounds f es i).1
  have hrj := (retainedFraction_bounds f es j).1
  have hrk := (retainedFraction_bounds f es k).1
  have he := cycleSaving_ge_rayCapacity (ZetaRieszMassTransport.norm_ray hi)
    (ZetaRieszMassTransport.norm_ray hj) (ZetaRieszMassTransport.norm_ray hk) (positiveCycle_ray h)
    (mul_nonneg hri ha) (mul_nonneg hrj hb) (mul_nonneg hrk hc)
    (mul_le_mul_of_nonneg_left hai hri) (mul_le_mul_of_nonneg_left hbj hrj)
    (mul_le_mul_of_nonneg_left hck hrk)
  simpa only [mul_smul, ZetaRieszMassTransport.norm_smul_ray,
    cycleResidual_eq_retainedFraction] using he

/-- The oriented minimum capacity is nonnegative on every positive ray
cycle when all three proposed supplies are nonnegative. -/
theorem rayCapacity_nonneg {z w v : ℂ} (h : ZetaRieszCycleCore.positiveCycle z w v)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ rayCapacity z w v a b c := by
  exact le_min (div_nonneg ha h.1.le)
    (le_min (div_nonneg hb h.2.1.le) (div_nonneg hc h.2.2.le))

end
end RiemannGaussian.ZetaRieszCycleCapacity

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordLowerDefect

/-!
# The logarithmic potential in Ford's moment iteration

The potential retains the second-order decrease in the normalized defect.
Its signed cubic logarithm bounds and every numerical constant are proved;
no potential-decrease estimate is supplied as an assumption.
-/

namespace RiemannGaussian.VinogradovFordPotential
noncomputable section

private def logRemainder (x : ℝ) := x - x ^ 2 / 2 + x ^ 3 / 3 - Real.log (1 + x)

private theorem logRemainder_deriv {x : ℝ} (hx : -1 < x) :
    HasDerivAt logRemainder (x ^ 3 / (1 + x)) x := by
  have hd := (((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 2).div_const 2)).add
    (((hasDerivAt_id x).pow 3).div_const 3)).sub
      (((hasDerivAt_id x).const_add 1).log (by linarith : 1 + x ≠ 0))
  convert! hd using 1
  norm_num
  field_simp [show 1 + x ≠ 0 by linarith, show x + 1 ≠ 0 by linarith]
  ring

/-- The signed cubic logarithm bound needed by Ford's potential argument. -/
theorem log_le_cubic {x : ℝ} (hx : -1 < x) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  have hz : logRemainder 0 = 0 := by norm_num [logRemainder]
  have hrem : 0 ≤ logRemainder x := by
    by_cases hx0 : 0 ≤ x
    · have hm : MonotoneOn logRemainder (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici _)
        · intro t ht
          exact (logRemainder_deriv (by have := ht; change 0 ≤ t at this; linarith)).continuousAt.continuousWithinAt
        · intro t ht
          have ht0 : 0 ≤ t := interior_subset ht
          exact (logRemainder_deriv (by linarith)).differentiableAt.differentiableWithinAt
        · intro t ht
          have ht0 : 0 ≤ t := interior_subset ht
          rw [(logRemainder_deriv (by linarith : -1 < t)).deriv]
          positivity
      simpa only [hz] using hm (show (0 : ℝ) ∈ Set.Ici 0 by simp) hx0 hx0
    · have hm : AntitoneOn logRemainder (Set.Icc x 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        · intro t ht
          exact (logRemainder_deriv (by linarith [ht.1])).continuousAt.continuousWithinAt
        · intro t ht
          have ht' : t ∈ Set.Icc x 0 := interior_subset ht
          exact (logRemainder_deriv (by linarith [ht'.1])).differentiableAt.differentiableWithinAt
        · intro t ht
          have ht' : t ∈ Set.Icc x 0 := interior_subset ht
          rw [(logRemainder_deriv (by linarith [ht'.1] : -1 < t)).deriv]
          have hcube : t ^ 3 ≤ 0 := by
            simpa only [pow_succ] using mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) ht'.2
          exact div_nonpos_of_nonpos_of_nonneg hcube (by linarith [ht'.1])
      have hh := hm (show x ∈ Set.Icc x 0 by constructor <;> linarith)
        (show (0 : ℝ) ∈ Set.Icc x 0 by constructor <;> linarith) (by linarith : x ≤ 0)
      simpa only [hz] using hh
  dsimp [logRemainder] at hrem
  linarith

/-- Ford's increasing normalized-defect potential. -/
def potential (d : ℝ) : ℝ := d + Real.log d + Real.log (2 - d)

/-- The ratio multiplying the normalized decrease in (3.14). -/
def rateRatio (d : ℝ) : ℝ := (2 - d) / (2 - d ^ 2)

/-- The comparison step before inserting the actual smaller defect. -/
def comparisonStep (d b : ℝ) : ℝ := d * (1 - rateRatio d * b)

/-- Both original bounds for the rate ratio hold throughout the defect range. -/
theorem rateRatio_bounds {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2) :
    6 / 7 ≤ rateRatio d ∧ rateRatio d ≤ 1 := by
  have hd2 : d ^ 2 ≤ 1 / 4 := by nlinarith
  have hB : 0 < 2 - d ^ 2 := by linarith
  unfold rateRatio
  constructor
  · apply (le_div_iff₀ hB).mpr
    have hp := mul_nonneg (show 0 ≤ 1 - 2 * d by linarith) (show 0 ≤ 2 - 3 * d by linarith)
    nlinarith
  · apply (div_le_one hB).mpr
    have hp := mul_nonneg hd0 (show 0 ≤ 1 - d by linarith)
    nlinarith

/-- The potential derivative is positive on the whole required interval. -/
theorem potential_hasDerivAt {d : ℝ} (hd0 : 0 < d) (hd : d ≤ 1 / 2) :
    HasDerivAt potential ((2 - d ^ 2) / (d * (2 - d))) d := by
  have hd2 : 2 - d ≠ 0 := by linarith
  have hh := ((hasDerivAt_id d).add (Real.hasDerivAt_log hd0.ne')).add
    (((hasDerivAt_id d).const_sub 2).log hd2)
  convert! hh using 1
  norm_num
  field_simp
  ring

/-- The potential is monotone on the exact normalized-defect domain. -/
theorem potential_monotone : MonotoneOn potential (Set.Ioc 0 (1 / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
  · intro d hd
    exact (potential_hasDerivAt hd.1 hd.2).continuousAt.continuousWithinAt
  · intro d hd
    have hh : d ∈ Set.Ioc 0 (1 / 2) := interior_subset hd
    exact (potential_hasDerivAt hh.1 hh.2).differentiableAt.differentiableWithinAt
  · intro d hd
    have hh : d ∈ Set.Ioc 0 (1 / 2) := interior_subset hd
    rw [(potential_hasDerivAt hh.1 hh.2).deriv]
    have hd2 : d ^ 2 ≤ 1 / 4 := by nlinarith [hh.1, hh.2]
    exact div_nonneg (by linarith) (mul_nonneg hh.1.le (by linarith [hh.2]))

/-- The comparison point is positive and no larger than the input defect. -/
theorem comparisonStep_bounds {d b : ℝ} (hd0 : 0 < d) (hd : d ≤ 1 / 2)
    (hb0 : 0 ≤ b) (hb : b < 1) : 0 < comparisonStep d b ∧ comparisonStep d b ≤ d := by
  obtain ⟨ha0, ha1⟩ := rateRatio_bounds hd0.le hd
  have hp := mul_le_mul_of_nonneg_right ha1 hb0
  have hq := mul_nonneg (show 0 ≤ rateRatio d by linarith) hb0
  unfold comparisonStep
  constructor
  · apply mul_pos hd0
    nlinarith
  · nlinarith

/-- The two logarithmic changes remain signed and exact before estimating. -/
theorem potential_comparison_identity {d b : ℝ} (hd0 : 0 < d) (hd : d ≤ 1 / 2)
    (hb0 : 0 ≤ b) (hb : b < 1) :
    potential (comparisonStep d b) - potential d =
      -d * rateRatio d * b + Real.log (1 - rateRatio d * b) +
        Real.log (1 + d * b / (2 - d ^ 2)) := by
  have hd2 : d ^ 2 ≤ 1 / 4 := by nlinarith
  have hB : 0 < 2 - d ^ 2 := by linarith
  have hab := mul_le_mul_of_nonneg_right (rateRatio_bounds hd0.le hd).2 hb0
  have hstep : 1 - rateRatio d * b ≠ 0 := by nlinarith
  have htwo : 2 - d ≠ 0 := by linarith
  have hlog1 : Real.log (comparisonStep d b) = Real.log d + Real.log (1 - rateRatio d * b) :=
    Real.log_mul hd0.ne' hstep
  have hsplit : 2 - comparisonStep d b = (2 - d) * (1 + d * b / (2 - d ^ 2)) := by
    unfold comparisonStep rateRatio
    field_simp
    ring
  have hfactor : 1 + d * b / (2 - d ^ 2) ≠ 0 := by positivity
  have hlog2 : Real.log (2 - comparisonStep d b) = Real.log (2 - d) +
      Real.log (1 + d * b / (2 - d ^ 2)) := by rw [hsplit, Real.log_mul htwo hfactor]
  unfold potential
  rw [hlog1, hlog2]
  unfold comparisonStep
  ring

/-- The quadratic Taylor coefficient is at least the published `2/5`.
The remainder is paid by `(5*d-2)^2` and `d^2*(1/4-d^2)`. -/
theorem quadratic_reserve {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2) :
    2 / 5 ≤ ((2 - d) ^ 2 + d ^ 2) / (2 * (2 - d ^ 2) ^ 2) := by
  have hd2 : d ^ 2 ≤ 1 / 4 := by nlinarith
  have hB : 0 < 2 - d ^ 2 := by linarith
  apply (le_div_iff₀ (by positivity : 0 < 2 * (2 - d ^ 2) ^ 2)).mpr
  have hp := mul_nonneg (sq_nonneg d) (show 0 ≤ 1 / 4 - d ^ 2 by linarith)
  nlinarith [sq_nonneg (5 * d - 2)]

/-- Ford's signed second-order potential decrease for the comparison step. -/
theorem potential_comparison_le {d b : ℝ} (hd0 : 0 < d) (hd : d ≤ 1 / 2)
    (hb0 : 0 ≤ b) (hb : b < 1) :
    potential (comparisonStep d b) ≤ potential d - b - (2 / 5) * b ^ 2 := by
  have hd2 : d ^ 2 ≤ 1 / 4 := by nlinarith
  have hB : 0 < 2 - d ^ 2 := by linarith
  have hab := mul_le_mul_of_nonneg_right (rateRatio_bounds hd0.le hd).2 hb0
  have hl := log_le_cubic (by nlinarith : -1 < -(rateRatio d * b))
  have hr := log_le_cubic (show -1 < d * b / (2 - d ^ 2) by
    have hh : 0 ≤ d * b / (2 - d ^ 2) := by positivity
    linarith)
  have he := potential_comparison_identity hd0 hd hb0 hb
  simp only [← sub_eq_add_neg] at hl
  have halgebra : -d * rateRatio d * b +
      (-(rateRatio d * b) - (-(rateRatio d * b)) ^ 2 / 2 + (-(rateRatio d * b)) ^ 3 / 3) +
      (d * b / (2 - d ^ 2) - (d * b / (2 - d ^ 2)) ^ 2 / 2 + (d * b / (2 - d ^ 2)) ^ 3 / 3) =
        -b - b ^ 2 * (((2 - d) ^ 2 + d ^ 2) / (2 * (2 - d ^ 2) ^ 2)) +
          b ^ 3 * (d ^ 3 - (2 - d) ^ 3) / (3 * (2 - d ^ 2) ^ 3) := by
    unfold rateRatio
    field_simp
    ring
  have hquad := mul_le_mul_of_nonneg_left (quadratic_reserve hd0.le hd) (sq_nonneg b)
  have hcubic : b ^ 3 * (d ^ 3 - (2 - d) ^ 3) / (3 * (2 - d ^ 2) ^ 3) ≤ 0 := by
    have hp := pow_le_pow_left₀ hd0.le (show d ≤ 2 - d by linarith) 3
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hb0 3) (sub_nonpos.mpr hp)) (by positivity)
  linarith

/-- Inserting any positive smaller defect preserves the same potential gain. -/
theorem potential_step_le {d d' b : ℝ} (hd0 : 0 < d) (hd : d ≤ 1 / 2)
    (hd' : 0 < d') (hb0 : 0 ≤ b) (hb : b < 1) (hstep : d' ≤ comparisonStep d b) :
    potential d' ≤ potential d - b - (2 / 5) * b ^ 2 := by
  have hs := comparisonStep_bounds hd0 hd hb0 hb
  have hmono := potential_monotone ⟨hd', hstep.trans (hs.2.trans hd)⟩
    ⟨hs.1, hs.2.trans hd⟩ hstep
  exact hmono.trans (potential_comparison_le hd0 hd hb0 hb)

end
end RiemannGaussian.VinogradovFordPotential

import RiemannGaussian.SymmetricQuartetEnergy

/-!
# Scalar algebra for the symmetric Pick value disk

This file proves the real/complex inequality at the end of a correctly
derived Schur-complement calculation.  It does not postulate that a Schur
function supplies the required quadratic inequality: that analytic and
matrix-theoretic step remains a separate obligation.
-/

namespace RiemannGaussian

noncomputable section

/-- If a value-disk quadratic has center coefficient `d`, base diagonal
`h`, and second Schur-complement coefficient `M`, then the exact identities
used in the symmetric two-node calculation imply the claimed norm bound.

All four inputs produced by a Pick calculation are explicit here: positivity
of `h`, nonnegativity of `b`, the Cauchy--Schwarz lower bound on `M`, the
norm identity for `d`, and the value-disk quadratic itself. -/
theorem norm_le_two_mul_div_one_add_sq_of_pickDiskQuadratic
    {h M b : ℝ} {d s : ℂ}
    (hh : 0 < h) (hb : 0 ≤ b)
    (hM : h * b ^ 2 ≤ M)
    (hd : ‖d‖ = h * b)
    (hquadratic :
      (h + M) * ‖s‖ ^ 2 ≤ -2 * (s * d).re) :
    ‖s‖ ≤ 2 * b / (1 + b ^ 2) := by
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have hM0 : 0 ≤ M := (mul_nonneg hh.le hb2).trans hM
  have hsum : 0 < h + M := add_pos_of_pos_of_nonneg hh hM0
  have hre : -(s * d).re ≤ ‖s‖ * ‖d‖ := by
    calc
      -(s * d).re ≤ |(s * d).re| := neg_le_abs _
      _ ≤ ‖s * d‖ := Complex.abs_re_le_norm _
      _ = ‖s‖ * ‖d‖ := norm_mul _ _
  have hraw : (h + M) * ‖s‖ ^ 2 ≤ 2 * ‖s‖ * ‖d‖ := by
    linarith
  by_cases hs : ‖s‖ = 0
  · rw [hs]
    positivity
  · have hspos : 0 < ‖s‖ := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hcancel : (h + M) * ‖s‖ ≤ 2 * ‖d‖ := by
      apply (mul_le_mul_iff_of_pos_right hspos).mp
      calc
        ((h + M) * ‖s‖) * ‖s‖ =
            (h + M) * ‖s‖ ^ 2 := by ring
        _ ≤ 2 * ‖s‖ * ‖d‖ := hraw
        _ = (2 * ‖d‖) * ‖s‖ := by ring
    have hdenLower : h * (1 + b ^ 2) ≤ h + M := by
      nlinarith
    have hscaled : h * (1 + b ^ 2) * ‖s‖ ≤ 2 * h * b := by
      calc
        h * (1 + b ^ 2) * ‖s‖ ≤ (h + M) * ‖s‖ :=
          mul_le_mul_of_nonneg_right hdenLower hs0
        _ ≤ 2 * ‖d‖ := hcancel
        _ = 2 * h * b := by rw [hd]; ring
    have hunit : (1 + b ^ 2) * ‖s‖ ≤ 2 * b := by
      apply (mul_le_mul_iff_of_pos_left hh).mp
      calc
        h * ((1 + b ^ 2) * ‖s‖) =
            h * (1 + b ^ 2) * ‖s‖ := by ring
        _ ≤ 2 * h * b := hscaled
        _ = h * (2 * b) := by ring
    exact (le_div_iff₀ (by positivity : 0 < 1 + b ^ 2)).2 <| by
      simpa [mul_comm] using hunit

/-- The Cayley-radius expression used by the Pick bound is monotone on the
closed unit interval. -/
theorem two_mul_div_one_add_sq_mono
    {b r : ℝ} (hb : 0 ≤ b) (hbr : b ≤ r) (hr : r ≤ 1) :
    2 * b / (1 + b ^ 2) ≤ 2 * r / (1 + r ^ 2) := by
  have hr0 : 0 ≤ r := hb.trans hbr
  have hbrMul : b * r ≤ 1 := by
    have : b * r ≤ r * r :=
      mul_le_mul_of_nonneg_right hbr hr0
    nlinarith [mul_le_mul_of_nonneg_left hr hr0]
  rw [div_le_div_iff₀ (by positivity : 0 < 1 + b ^ 2)
    (by positivity : 0 < 1 + r ^ 2)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hbr)
    (sub_nonneg.mpr hbrMul)]

/-- Once the Pick disk gives the bound in terms of `b`, the checked quartet
threshold converts it to the closed form `m / sqrt (m^2 + a^2)`. -/
theorem norm_le_closed_quartet_bound_of_pick_bound
    {m a b s : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hb : 0 ≤ b) (hbThreshold : b ≤ pairHyperbolicThreshold m a)
    (hs : s ≤ 2 * b / (1 + b ^ 2)) :
    s ≤ m / Real.sqrt (m ^ 2 + a ^ 2) := by
  have hthresholdOne : pairHyperbolicThreshold m a ≤ 1 :=
    (pairHyperbolicThreshold_lt_one hm ha).le
  exact hs.trans <|
    (two_mul_div_one_add_sq_mono hb hbThreshold hthresholdOne).trans_eq
      (two_mul_pairHyperbolicThreshold_div_one_add_sq hm ha)

end

end RiemannGaussian

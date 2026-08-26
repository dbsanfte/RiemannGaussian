import RiemannGaussian.SymmetricTwoNodePick

/-!
# Separation-free finite symmetric-quartet defect bound

This file composes the checked pole-energy threshold with the complete finite
two-node Pick estimate.  The result is the closed bound
`m / sqrt (m^2 + a^2)` for the finite residual inner value at the candidate
pole.  No metric-pencil identification is asserted here.
-/

namespace RiemannGaussian

noncomputable section

/-- Strict monotonicity of the Cayley-radius expression along a genuinely
increasing pair in the closed unit interval. -/
theorem two_mul_div_one_add_sq_lt
    {b r : ℝ} (hb : 0 ≤ b) (hbr : b < r) (hr : r ≤ 1) :
    2 * b / (1 + b ^ 2) < 2 * r / (1 + r ^ 2) := by
  have hr0 : 0 < r := hb.trans_lt hbr
  have hbrMul : b * r < 1 := by
    have hlt : b * r < r * r :=
      mul_lt_mul_of_pos_right hbr hr0
    have hle : r * r ≤ 1 := by
      nlinarith
    exact hlt.trans_le hle
  rw [div_lt_div_iff₀ (by positivity : 0 < 1 + b ^ 2)
    (by positivity : 0 < 1 + r ^ 2)]
  nlinarith [mul_pos (sub_pos.mpr hbr) (sub_pos.mpr hbrMul)]

/-- Strict version of the checked terminal threshold conversion. -/
theorem norm_lt_closed_quartet_bound_of_pick_bound
    {m a b s : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hb : 0 ≤ b) (hbThreshold : b < pairHyperbolicThreshold m a)
    (hs : s ≤ 2 * b / (1 + b ^ 2)) :
    s < m / Real.sqrt (m ^ 2 + a ^ 2) := by
  have hthresholdOne : pairHyperbolicThreshold m a ≤ 1 :=
    (pairHyperbolicThreshold_lt_one hm ha).le
  exact hs.trans_lt <|
    (two_mul_div_one_add_sq_lt hb hbThreshold hthresholdOne).trans_eq
      (two_mul_pairHyperbolicThreshold_div_one_add_sq hm ha)

/-- End-to-end finite residual-inner conclusion for one symmetric quartet:
the pole equation forces a strict Blaschke threshold, finite Pick positivity
forces the sharp value disk, and the scalar conversion gives the closed
quartet bound. -/
theorem norm_lowerRootInnerValue_at_pole_lt_closed_quartet_bound
    (p : Polynomial ℂ) {m tau a x v : ℝ} {background : ℂ}
    (hm : 0 < m) (htau : tau ≠ 0) (ha : 0 < a) (hv : 0 < v)
    (hupperPlus : 0 < pairHyperbolicUpperSq (x - tau) v a)
    (hupperMinus : 0 < pairHyperbolicUpperSq (x + tau) v a)
    (hbackground : 0 ≤ background.im)
    (hpole : symmetricQuartetLogDerivativeContribution m tau a
        (upperHalfPlanePoint x v) + background = -Complex.I)
    (hinterpPlus :
      lowerRootInnerValue p (symmetricPickAlphaPlus tau a) =
        -symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a))
    (hinterpMinus :
      lowerRootInnerValue p (symmetricPickAlphaMinus tau a) =
        -symmetricPickBlaschke x v (symmetricPickAlphaMinus tau a)) :
    ‖lowerRootInnerValue p (symmetricPickPole x v)‖ <
      m / Real.sqrt (m ^ 2 + a ^ 2) := by
  let b :=
    ‖symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a)‖
  have hb : 0 ≤ b := norm_nonneg _
  have hbThreshold : b < pairHyperbolicThreshold m a := by
    simpa [b, symmetricPickBlaschke, symmetricPickAlphaPlus] using
      (norm_symmetricTwoPointBlaschke_lt_threshold_of_pole
        hm ha hv hupperPlus hupperMinus hbackground hpole)
  have hPick : ‖lowerRootInnerValue p (symmetricPickPole x v)‖ ≤
      2 * b / (1 + b ^ 2) := by
    simpa [b] using
      (norm_lowerRootInnerValue_at_pole_le_symmetricPickBound
        p htau ha hv hinterpPlus hinterpMinus)
  exact norm_lt_closed_quartet_bound_of_pick_bound
    hm ha hb hbThreshold hPick

/-- If the reflected pole value is the conjugate of the first, the product
of the two residual values obeys the squared quartet bound.  This is the
scalar product statement needed before any separate metric-pencil bridge. -/
theorem norm_lowerRootInnerValue_pole_product_lt_closed_quartet_bound_sq
    (p : Polynomial ℂ) {m tau a x v : ℝ} {background : ℂ}
    (hm : 0 < m) (htau : tau ≠ 0) (ha : 0 < a) (hv : 0 < v)
    (hupperPlus : 0 < pairHyperbolicUpperSq (x - tau) v a)
    (hupperMinus : 0 < pairHyperbolicUpperSq (x + tau) v a)
    (hbackground : 0 ≤ background.im)
    (hpole : symmetricQuartetLogDerivativeContribution m tau a
        (upperHalfPlanePoint x v) + background = -Complex.I)
    (hinterpPlus :
      lowerRootInnerValue p (symmetricPickAlphaPlus tau a) =
        -symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a))
    (hinterpMinus :
      lowerRootInnerValue p (symmetricPickAlphaMinus tau a) =
        -symmetricPickBlaschke x v (symmetricPickAlphaMinus tau a))
    (hreflect :
      lowerRootInnerValue p (symmetricPickPole (-x) v) =
        starRingEnd ℂ
          (lowerRootInnerValue p (symmetricPickPole x v))) :
    ‖lowerRootInnerValue p (symmetricPickPole x v) *
        lowerRootInnerValue p (symmetricPickPole (-x) v)‖ <
      m ^ 2 / (m ^ 2 + a ^ 2) := by
  have hsingle :=
    norm_lowerRootInnerValue_at_pole_lt_closed_quartet_bound
      p hm htau ha hv hupperPlus hupperMinus hbackground hpole
      hinterpPlus hinterpMinus
  have hsqrt : 0 < Real.sqrt (m ^ 2 + a ^ 2) := by positivity
  have hden : 0 < m ^ 2 + a ^ 2 := by positivity
  rw [hreflect, norm_mul, Complex.norm_conj]
  have hnorm : 0 ≤ ‖lowerRootInnerValue p (symmetricPickPole x v)‖ :=
    norm_nonneg _
  have hbound : 0 < m / Real.sqrt (m ^ 2 + a ^ 2) :=
    div_pos hm hsqrt
  calc
    ‖lowerRootInnerValue p (symmetricPickPole x v)‖ *
          ‖lowerRootInnerValue p (symmetricPickPole x v)‖ <
        (m / Real.sqrt (m ^ 2 + a ^ 2)) *
          (m / Real.sqrt (m ^ 2 + a ^ 2)) :=
      mul_self_lt_mul_self hnorm hsingle
    _ = m ^ 2 / (m ^ 2 + a ^ 2) := by
      rw [div_mul_div_comm]
      rw [show Real.sqrt (m ^ 2 + a ^ 2) *
          Real.sqrt (m ^ 2 + a ^ 2) = m ^ 2 + a ^ 2 by
        simpa [pow_two] using Real.sq_sqrt hden.le]
      ring

end

end RiemannGaussian

import RiemannGaussian.HyperbolicEnergySuperadditive

/-!
# Unequal-height finite hyperbolic energy

This file reduces a finite collection of unequal-height pair costs to the
checked equal-height multiset theorem.  A common positive lower bound on the
heights gives a dominating common cost, so a unit weighted pole budget forces
the complete pseudo-hyperbolic radius product below the exact threshold at
that lower height.
-/

namespace RiemannGaussian

noncomputable section

/-- At fixed radius and nonnegative weight, pair cost decreases as the root
height increases. -/
theorem pairHyperbolicCost_le_of_height_le
    {m a0 a r : ℝ} (hm : 0 ≤ m) (ha0 : 0 < a0)
    (haa : a0 ≤ a) (hr : 0 < r) (hr1 : r ≤ 1) :
    pairHyperbolicCost m a r ≤ pairHyperbolicCost m a0 r := by
  have ha : 0 < a := ha0.trans_le haa
  have hk : 0 ≤ 1 / r - r := by
    have hinv : 1 ≤ 1 / r := by
      exact (le_div_iff₀ hr).2 (by simpa using hr1)
    exact sub_nonneg.mpr (hr1.trans hinv)
  have hcoeff : m / (2 * a) ≤ m / (2 * a0) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * a)
      (by positivity : 0 < 2 * a0)]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hm
  unfold pairHyperbolicCost
  exact mul_le_mul_of_nonneg_right hcoeff hk

/-- Sum comparison for a multiset of `(height, radius)` pairs.  Replacing
every height by a common positive lower bound can only increase total cost. -/
theorem pairHyperbolicCost_multiset_sum_le_commonLowerHeight
    {m a0 : ℝ} (hm : 0 ≤ m) (ha0 : 0 < a0)
    (pairs : Multiset (ℝ × ℝ))
    (hheight : ∀ ar ∈ pairs, a0 ≤ ar.1)
    (hrpos : ∀ ar ∈ pairs, 0 < ar.2)
    (hrone : ∀ ar ∈ pairs, ar.2 ≤ 1) :
    (pairs.map fun ar => pairHyperbolicCost m ar.1 ar.2).sum ≤
      ((pairs.map Prod.snd).map fun r =>
        pairHyperbolicCost m a0 r).sum := by
  induction pairs using Multiset.induction_on with
  | empty => simp
  | cons ar s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact add_le_add
        (pairHyperbolicCost_le_of_height_le hm ha0
          (hheight ar (by simp)) (hrpos ar (by simp))
          (hrone ar (by simp)))
        (ih
          (fun ar har => hheight ar (by simp [har]))
          (fun ar har => hrpos ar (by simp [har]))
          (fun ar har => hrone ar (by simp [har])))

/-- Nonstrict unequal-height product theorem, valid for any finite number of
pairs.  A unit true-cost budget puts the complete radius product at or below
the common-lower-height threshold. -/
theorem weightedPairHyperbolicCost_multiset_prod_le_threshold_of_lowerHeight
    {m a0 : ℝ} (hm : 0 < m) (ha0 : 0 < a0)
    (pairs : Multiset (ℝ × ℝ))
    (hheight : ∀ ar ∈ pairs, a0 ≤ ar.1)
    (hrpos : ∀ ar ∈ pairs, 0 < ar.2)
    (hrone : ∀ ar ∈ pairs, ar.2 < 1)
    (hcost : 1 ≤
      (pairs.map fun ar => pairHyperbolicCost m ar.1 ar.2).sum) :
    (pairs.map Prod.snd).prod ≤ pairHyperbolicThreshold m a0 := by
  let radii := pairs.map Prod.snd
  have hrposRadii : ∀ r ∈ radii, 0 < r := by
    intro r hr
    obtain ⟨ar, har, rfl⟩ := Multiset.mem_map.mp hr
    exact hrpos ar har
  have hroneRadii : ∀ r ∈ radii, r < 1 := by
    intro r hr
    obtain ⟨ar, har, rfl⟩ := Multiset.mem_map.mp hr
    exact hrone ar har
  have hcommon : 1 ≤
      (radii.map fun r => pairHyperbolicCost m a0 r).sum :=
    hcost.trans
      (pairHyperbolicCost_multiset_sum_le_commonLowerHeight
        hm.le ha0 pairs hheight hrpos fun ar har => (hrone ar har).le)
  apply radius_le_pairHyperbolicThreshold_of_one_le_cost hm ha0
  exact hcommon.trans
    (pairHyperbolicCost_multiset_sum_le_cost_prod
      hm.le ha0 radii hrposRadii fun r hr => (hroneRadii r hr).le)

/-- Unequal-height finite product theorem.  A unit sum of the true weighted
costs forces the complete radius product below the common-lower-height
threshold. -/
theorem weightedPairHyperbolicCost_multiset_prod_lt_threshold_of_lowerHeight
    {m a0 : ℝ} (hm : 0 < m) (ha0 : 0 < a0)
    (pairs : Multiset (ℝ × ℝ)) (hcard : 2 ≤ pairs.card)
    (hheight : ∀ ar ∈ pairs, a0 ≤ ar.1)
    (hrpos : ∀ ar ∈ pairs, 0 < ar.2)
    (hrone : ∀ ar ∈ pairs, ar.2 < 1)
    (hcost : 1 ≤
      (pairs.map fun ar => pairHyperbolicCost m ar.1 ar.2).sum) :
    (pairs.map Prod.snd).prod < pairHyperbolicThreshold m a0 := by
  let radii := pairs.map Prod.snd
  have hcardRadii : 2 ≤ radii.card := by
    simpa [radii] using hcard
  have hrposRadii : ∀ r ∈ radii, 0 < r := by
    intro r hr
    obtain ⟨ar, har, rfl⟩ := Multiset.mem_map.mp hr
    exact hrpos ar har
  have hroneRadii : ∀ r ∈ radii, r < 1 := by
    intro r hr
    obtain ⟨ar, har, rfl⟩ := Multiset.mem_map.mp hr
    exact hrone ar har
  have hcommon : 1 ≤
      (radii.map fun r => pairHyperbolicCost m a0 r).sum :=
    hcost.trans
      (pairHyperbolicCost_multiset_sum_le_commonLowerHeight
        hm.le ha0 pairs hheight hrpos fun ar har => (hrone ar har).le)
  exact multiset_prod_lt_pairHyperbolicThreshold_of_cost_sum
    hm ha0 radii hcardRadii hrposRadii hroneRadii hcommon

/-! ## Complex-coordinate lift -/

/-- Pseudo-hyperbolic distance between distinct upper-half-plane points is
strictly positive. -/
theorem upperHalfPlanePseudoHyperbolicDistance_pos_of_ne
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    (hne : z ≠ alpha) :
    0 < upperHalfPlanePseudoHyperbolicDistance z alpha := by
  have hupper : 0 <
      pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im := by
    rw [show pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im =
        Complex.normSq (z - alpha) by
      unfold pairHyperbolicUpperSq Complex.normSq
      simp
      ring]
    exact Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  have halphaForm :
      (alpha.re : ℂ) + Complex.I * (alpha.im : ℂ) = alpha := by
    rw [mul_comm]
    exact Complex.re_add_im alpha
  have hzForm : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    rw [mul_comm]
    exact Complex.re_add_im z
  rw [← halphaForm, ← hzForm,
    upperHalfPlanePseudoHyperbolicDistance_eq_pairRadius
      alpha.re alpha.im z.re z.im halpha hz]
  exact pairHyperbolicRadius_pos halpha hz hupper

/-- Pseudo-hyperbolic distance between upper-half-plane points is strictly
below one. -/
theorem upperHalfPlanePseudoHyperbolicDistance_lt_one
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im) :
    upperHalfPlanePseudoHyperbolicDistance z alpha < 1 := by
  have halphaForm :
      (alpha.re : ℂ) + Complex.I * (alpha.im : ℂ) = alpha := by
    rw [mul_comm]
    exact Complex.re_add_im alpha
  have hzForm : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    rw [mul_comm]
    exact Complex.re_add_im z
  rw [← halphaForm, ← hzForm,
    upperHalfPlanePseudoHyperbolicDistance_eq_pairRadius
      alpha.re alpha.im z.re z.im halpha hz]
  exact pairHyperbolicRadius_lt_one halpha hz

/-- Coordinate-free form of the universal pair-energy lower bound. -/
theorem onePairLogDerivativeContribution_im_ge_neg_cost_complex
    {m : ℝ} (hm : 0 ≤ m) {z alpha : ℂ}
    (hz : 0 < z.im) (halpha : 0 < alpha.im) (hne : z ≠ alpha) :
    -pairHyperbolicCost m alpha.im
        (upperHalfPlanePseudoHyperbolicDistance z alpha) ≤
      (onePairLogDerivativeContribution m alpha z).im := by
  have hupper : 0 <
      pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im := by
    rw [show pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im =
        Complex.normSq (z - alpha) by
      unfold pairHyperbolicUpperSq Complex.normSq
      simp
      ring]
    exact Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  have halphaForm :
      (alpha.re : ℂ) + Complex.I * (alpha.im : ℂ) = alpha := by
    rw [mul_comm]
    exact Complex.re_add_im alpha
  have hzForm : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    rw [mul_comm]
    exact Complex.re_add_im z
  simpa only [halphaForm, hzForm] using
    (onePairLogDerivativeContribution_im_ge_neg_hyperbolicCost
      hm halpha hz hupper)

/-- Away from vertical alignment, the coordinate-free one-pair energy bound
is strict. -/
theorem onePairLogDerivativeContribution_im_gt_neg_cost_complex_of_re_ne
    {m : ℝ} (hm : 0 < m) {z alpha : ℂ}
    (hz : 0 < z.im) (halpha : 0 < alpha.im)
    (hre : z.re ≠ alpha.re) :
    -pairHyperbolicCost m alpha.im
        (upperHalfPlanePseudoHyperbolicDistance z alpha) <
      (onePairLogDerivativeContribution m alpha z).im := by
  have halphaForm :
      (alpha.re : ℂ) + Complex.I * (alpha.im : ℂ) = alpha := by
    rw [mul_comm]
    exact Complex.re_add_im alpha
  have hzForm : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    rw [mul_comm]
    exact Complex.re_add_im z
  simpa only [halphaForm, hzForm] using
    (onePairLogDerivativeContribution_im_gt_neg_hyperbolicCost_of_horizontal_ne
      hm halpha hz (sub_ne_zero.mpr hre))

/-- If a finite collection of upper-root pair contributions has imaginary
part at most `-1`, its exact weighted hyperbolic cost sum is at least one. -/
theorem one_le_weightedPairHyperbolicCost_sum_of_im_le_neg_one
    {m : ℝ} (hm : 0 ≤ m) {z : ℂ} {upper : Multiset ℂ}
    (hz : 0 < z.im)
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    (hne : ∀ alpha ∈ upper, z ≠ alpha)
    (hsum : ((upper.map fun alpha =>
      onePairLogDerivativeContribution m alpha z).sum).im ≤ -1) :
    1 ≤ (upper.map fun alpha =>
      pairHyperbolicCost m alpha.im
        (upperHalfPlanePseudoHyperbolicDistance z alpha)).sum := by
  have hbound :
      -((upper.map fun alpha =>
          pairHyperbolicCost m alpha.im
            (upperHalfPlanePseudoHyperbolicDistance z alpha)).sum) ≤
        ((upper.map fun alpha =>
          onePairLogDerivativeContribution m alpha z).sum).im := by
    clear hsum
    induction upper using Multiset.induction_on with
    | empty => simp
    | cons alpha s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im]
        have hpair := onePairLogDerivativeContribution_im_ge_neg_cost_complex
          hm hz (halpha alpha (by simp)) (hne alpha (by simp))
        have htail := ih
          (fun beta hbeta => halpha beta (by simp [hbeta]))
          (fun beta hbeta => hne beta (by simp [hbeta]))
        linarith
  linarith

/-- Nonstrict complex unequal-height product theorem, valid without a
cardinality hypothesis. -/
theorem upperRootPseudoHyperbolicProduct_le_threshold_of_im_sum
    {m a0 : ℝ} (hm : 0 < m) (ha0 : 0 < a0)
    {z : ℂ} {upper : Multiset ℂ} (hz : 0 < z.im)
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    (hne : ∀ alpha ∈ upper, z ≠ alpha)
    (hminHeight : ∀ alpha ∈ upper, a0 ≤ alpha.im)
    (hsum : ((upper.map fun alpha =>
      onePairLogDerivativeContribution m alpha z).sum).im ≤ -1) :
    (upper.map fun alpha =>
      upperHalfPlanePseudoHyperbolicDistance z alpha).prod ≤
        pairHyperbolicThreshold m a0 := by
  let pairs : Multiset (ℝ × ℝ) := upper.map fun alpha =>
    (alpha.im, upperHalfPlanePseudoHyperbolicDistance z alpha)
  have hcost : 1 ≤
      (upper.map fun alpha =>
        pairHyperbolicCost m alpha.im
          (upperHalfPlanePseudoHyperbolicDistance z alpha)).sum :=
    one_le_weightedPairHyperbolicCost_sum_of_im_le_neg_one
      hm.le hz halpha hne hsum
  have hheightPairs : ∀ ar ∈ pairs, a0 ≤ ar.1 := by
    intro ar har
    obtain ⟨alpha, halphaMem, rfl⟩ := Multiset.mem_map.mp har
    exact hminHeight alpha halphaMem
  have hrposPairs : ∀ ar ∈ pairs, 0 < ar.2 := by
    intro ar har
    obtain ⟨alpha, halphaMem, rfl⟩ := Multiset.mem_map.mp har
    exact upperHalfPlanePseudoHyperbolicDistance_pos_of_ne
      hz (halpha alpha halphaMem) (hne alpha halphaMem)
  have hronePairs : ∀ ar ∈ pairs, ar.2 < 1 := by
    intro ar har
    obtain ⟨alpha, halphaMem, rfl⟩ := Multiset.mem_map.mp har
    exact upperHalfPlanePseudoHyperbolicDistance_lt_one
      hz (halpha alpha halphaMem)
  have hweighted : 1 ≤
      (pairs.map fun ar => pairHyperbolicCost m ar.1 ar.2).sum := by
    simpa [pairs, Multiset.map_map, Function.comp_apply] using hcost
  have hresult :=
    weightedPairHyperbolicCost_multiset_prod_le_threshold_of_lowerHeight
      hm ha0 pairs hheightPairs hrposPairs hronePairs hweighted
  simpa [pairs, Multiset.map_map, Function.comp_apply] using hresult

/-- Final complex unequal-height product theorem.  The only height input is a
common positive lower bound for the finite upper-root collection. -/
theorem upperRootPseudoHyperbolicProduct_lt_threshold_of_im_sum
    {m a0 : ℝ} (hm : 0 < m) (ha0 : 0 < a0)
    {z : ℂ} {upper : Multiset ℂ} (hz : 0 < z.im)
    (hcard : 2 ≤ upper.card)
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    (hne : ∀ alpha ∈ upper, z ≠ alpha)
    (hminHeight : ∀ alpha ∈ upper, a0 ≤ alpha.im)
    (hsum : ((upper.map fun alpha =>
      onePairLogDerivativeContribution m alpha z).sum).im ≤ -1) :
    (upper.map fun alpha =>
      upperHalfPlanePseudoHyperbolicDistance z alpha).prod <
        pairHyperbolicThreshold m a0 := by
  let pairs : Multiset (ℝ × ℝ) := upper.map fun alpha =>
    (alpha.im, upperHalfPlanePseudoHyperbolicDistance z alpha)
  have hcost : 1 ≤
      (upper.map fun alpha =>
        pairHyperbolicCost m alpha.im
          (upperHalfPlanePseudoHyperbolicDistance z alpha)).sum :=
    one_le_weightedPairHyperbolicCost_sum_of_im_le_neg_one
      hm.le hz halpha hne hsum
  have hcardPairs : 2 ≤ pairs.card := by
    simpa [pairs] using hcard
  have hheightPairs : ∀ ar ∈ pairs, a0 ≤ ar.1 := by
    intro ar har
    obtain ⟨alpha, halphaMem, rfl⟩ := Multiset.mem_map.mp har
    exact hminHeight alpha halphaMem
  have hrposPairs : ∀ ar ∈ pairs, 0 < ar.2 := by
    intro ar har
    obtain ⟨alpha, halphaMem, rfl⟩ := Multiset.mem_map.mp har
    exact upperHalfPlanePseudoHyperbolicDistance_pos_of_ne
      hz (halpha alpha halphaMem) (hne alpha halphaMem)
  have hronePairs : ∀ ar ∈ pairs, ar.2 < 1 := by
    intro ar har
    obtain ⟨alpha, halphaMem, rfl⟩ := Multiset.mem_map.mp har
    exact upperHalfPlanePseudoHyperbolicDistance_lt_one
      hz (halpha alpha halphaMem)
  have hweighted : 1 ≤
      (pairs.map fun ar => pairHyperbolicCost m ar.1 ar.2).sum := by
    simpa [pairs, Multiset.map_map, Function.comp_apply] using hcost
  have hresult :=
    weightedPairHyperbolicCost_multiset_prod_lt_threshold_of_lowerHeight
      hm ha0 pairs hcardPairs hheightPairs hrposPairs hronePairs hweighted
  simpa [pairs, Multiset.map_map, Function.comp_apply] using hresult

end

end RiemannGaussian

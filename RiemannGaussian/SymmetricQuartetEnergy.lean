import RiemannGaussian.HyperbolicEnergySuperadditive

/-!
# Separation-free symmetric-quartet energy bound

This file connects the checked one-pair inequality to the pole equation for
one symmetric off-real quartet.  It proves, without a horizontal-separation
hypothesis, that a nonnegative-imaginary-part background forces the product
of the two pseudo-hyperbolic radii below the sharp scalar threshold.  It also
identifies that product with the modulus of the corresponding degree-two
Blaschke product.

No Nevanlinna--Pick interpolation assertion is used here.
-/

namespace RiemannGaussian

noncomputable section

/-- A point with real coordinate `x` and positive-height coordinate `v`. -/
def upperHalfPlanePoint (x v : ℝ) : ℂ :=
  (x : ℂ) + Complex.I * (v : ℂ)

/-- The two-pair logarithmic-derivative contribution attached to upper zeros
at `±tau + I*a`. -/
def symmetricQuartetLogDerivativeContribution
    (m tau a : ℝ) (z : ℂ) : ℂ :=
  onePairLogDerivativeContribution m (upperHalfPlanePoint tau a) z +
    onePairLogDerivativeContribution m (upperHalfPlanePoint (-tau) a) z

/-- The two radii from `x + I*v` to the symmetric upper zeros. -/
def symmetricQuartetRadiusPlus (tau a x v : ℝ) : ℝ :=
  pairHyperbolicRadius (x - tau) v a

def symmetricQuartetRadiusMinus (tau a x v : ℝ) : ℝ :=
  pairHyperbolicRadius (x + tau) v a

theorem symmetricQuartetLogDerivativeContribution_im
    {m tau a x v : ℝ} (ha : 0 < a) (hv : 0 < v)
    (hplus : 0 < pairHyperbolicUpperSq (x - tau) v a)
    (hminus : 0 < pairHyperbolicUpperSq (x + tau) v a) :
    (symmetricQuartetLogDerivativeContribution m tau a
      (upperHalfPlanePoint x v)).im =
      pairImaginaryEnergy m (x - tau) v a +
        pairImaginaryEnergy m (x + tau) v a := by
  unfold symmetricQuartetLogDerivativeContribution upperHalfPlanePoint
  rw [Complex.add_im,
    onePairLogDerivativeContribution_im m tau a x v ha hv hplus,
    onePairLogDerivativeContribution_im m (-tau) a x v ha hv]
  · congr 2
    ring
  · simpa only [sub_neg_eq_add] using hminus

/-- The pole equation `q_qt(p) + h(p) = -I`, together with `Im h(p) ≥ 0`,
forces at least one unit of collective hyperbolic cost. -/
theorem one_le_symmetricQuartet_cost_sum_of_pole
    {m tau a x v : ℝ} {background : ℂ}
    (hm : 0 ≤ m) (ha : 0 < a) (hv : 0 < v)
    (hplus : 0 < pairHyperbolicUpperSq (x - tau) v a)
    (hminus : 0 < pairHyperbolicUpperSq (x + tau) v a)
    (hbackground : 0 ≤ background.im)
    (hpole : symmetricQuartetLogDerivativeContribution m tau a
        (upperHalfPlanePoint x v) + background = -Complex.I) :
    1 ≤
      pairHyperbolicCost m a (symmetricQuartetRadiusPlus tau a x v) +
        pairHyperbolicCost m a
          (symmetricQuartetRadiusMinus tau a x v) := by
  have him := congrArg Complex.im hpole
  have hquartet :
      (symmetricQuartetLogDerivativeContribution m tau a
        (upperHalfPlanePoint x v)).im ≤ -1 := by
    rw [Complex.add_im] at him
    simp only [Complex.neg_im, Complex.I_im] at him
    linarith
  have hplusEnergy :
      -pairHyperbolicCost m a (symmetricQuartetRadiusPlus tau a x v) ≤
        pairImaginaryEnergy m (x - tau) v a := by
    exact pairImaginaryEnergy_ge_neg_hyperbolicCost hm ha hv hplus
  have hminusEnergy :
      -pairHyperbolicCost m a (symmetricQuartetRadiusMinus tau a x v) ≤
        pairImaginaryEnergy m (x + tau) v a := by
    exact pairImaginaryEnergy_ge_neg_hyperbolicCost hm ha hv hminus
  rw [symmetricQuartetLogDerivativeContribution_im ha hv hplus hminus]
    at hquartet
  linarith

/-- The sharp product-radius conclusion from the quartet pole equation. -/
theorem symmetricQuartet_radius_product_lt_threshold_of_pole
    {m tau a x v : ℝ} {background : ℂ}
    (hm : 0 < m) (ha : 0 < a) (hv : 0 < v)
    (hplus : 0 < pairHyperbolicUpperSq (x - tau) v a)
    (hminus : 0 < pairHyperbolicUpperSq (x + tau) v a)
    (hbackground : 0 ≤ background.im)
    (hpole : symmetricQuartetLogDerivativeContribution m tau a
        (upperHalfPlanePoint x v) + background = -Complex.I) :
    symmetricQuartetRadiusPlus tau a x v *
        symmetricQuartetRadiusMinus tau a x v <
      pairHyperbolicThreshold m a := by
  apply radius_mul_lt_pairHyperbolicThreshold_of_cost_sum hm ha
  · exact pairHyperbolicRadius_pos ha hv hplus
  · exact pairHyperbolicRadius_lt_one ha hv
  · exact pairHyperbolicRadius_pos ha hv hminus
  · exact pairHyperbolicRadius_lt_one ha hv
  · exact one_le_symmetricQuartet_cost_sum_of_pole hm.le ha hv
      hplus hminus hbackground hpole

/-! ## Identification with the symmetric degree-two Blaschke product -/

/-- Upper-half-plane Blaschke factor with zero `p`. -/
def upperHalfPlaneBlaschkeFactor (p z : ℂ) : ℂ :=
  (z - p) / (z - starRingEnd ℂ p)

/-- Product with symmetric zeros `x + I*v` and `-x + I*v`. -/
def symmetricTwoPointBlaschke (x v : ℝ) (z : ℂ) : ℂ :=
  upperHalfPlaneBlaschkeFactor (upperHalfPlanePoint x v) z *
    upperHalfPlaneBlaschkeFactor (upperHalfPlanePoint (-x) v) z

theorem norm_symmetricTwoPointBlaschke_at_quartetPlus
    (tau a x v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    ‖symmetricTwoPointBlaschke x v (upperHalfPlanePoint tau a)‖ =
      symmetricQuartetRadiusPlus tau a x v *
        symmetricQuartetRadiusMinus tau a x v := by
  unfold symmetricTwoPointBlaschke upperHalfPlaneBlaschkeFactor
  rw [norm_mul]
  change
    upperHalfPlanePseudoHyperbolicDistance
        (upperHalfPlanePoint tau a) (upperHalfPlanePoint x v) *
      upperHalfPlanePseudoHyperbolicDistance
        (upperHalfPlanePoint tau a) (upperHalfPlanePoint (-x) v) = _
  unfold upperHalfPlanePoint
  rw [upperHalfPlanePseudoHyperbolicDistance_eq_pairRadius x v tau a hv ha,
    upperHalfPlanePseudoHyperbolicDistance_eq_pairRadius (-x) v tau a hv ha]
  unfold symmetricQuartetRadiusPlus symmetricQuartetRadiusMinus
  have hfirst :
      pairHyperbolicRadius (tau - x) a v =
        pairHyperbolicRadius (x - tau) v a := by
    calc
      pairHyperbolicRadius (tau - x) a v =
          pairHyperbolicRadius (tau - x) v a :=
        pairHyperbolicRadius_swap_heights _ _ _
      _ = pairHyperbolicRadius (x - tau) v a := by
        rw [show tau - x = -(x - tau) by ring,
          pairHyperbolicRadius_neg]
  have hsecond :
      pairHyperbolicRadius (tau - -x) a v =
        pairHyperbolicRadius (x + tau) v a := by
    calc
      pairHyperbolicRadius (tau - -x) a v =
          pairHyperbolicRadius (tau - -x) v a :=
        pairHyperbolicRadius_swap_heights _ _ _
      _ = pairHyperbolicRadius (x + tau) v a := by
        congr 2
        ring
  rw [hfirst, hsecond]

/-- Direct Blaschke-modulus consequence of the pole equation, with no
restriction on the horizontal parameter `tau`. -/
theorem norm_symmetricTwoPointBlaschke_lt_threshold_of_pole
    {m tau a x v : ℝ} {background : ℂ}
    (hm : 0 < m) (ha : 0 < a) (hv : 0 < v)
    (hplus : 0 < pairHyperbolicUpperSq (x - tau) v a)
    (hminus : 0 < pairHyperbolicUpperSq (x + tau) v a)
    (hbackground : 0 ≤ background.im)
    (hpole : symmetricQuartetLogDerivativeContribution m tau a
        (upperHalfPlanePoint x v) + background = -Complex.I) :
    ‖symmetricTwoPointBlaschke x v (upperHalfPlanePoint tau a)‖ <
      pairHyperbolicThreshold m a := by
  rw [norm_symmetricTwoPointBlaschke_at_quartetPlus tau a x v ha hv]
  exact symmetricQuartet_radius_product_lt_threshold_of_pole hm ha hv
    hplus hminus hbackground hpole

end

end RiemannGaussian

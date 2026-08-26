import RiemannGaussian.TwoNodePickSchur

/-!
# Symmetric two-node Pick geometry

This file specializes the general two-node Schur complement to the symmetric
upper zeros `±tau + I*a` and symmetric candidate poles `±x + I*v`.
-/

namespace RiemannGaussian

noncomputable section

open scoped ComplexConjugate ComplexOrder

def symmetricPickAlphaPlus (tau a : ℝ) : ℂ :=
  upperHalfPlanePoint tau a

def symmetricPickAlphaMinus (tau a : ℝ) : ℂ :=
  upperHalfPlanePoint (-tau) a

def symmetricPickPole (x v : ℝ) : ℂ :=
  upperHalfPlanePoint x v

def symmetricPickBlaschke (x v : ℝ) : ℂ → ℂ :=
  symmetricTwoPointBlaschke x v

def symmetricPickBaseA (tau a x v : ℝ) : ℝ :=
  (1 - Complex.normSq
    (symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a))) / (2 * a)

def symmetricPickBaseD (tau a x v : ℝ) : ℝ :=
  (1 - Complex.normSq
    (symmetricPickBlaschke x v (symmetricPickAlphaMinus tau a))) / (2 * a)

def symmetricPickBaseC (tau a x v : ℝ) : ℂ :=
  upperHalfPlanePickKernel (symmetricPickBlaschke x v)
    (symmetricPickAlphaPlus tau a) (symmetricPickAlphaMinus tau a)

def symmetricPickH (v : ℝ) : ℝ := 1 / (2 * v)

def symmetricPickUPlus (tau a x v : ℝ) : ℂ :=
  Complex.I / (symmetricPickAlphaPlus tau a -
    starRingEnd ℂ (symmetricPickPole x v))

def symmetricPickUMinus (tau a x v : ℝ) : ℂ :=
  Complex.I / (symmetricPickAlphaMinus tau a -
    starRingEnd ℂ (symmetricPickPole x v))

def symmetricPickVPlus (tau a x v : ℝ) : ℂ :=
  symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a) *
    symmetricPickUPlus tau a x v

def symmetricPickVMinus (tau a x v : ℝ) : ℂ :=
  symmetricPickBlaschke x v (symmetricPickAlphaMinus tau a) *
    symmetricPickUMinus tau a x v

/-- The unimodular pole phase times the first Blaschke factor and the
conjugate of the second.  Its norm is the norm of the full symmetric
Blaschke product at the upper interpolation node. -/
def symmetricPickPhaseRatio (tau a x v : ℝ) : ℂ :=
  starRingEnd ℂ (symmetricPickPole x v) / symmetricPickPole x v *
    elementaryUpperHalfPlaneBlaschke (symmetricPickPole x v)
      (symmetricPickAlphaPlus tau a) *
    starRingEnd ℂ
      (elementaryUpperHalfPlaneBlaschke (symmetricPickPole (-x) v)
        (symmetricPickAlphaPlus tau a))

def symmetricPickNodes (tau a x v : ℝ) : Fin 3 → ℂ :=
  ![symmetricPickAlphaPlus tau a,
    symmetricPickAlphaMinus tau a,
    symmetricPickPole x v]

/-- Degree-two Blaschke product whose zeros are `p` and `-conj p`. -/
def conjugateSymmetricBlaschke (p z : ℂ) : ℂ :=
  elementaryUpperHalfPlaneBlaschke p z *
    elementaryUpperHalfPlaneBlaschke (-starRingEnd ℂ p) z

def conjugateSymmetricFeature0 (p z : ℂ) : ℂ :=
  elementaryPickFeature p z

def conjugateSymmetricFeature1 (p z : ℂ) : ℂ :=
  elementaryUpperHalfPlaneBlaschke p z *
    elementaryPickFeature (-starRingEnd ℂ p) z

def conjugateSymmetricPhase (p z : ℂ) : ℂ :=
  starRingEnd ℂ p / p * elementaryUpperHalfPlaneBlaschke p z *
    starRingEnd ℂ
      (elementaryUpperHalfPlaneBlaschke (-starRingEnd ℂ p) z)

@[simp] theorem neg_conj_symmetricPickPole (x v : ℝ) :
    -starRingEnd ℂ (symmetricPickPole x v) = symmetricPickPole (-x) v := by
  apply Complex.ext <;>
    simp [symmetricPickPole, upperHalfPlanePoint]

@[simp] theorem neg_conj_upperHalfPlanePoint (x v : ℝ) :
    -starRingEnd ℂ (upperHalfPlanePoint x v) =
      upperHalfPlanePoint (-x) v := by
  apply Complex.ext <;> simp [upperHalfPlanePoint]

@[simp] theorem neg_conj_symmetricPickAlphaPlus (tau a : ℝ) :
    -starRingEnd ℂ (symmetricPickAlphaPlus tau a) =
      symmetricPickAlphaMinus tau a := by
  apply Complex.ext <;>
    simp [symmetricPickAlphaPlus, symmetricPickAlphaMinus,
      upperHalfPlanePoint]

theorem upperHalfPlanePickKernel_conj_transpose
    (f : ℂ → ℂ) (z w : ℂ) :
    upperHalfPlanePickKernel f w z =
      starRingEnd ℂ (upperHalfPlanePickKernel f z w) := by
  unfold upperHalfPlanePickKernel
  simp only [map_div₀, map_mul, map_sub, Complex.conj_I]
  rw [show w - starRingEnd ℂ z =
      -(starRingEnd ℂ z - w) by ring, div_neg]
  rw [show starRingEnd ℂ (starRingEnd ℂ (f w)) = f w by simp]
  rw [show starRingEnd ℂ (starRingEnd ℂ w) = w by simp]
  rw [show starRingEnd ℂ (1 : ℂ) = 1 by simp]
  ring

theorem upperHalfPlanePickKernel_eq_of_neg_values
    {f B : ℂ → ℂ} {z w : ℂ}
    (hz : f z = -B z) (hw : f w = -B w) :
    upperHalfPlanePickKernel f z w = upperHalfPlanePickKernel B z w := by
  unfold upperHalfPlanePickKernel
  rw [hz, hw]
  simp only [map_neg, neg_mul, mul_neg, neg_neg]

theorem upperHalfPlanePickKernel_cross_of_neg_value
    {f B : ℂ → ℂ} {z p s : ℂ}
    (hz : f z = -B z) (hp : f p = s) :
    upperHalfPlanePickKernel f z p =
      normalizedPickCross
        (Complex.I / (z - starRingEnd ℂ p))
        (B z * (Complex.I / (z - starRingEnd ℂ p))) s := by
  unfold upperHalfPlanePickKernel normalizedPickCross
  rw [hz, hp]
  simp only [neg_mul]
  ring

theorem symmetricPickKernel_self_plus_eq_baseA
    {S : ℂ → ℂ} {tau a x v : ℝ} (ha : 0 < a)
    (hplus : S (symmetricPickAlphaPlus tau a) =
      -symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a)) :
    upperHalfPlanePickKernel S
        (symmetricPickAlphaPlus tau a) (symmetricPickAlphaPlus tau a) =
      (symmetricPickBaseA tau a x v : ℂ) := by
  rw [upperHalfPlanePickKernel_self S
    (by simpa [symmetricPickAlphaPlus, upperHalfPlanePoint] using ha)]
  rw [hplus, Complex.normSq_neg]
  simp [symmetricPickBaseA, symmetricPickAlphaPlus, upperHalfPlanePoint]

theorem symmetricPickKernel_self_minus_eq_baseD
    {S : ℂ → ℂ} {tau a x v : ℝ} (ha : 0 < a)
    (hminus : S (symmetricPickAlphaMinus tau a) =
      -symmetricPickBlaschke x v (symmetricPickAlphaMinus tau a)) :
    upperHalfPlanePickKernel S
        (symmetricPickAlphaMinus tau a) (symmetricPickAlphaMinus tau a) =
      (symmetricPickBaseD tau a x v : ℂ) := by
  rw [upperHalfPlanePickKernel_self S
    (by simpa [symmetricPickAlphaMinus, upperHalfPlanePoint] using ha)]
  rw [hminus, Complex.normSq_neg]
  simp [symmetricPickBaseD, symmetricPickAlphaMinus, upperHalfPlanePoint]

theorem symmetricPickKernel_self_pole_eq_h
    {S : ℂ → ℂ} {s : ℂ} {x v : ℝ} (hv : 0 < v)
    (hpole : S (symmetricPickPole x v) = s) :
    upperHalfPlanePickKernel S
        (symmetricPickPole x v) (symmetricPickPole x v) =
      ((symmetricPickH v * (1 - Complex.normSq s) : ℝ) : ℂ) := by
  rw [upperHalfPlanePickKernel_self S
    (by simpa [symmetricPickPole, upperHalfPlanePoint] using hv)]
  rw [hpole]
  simp only [symmetricPickPole, upperHalfPlanePoint, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_add, zero_mul, one_mul]
  congr 1
  unfold symmetricPickH
  field_simp [hv.ne']

theorem symmetricPickKernel_plus_minus_eq_baseC
    {S : ℂ → ℂ} {tau a x v : ℝ}
    (hplus : S (symmetricPickAlphaPlus tau a) =
      -symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a))
    (hminus : S (symmetricPickAlphaMinus tau a) =
      -symmetricPickBlaschke x v (symmetricPickAlphaMinus tau a)) :
    upperHalfPlanePickKernel S
        (symmetricPickAlphaPlus tau a) (symmetricPickAlphaMinus tau a) =
      symmetricPickBaseC tau a x v := by
  unfold symmetricPickBaseC
  exact upperHalfPlanePickKernel_eq_of_neg_values hplus hminus

theorem symmetricPickKernel_plus_pole_eq_cross
    {S : ℂ → ℂ} {s : ℂ} {tau a x v : ℝ}
    (hplus : S (symmetricPickAlphaPlus tau a) =
      -symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a))
    (hpole : S (symmetricPickPole x v) = s) :
    upperHalfPlanePickKernel S
        (symmetricPickAlphaPlus tau a) (symmetricPickPole x v) =
      normalizedPickCross
        (symmetricPickUPlus tau a x v)
        (symmetricPickVPlus tau a x v) s := by
  simpa [symmetricPickUPlus, symmetricPickVPlus] using
    (upperHalfPlanePickKernel_cross_of_neg_value hplus hpole)

theorem symmetricPickKernel_minus_pole_eq_cross
    {S : ℂ → ℂ} {s : ℂ} {tau a x v : ℝ}
    (hminus : S (symmetricPickAlphaMinus tau a) =
      -symmetricPickBlaschke x v (symmetricPickAlphaMinus tau a))
    (hpole : S (symmetricPickPole x v) = s) :
    upperHalfPlanePickKernel S
        (symmetricPickAlphaMinus tau a) (symmetricPickPole x v) =
      normalizedPickCross
        (symmetricPickUMinus tau a x v)
        (symmetricPickVMinus tau a x v) s := by
  simpa [symmetricPickUMinus, symmetricPickVMinus] using
    (upperHalfPlanePickKernel_cross_of_neg_value hminus hpole)

@[simp] theorem symmetricPickAlphaPlus_im (tau a : ℝ) :
    (symmetricPickAlphaPlus tau a).im = a := by
  simp [symmetricPickAlphaPlus, upperHalfPlanePoint]

@[simp] theorem symmetricPickAlphaMinus_im (tau a : ℝ) :
    (symmetricPickAlphaMinus tau a).im = a := by
  simp [symmetricPickAlphaMinus, upperHalfPlanePoint]

@[simp] theorem symmetricPickPole_im (x v : ℝ) :
    (symmetricPickPole x v).im = v := by
  simp [symmetricPickPole, upperHalfPlanePoint]

theorem symmetricPickBlaschke_minus_eq_conj_plus
    (tau a x v : ℝ) :
    symmetricPickBlaschke x v (symmetricPickAlphaMinus tau a) =
      starRingEnd ℂ
        (symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a)) := by
  apply Complex.ext <;>
    simp [symmetricPickBlaschke, symmetricPickAlphaMinus,
      symmetricPickAlphaPlus, symmetricTwoPointBlaschke,
      upperHalfPlaneBlaschkeFactor, upperHalfPlanePoint,
      Complex.div_re, Complex.div_im, Complex.normSq_apply]
  <;> ring

theorem symmetricPickBaseD_eq_A (tau a x v : ℝ) :
    symmetricPickBaseD tau a x v = symmetricPickBaseA tau a x v := by
  unfold symmetricPickBaseD symmetricPickBaseA
  rw [symmetricPickBlaschke_minus_eq_conj_plus]
  rw [Complex.normSq_conj]

/-- First feature in the rank-two Gram representation of the symmetric
degree-two Blaschke Pick kernel. -/
def symmetricPickFeature0 (x v : ℝ) (z : ℂ) : ℂ :=
  elementaryPickFeature (symmetricPickPole x v) z

/-- Second feature in the rank-two Gram representation of the symmetric
degree-two Blaschke Pick kernel. -/
def symmetricPickFeature1 (x v : ℝ) (z : ℂ) : ℂ :=
  elementaryUpperHalfPlaneBlaschke (symmetricPickPole x v) z *
    elementaryPickFeature (symmetricPickPole (-x) v) z

theorem symmetricPickKernel_eq_feature_sum
    {x v : ℝ} {z w : ℂ} (hv : 0 < v)
    (hz : 0 < z.im) (hw : 0 < w.im) :
    upperHalfPlanePickKernel (symmetricPickBlaschke x v) z w =
      symmetricPickFeature0 x v z *
          starRingEnd ℂ (symmetricPickFeature0 x v w) +
        symmetricPickFeature1 x v z *
          starRingEnd ℂ (symmetricPickFeature1 x v w) := by
  unfold symmetricPickBlaschke symmetricTwoPointBlaschke
  change upperHalfPlanePickKernel
      (fun u =>
        elementaryUpperHalfPlaneBlaschke (symmetricPickPole x v) u *
          elementaryUpperHalfPlaneBlaschke (symmetricPickPole (-x) v) u)
      z w = _
  rw [upperHalfPlanePickKernel_mul]
  rw [upperHalfPlanePickKernel_elementary_eq_feature_mul_conj
      (by simpa using hv) hz hw]
  rw [upperHalfPlanePickKernel_elementary_eq_feature_mul_conj
      (by simpa using hv) hz hw]
  unfold symmetricPickFeature0 symmetricPickFeature1
  simp only [map_mul]
  ring

/-- The two-dimensional complex Lagrange identity. -/
theorem two_feature_gram_det (a b c d : ℂ) :
    (Complex.normSq a + Complex.normSq b) *
          (Complex.normSq c + Complex.normSq d) -
        Complex.normSq
          (a * starRingEnd ℂ c + b * starRingEnd ℂ d) =
      Complex.normSq (a * d - b * c) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem twoHermitianAdjugateNorm_first_feature
    (a b c d k : ℂ) :
    twoHermitianAdjugateNorm
        (Complex.normSq a + Complex.normSq b)
        (Complex.normSq c + Complex.normSq d)
        (a * starRingEnd ℂ c + b * starRingEnd ℂ d)
        (k * a) (k * c) =
      Complex.normSq k * Complex.normSq (a * d - b * c) := by
  simp [twoHermitianAdjugateNorm, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

theorem twoHermitianInvNorm_first_feature
    {a b c d k : ℂ} (hwedge : a * d - b * c ≠ 0) :
    twoHermitianInvNorm
        (Complex.normSq a + Complex.normSq b)
        (Complex.normSq c + Complex.normSq d)
        (a * starRingEnd ℂ c + b * starRingEnd ℂ d)
        (k * a) (k * c) =
      Complex.normSq k := by
  unfold twoHermitianInvNorm
  rw [twoHermitianAdjugateNorm_first_feature]
  rw [show twoHermitianDet
      (Complex.normSq a + Complex.normSq b)
      (Complex.normSq c + Complex.normSq d)
      (a * starRingEnd ℂ c + b * starRingEnd ℂ d) =
        Complex.normSq (a * d - b * c) by
    unfold twoHermitianDet
    exact two_feature_gram_det a b c d]
  field_simp [(Complex.normSq_pos.mpr hwedge).ne']

theorem twoHermitianInvForm_first_feature
    {a b c d k v₀ v₁ : ℂ} (hwedge : a * d - b * c ≠ 0) :
    twoHermitianInvForm
        (Complex.normSq a + Complex.normSq b)
        (Complex.normSq c + Complex.normSq d)
        (a * starRingEnd ℂ c + b * starRingEnd ℂ d)
        v₀ v₁ (k * a) (k * c) =
      k * starRingEnd ℂ ((v₀ * d - v₁ * b) / (a * d - b * c)) := by
  unfold twoHermitianInvForm
  rw [show twoHermitianDet
      (Complex.normSq a + Complex.normSq b)
      (Complex.normSq c + Complex.normSq d)
      (a * starRingEnd ℂ c + b * starRingEnd ℂ d) =
        Complex.normSq (a * d - b * c) by
    unfold twoHermitianDet
    exact two_feature_gram_det a b c d]
  have hnum :
      ((Complex.normSq c + Complex.normSq d : ℝ) : ℂ) *
            starRingEnd ℂ v₀ * (k * a) -
          (a * starRingEnd ℂ c + b * starRingEnd ℂ d) *
            starRingEnd ℂ v₀ * (k * c) -
          starRingEnd ℂ (a * starRingEnd ℂ c + b * starRingEnd ℂ d) *
            starRingEnd ℂ v₁ * (k * a) +
          ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) *
            starRingEnd ℂ v₁ * (k * c) =
        k * (a * d - b * c) * starRingEnd ℂ (v₀ * d - v₁ * b) := by
    push_cast
    simp only [Complex.normSq_eq_conj_mul_self, map_add, map_sub, map_mul,
      starRingEnd_apply, star_star]
    ring
  rw [hnum]
  rw [show (Complex.normSq (a * d - b * c) : ℂ) =
      starRingEnd ℂ (a * d - b * c) * (a * d - b * c) by
    exact Complex.normSq_eq_conj_mul_self]
  simp only [map_sub, map_mul, map_div₀]
  have hwedgeStar : starRingEnd ℂ (a * d - b * c) ≠ 0 :=
    star_ne_zero.mpr hwedge
  field_simp [hwedge, hwedgeStar]

theorem symmetricPickBaseA_eq_feature_normSq_sum
    {tau a x v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    symmetricPickBaseA tau a x v =
      Complex.normSq
          (symmetricPickFeature0 x v (symmetricPickAlphaPlus tau a)) +
        Complex.normSq
          (symmetricPickFeature1 x v (symmetricPickAlphaPlus tau a)) := by
  have hself := upperHalfPlanePickKernel_self
    (symmetricPickBlaschke x v)
    (z := symmetricPickAlphaPlus tau a) (by simpa using ha)
  have hfeatures := symmetricPickKernel_eq_feature_sum
    (x := x) (v := v) (z := symmetricPickAlphaPlus tau a)
    (w := symmetricPickAlphaPlus tau a) hv
    (by simpa using ha) (by simpa using ha)
  have hcast :
      (symmetricPickBaseA tau a x v : ℂ) =
        ((Complex.normSq
              (symmetricPickFeature0 x v (symmetricPickAlphaPlus tau a)) +
            Complex.normSq
              (symmetricPickFeature1 x v
                (symmetricPickAlphaPlus tau a)) : ℝ) : ℂ) := by
    calc
      (symmetricPickBaseA tau a x v : ℂ) =
          upperHalfPlanePickKernel (symmetricPickBlaschke x v)
            (symmetricPickAlphaPlus tau a)
            (symmetricPickAlphaPlus tau a) := by
        rw [hself]
        simp [symmetricPickBaseA]
      _ = _ := by
        rw [hfeatures]
        rw [show symmetricPickFeature0 x v (symmetricPickAlphaPlus tau a) *
              starRingEnd ℂ
                (symmetricPickFeature0 x v (symmetricPickAlphaPlus tau a)) =
              (Complex.normSq
                (symmetricPickFeature0 x v
                  (symmetricPickAlphaPlus tau a)) : ℂ) by
            rw [mul_comm, Complex.normSq_eq_conj_mul_self]]
        rw [show symmetricPickFeature1 x v (symmetricPickAlphaPlus tau a) *
              starRingEnd ℂ
                (symmetricPickFeature1 x v (symmetricPickAlphaPlus tau a)) =
              (Complex.normSq
                (symmetricPickFeature1 x v
                  (symmetricPickAlphaPlus tau a)) : ℂ) by
            rw [mul_comm, Complex.normSq_eq_conj_mul_self]]
        norm_cast
  exact_mod_cast hcast

theorem symmetricPickBaseD_eq_feature_normSq_sum
    {tau a x v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    symmetricPickBaseD tau a x v =
      Complex.normSq
          (symmetricPickFeature0 x v (symmetricPickAlphaMinus tau a)) +
        Complex.normSq
          (symmetricPickFeature1 x v (symmetricPickAlphaMinus tau a)) := by
  have hself := upperHalfPlanePickKernel_self
    (symmetricPickBlaschke x v)
    (z := symmetricPickAlphaMinus tau a) (by simpa using ha)
  have hfeatures := symmetricPickKernel_eq_feature_sum
    (x := x) (v := v) (z := symmetricPickAlphaMinus tau a)
    (w := symmetricPickAlphaMinus tau a) hv
    (by simpa using ha) (by simpa using ha)
  have hcast :
      (symmetricPickBaseD tau a x v : ℂ) =
        ((Complex.normSq
              (symmetricPickFeature0 x v (symmetricPickAlphaMinus tau a)) +
            Complex.normSq
              (symmetricPickFeature1 x v
                (symmetricPickAlphaMinus tau a)) : ℝ) : ℂ) := by
    calc
      (symmetricPickBaseD tau a x v : ℂ) =
          upperHalfPlanePickKernel (symmetricPickBlaschke x v)
            (symmetricPickAlphaMinus tau a)
            (symmetricPickAlphaMinus tau a) := by
        rw [hself]
        simp [symmetricPickBaseD]
      _ = _ := by
        rw [hfeatures]
        rw [show symmetricPickFeature0 x v (symmetricPickAlphaMinus tau a) *
              starRingEnd ℂ
                (symmetricPickFeature0 x v (symmetricPickAlphaMinus tau a)) =
              (Complex.normSq
                (symmetricPickFeature0 x v
                  (symmetricPickAlphaMinus tau a)) : ℂ) by
            rw [mul_comm, Complex.normSq_eq_conj_mul_self]]
        rw [show symmetricPickFeature1 x v (symmetricPickAlphaMinus tau a) *
              starRingEnd ℂ
                (symmetricPickFeature1 x v (symmetricPickAlphaMinus tau a)) =
              (Complex.normSq
                (symmetricPickFeature1 x v
                  (symmetricPickAlphaMinus tau a)) : ℂ) by
            rw [mul_comm, Complex.normSq_eq_conj_mul_self]]
        norm_cast
  exact_mod_cast hcast

theorem symmetricPickBase_det_eq_feature_normSq
    {tau a x v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    twoHermitianDet
        (symmetricPickBaseA tau a x v)
        (symmetricPickBaseD tau a x v)
        (symmetricPickBaseC tau a x v) =
      Complex.normSq
        (symmetricPickFeature0 x v (symmetricPickAlphaPlus tau a) *
            symmetricPickFeature1 x v (symmetricPickAlphaMinus tau a) -
          symmetricPickFeature1 x v (symmetricPickAlphaPlus tau a) *
            symmetricPickFeature0 x v (symmetricPickAlphaMinus tau a)) := by
  rw [symmetricPickBaseA_eq_feature_normSq_sum ha hv,
    symmetricPickBaseD_eq_feature_normSq_sum ha hv]
  unfold symmetricPickBaseC twoHermitianDet
  rw [symmetricPickKernel_eq_feature_sum hv
    (by simpa using ha) (by simpa using ha)]
  exact two_feature_gram_det _ _ _ _

theorem symmetricPickFeature_det_formula
    {tau a x v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    symmetricPickFeature0 x v (symmetricPickAlphaPlus tau a) *
          symmetricPickFeature1 x v (symmetricPickAlphaMinus tau a) -
        symmetricPickFeature1 x v (symmetricPickAlphaPlus tau a) *
          symmetricPickFeature0 x v (symmetricPickAlphaMinus tau a) =
      (2 * v : ℂ) *
          ((symmetricPickAlphaPlus tau a - symmetricPickAlphaMinus tau a) *
            (starRingEnd ℂ (symmetricPickPole (-x) v) -
              symmetricPickPole x v)) /
        ((symmetricPickAlphaPlus tau a -
              starRingEnd ℂ (symmetricPickPole x v)) *
          (symmetricPickAlphaMinus tau a -
              starRingEnd ℂ (symmetricPickPole x v)) *
          (symmetricPickAlphaPlus tau a -
              starRingEnd ℂ (symmetricPickPole (-x) v)) *
          (symmetricPickAlphaMinus tau a -
              starRingEnd ℂ (symmetricPickPole (-x) v))) := by
  have hpPlus : symmetricPickAlphaPlus tau a -
      starRingEnd ℂ (symmetricPickPole x v) ≠ 0 :=
    sub_conj_ne_zero_of_im_pos (by simpa using ha) (by simpa using hv)
  have hpMinus : symmetricPickAlphaMinus tau a -
      starRingEnd ℂ (symmetricPickPole x v) ≠ 0 :=
    sub_conj_ne_zero_of_im_pos (by simpa using ha) (by simpa using hv)
  have hqPlus : symmetricPickAlphaPlus tau a -
      starRingEnd ℂ (symmetricPickPole (-x) v) ≠ 0 :=
    sub_conj_ne_zero_of_im_pos (by simpa using ha) (by simpa using hv)
  have hqMinus : symmetricPickAlphaMinus tau a -
      starRingEnd ℂ (symmetricPickPole (-x) v) ≠ 0 :=
    sub_conj_ne_zero_of_im_pos (by simpa using ha) (by simpa using hv)
  have hsqrt : (Real.sqrt (2 * v) : ℂ) ^ 2 = (2 * v : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ 2 * v)
  unfold symmetricPickFeature0 symmetricPickFeature1
    elementaryPickFeature elementaryUpperHalfPlaneBlaschke
  simp only [symmetricPickPole_im]
  field_simp [hpPlus, hpMinus, hqPlus, hqMinus]
  rw [hsqrt]
  ring

theorem symmetricPickFeature_det_ne_zero
    {tau a x v : ℝ} (htau : tau ≠ 0) (ha : 0 < a) (hv : 0 < v) :
    symmetricPickFeature0 x v (symmetricPickAlphaPlus tau a) *
          symmetricPickFeature1 x v (symmetricPickAlphaMinus tau a) -
        symmetricPickFeature1 x v (symmetricPickAlphaPlus tau a) *
          symmetricPickFeature0 x v (symmetricPickAlphaMinus tau a) ≠ 0 := by
  rw [symmetricPickFeature_det_formula ha hv]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hv.ne')
    · apply mul_ne_zero
      · intro h
        apply htau
        have hre := congrArg Complex.re h
        simp [symmetricPickAlphaPlus, symmetricPickAlphaMinus,
          upperHalfPlanePoint] at hre
        linarith
      · intro h
        have him := congrArg Complex.im h
        simp [symmetricPickPole, upperHalfPlanePoint] at him
        linarith
  · exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (sub_conj_ne_zero_of_im_pos (by simpa using ha) (by simpa using hv))
          (sub_conj_ne_zero_of_im_pos (by simpa using ha) (by simpa using hv)))
        (sub_conj_ne_zero_of_im_pos (by simpa using ha) (by simpa using hv)))
      (sub_conj_ne_zero_of_im_pos (by simpa using ha) (by simpa using hv))

theorem symmetricPickUPlus_eq_scaled_feature0
    {tau a x v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    symmetricPickUPlus tau a x v =
      (Complex.I / (Real.sqrt (2 * v) : ℂ)) *
        symmetricPickFeature0 x v (symmetricPickAlphaPlus tau a) := by
  have hsqrt : Real.sqrt (2 * v) ≠ 0 := by positivity
  have hden : symmetricPickAlphaPlus tau a -
      starRingEnd ℂ (symmetricPickPole x v) ≠ 0 :=
    sub_conj_ne_zero_of_im_pos (by simpa using ha) (by simpa using hv)
  unfold symmetricPickUPlus symmetricPickFeature0 elementaryPickFeature
  simp only [symmetricPickPole_im]
  field_simp [hsqrt, hden]

theorem symmetricPickUMinus_eq_scaled_feature0
    {tau a x v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    symmetricPickUMinus tau a x v =
      (Complex.I / (Real.sqrt (2 * v) : ℂ)) *
        symmetricPickFeature0 x v (symmetricPickAlphaMinus tau a) := by
  have hsqrt : Real.sqrt (2 * v) ≠ 0 := by positivity
  have hden : symmetricPickAlphaMinus tau a -
      starRingEnd ℂ (symmetricPickPole x v) ≠ 0 :=
    sub_conj_ne_zero_of_im_pos (by simpa using ha) (by simpa using hv)
  unfold symmetricPickUMinus symmetricPickFeature0 elementaryPickFeature
  simp only [symmetricPickPole_im]
  field_simp [hsqrt, hden]

theorem normSq_I_div_sqrt_two_mul
    {v : ℝ} (hv : 0 < v) :
    Complex.normSq (Complex.I / (Real.sqrt (2 * v) : ℂ)) =
      1 / (2 * v) := by
  rw [Complex.normSq_div, Complex.normSq_I, Complex.normSq_ofReal]
  have hsqrt : Real.sqrt (2 * v) ^ 2 = 2 * v :=
    Real.sq_sqrt (by positivity)
  rw [show Real.sqrt (2 * v) * Real.sqrt (2 * v) = 2 * v by
    simpa [pow_two] using hsqrt]

theorem symmetricPickInvNorm_u_eq_h
    {tau a x v : ℝ} (htau : tau ≠ 0) (ha : 0 < a) (hv : 0 < v) :
    twoHermitianInvNorm
        (symmetricPickBaseA tau a x v)
        (symmetricPickBaseD tau a x v)
        (symmetricPickBaseC tau a x v)
        (symmetricPickUPlus tau a x v)
        (symmetricPickUMinus tau a x v) =
      symmetricPickH v := by
  rw [symmetricPickBaseA_eq_feature_normSq_sum ha hv,
    symmetricPickBaseD_eq_feature_normSq_sum ha hv]
  unfold symmetricPickBaseC
  rw [symmetricPickKernel_eq_feature_sum hv
    (by simpa using ha) (by simpa using ha)]
  rw [symmetricPickUPlus_eq_scaled_feature0 ha hv,
    symmetricPickUMinus_eq_scaled_feature0 ha hv]
  rw [twoHermitianInvNorm_first_feature
    (symmetricPickFeature_det_ne_zero htau ha hv)]
  exact normSq_I_div_sqrt_two_mul hv

theorem symmetricPickInvForm_v_u_eq_feature_ratio
    {tau a x v : ℝ} (htau : tau ≠ 0) (ha : 0 < a) (hv : 0 < v) :
    twoHermitianInvForm
        (symmetricPickBaseA tau a x v)
        (symmetricPickBaseD tau a x v)
        (symmetricPickBaseC tau a x v)
        (symmetricPickVPlus tau a x v)
        (symmetricPickVMinus tau a x v)
        (symmetricPickUPlus tau a x v)
        (symmetricPickUMinus tau a x v) =
      (Complex.I / (Real.sqrt (2 * v) : ℂ)) *
        starRingEnd ℂ
          ((symmetricPickVPlus tau a x v *
                symmetricPickFeature1 x v (symmetricPickAlphaMinus tau a) -
              symmetricPickVMinus tau a x v *
                symmetricPickFeature1 x v (symmetricPickAlphaPlus tau a)) /
            (symmetricPickFeature0 x v (symmetricPickAlphaPlus tau a) *
                symmetricPickFeature1 x v
                  (symmetricPickAlphaMinus tau a) -
              symmetricPickFeature1 x v (symmetricPickAlphaPlus tau a) *
                symmetricPickFeature0 x v
                  (symmetricPickAlphaMinus tau a))) := by
  rw [symmetricPickBaseA_eq_feature_normSq_sum ha hv,
    symmetricPickBaseD_eq_feature_normSq_sum ha hv]
  unfold symmetricPickBaseC
  rw [symmetricPickKernel_eq_feature_sum hv
    (by simpa using ha) (by simpa using ha)]
  rw [symmetricPickUPlus_eq_scaled_feature0 ha hv,
    symmetricPickUMinus_eq_scaled_feature0 ha hv]
  exact twoHermitianInvForm_first_feature
    (symmetricPickFeature_det_ne_zero htau ha hv)

theorem norm_symmetricPickPhaseRatio
    {tau a x v : ℝ} (hv : 0 < v) :
    ‖symmetricPickPhaseRatio tau a x v‖ =
      ‖symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a)‖ := by
  have hp : symmetricPickPole x v ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    simpa using hv.ne' him
  have hnormp : ‖symmetricPickPole x v‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hp
  unfold symmetricPickPhaseRatio
  rw [norm_mul, norm_mul, norm_div, Complex.norm_conj,
    Complex.norm_conj, div_self hnormp, one_mul]
  unfold symmetricPickBlaschke symmetricTwoPointBlaschke
    upperHalfPlaneBlaschkeFactor elementaryUpperHalfPlaneBlaschke
  rw [norm_mul]
  simp only [symmetricPickPole]

theorem symmetricPickVPlus_eq_scaled_feature0
    {tau a x v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    symmetricPickVPlus tau a x v =
      symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a) *
        (Complex.I / (Real.sqrt (2 * v) : ℂ)) *
        symmetricPickFeature0 x v (symmetricPickAlphaPlus tau a) := by
  unfold symmetricPickVPlus
  rw [symmetricPickUPlus_eq_scaled_feature0 ha hv]
  ring

theorem symmetricPickVMinus_eq_scaled_feature0
    {tau a x v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    symmetricPickVMinus tau a x v =
      symmetricPickBlaschke x v (symmetricPickAlphaMinus tau a) *
        (Complex.I / (Real.sqrt (2 * v) : ℂ)) *
        symmetricPickFeature0 x v (symmetricPickAlphaMinus tau a) := by
  unfold symmetricPickVMinus
  rw [symmetricPickUMinus_eq_scaled_feature0 ha hv]
  ring

theorem elementaryBlaschke_neg_conj
    (p z : ℂ) :
    elementaryUpperHalfPlaneBlaschke p (-starRingEnd ℂ z) =
      starRingEnd ℂ
        (elementaryUpperHalfPlaneBlaschke (-starRingEnd ℂ p) z) := by
  unfold elementaryUpperHalfPlaneBlaschke
  simp [map_div₀, map_neg]
  rw [show -starRingEnd ℂ z - p =
      -(starRingEnd ℂ z + p) by ring]
  rw [show -starRingEnd ℂ z - starRingEnd ℂ p =
      -(starRingEnd ℂ z + starRingEnd ℂ p) by ring]
  rw [neg_div_neg_eq]

theorem elementaryFeature_neg_conj
    (p z : ℂ) :
    elementaryPickFeature p (-starRingEnd ℂ z) =
      -starRingEnd ℂ (elementaryPickFeature (-starRingEnd ℂ p) z) := by
  have him : (-starRingEnd ℂ p).im = p.im := by simp
  unfold elementaryPickFeature
  rw [him]
  simp [map_div₀, map_neg]
  rw [show -starRingEnd ℂ z - starRingEnd ℂ p =
      -(starRingEnd ℂ z + starRingEnd ℂ p) by ring]
  rw [div_neg]

/-- The small rational identity remaining after reflected values have been
paired.  This is the algebraic core of the mixed Schur coefficient. -/
theorem conjugateSymmetric_core_identity
    {p z : ℂ} (hpim : 0 < p.im) (hzim : 0 < z.im) :
    -elementaryUpperHalfPlaneBlaschke (-starRingEnd ℂ p) z *
          (Complex.normSq (elementaryPickFeature p z) : ℂ) +
        starRingEnd ℂ (elementaryUpperHalfPlaneBlaschke p z) *
          (Complex.normSq
            (elementaryPickFeature (-starRingEnd ℂ p) z) : ℂ) =
      starRingEnd ℂ p / p *
        (-starRingEnd ℂ
              (elementaryUpperHalfPlaneBlaschke (-starRingEnd ℂ p) z) *
            (Complex.normSq (elementaryPickFeature p z) : ℂ) +
          elementaryUpperHalfPlaneBlaschke p z *
            (Complex.normSq
              (elementaryPickFeature (-starRingEnd ℂ p) z) : ℂ)) := by
  have hp : p ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hqim : 0 < (-starRingEnd ℂ p).im := by simpa
  have hzp := sub_conj_ne_zero_of_im_pos hzim hpim
  have hzq := sub_conj_ne_zero_of_im_pos hzim hqim
  have hzpStar : starRingEnd ℂ (z - starRingEnd ℂ p) ≠ 0 :=
    star_ne_zero.mpr hzp
  have hzqStar : starRingEnd ℂ
      (z - starRingEnd ℂ (-starRingEnd ℂ p)) ≠ 0 :=
    star_ne_zero.mpr hzq
  have hzPlusP : z + p ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hstarZMinusP : star z - p ≠ 0 := by
    simpa only [starRingEnd_apply, star_sub, star_star] using hzpStar
  have hstarSum : star z + star p ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hstarSum' : star p + star z ≠ 0 := by
    simpa [add_comm] using hstarSum
  unfold elementaryUpperHalfPlaneBlaschke elementaryPickFeature
  rw [show (Complex.normSq
      ((Real.sqrt (2 * p.im) : ℂ) / (z - starRingEnd ℂ p)) : ℂ) =
        starRingEnd ℂ
            ((Real.sqrt (2 * p.im) : ℂ) /
              (z - starRingEnd ℂ p)) *
          ((Real.sqrt (2 * p.im) : ℂ) /
            (z - starRingEnd ℂ p)) by
    exact Complex.normSq_eq_conj_mul_self]
  rw [show (Complex.normSq
      ((Real.sqrt (2 * (-starRingEnd ℂ p).im) : ℂ) /
        (z - starRingEnd ℂ (-starRingEnd ℂ p))) : ℂ) =
        starRingEnd ℂ
            ((Real.sqrt (2 * (-starRingEnd ℂ p).im) : ℂ) /
              (z - starRingEnd ℂ (-starRingEnd ℂ p))) *
          ((Real.sqrt (2 * (-starRingEnd ℂ p).im) : ℂ) /
            (z - starRingEnd ℂ (-starRingEnd ℂ p))) by
    exact Complex.normSq_eq_conj_mul_self]
  simp only [Complex.neg_im, Complex.conj_im, neg_neg]
  simp only [map_div₀, map_sub, map_neg, Complex.conj_ofReal]
  simp only [starRingEnd_apply, star_star]
  field_simp [hp, hzp, hzq, hzpStar, hzqStar, hzPlusP,
    hstarZMinusP, hstarSum, hstarSum']
  have hcancel :
      (star p + star z) * (star p + star z)⁻¹ = 1 :=
    mul_inv_cancel₀ hstarSum'
  linear_combination (p * (star p + z)) * hcancel

/-- The mixed-coordinate identity behind the symmetric two-node Schur
coefficient.  It is proved once over `ℂ`, before introducing real coordinates
for the two reflected pairs. -/
theorem conjugateSymmetric_mixed_identity
    {p z k : ℂ} (hpim : 0 < p.im) (hzim : 0 < z.im) :
    conjugateSymmetricBlaschke p z * k *
            conjugateSymmetricFeature0 p z *
            conjugateSymmetricFeature1 p (-starRingEnd ℂ z) -
          conjugateSymmetricBlaschke p (-starRingEnd ℂ z) * k *
            conjugateSymmetricFeature0 p (-starRingEnd ℂ z) *
            conjugateSymmetricFeature1 p z =
      k * conjugateSymmetricPhase p z *
        (conjugateSymmetricFeature0 p z *
              conjugateSymmetricFeature1 p (-starRingEnd ℂ z) -
            conjugateSymmetricFeature1 p z *
              conjugateSymmetricFeature0 p (-starRingEnd ℂ z)) := by
  let P := elementaryUpperHalfPlaneBlaschke p z
  let Q := elementaryUpperHalfPlaneBlaschke (-starRingEnd ℂ p) z
  let A := elementaryPickFeature p z
  let G := elementaryPickFeature (-starRingEnd ℂ p) z
  have hpw : elementaryUpperHalfPlaneBlaschke p (-starRingEnd ℂ z) =
      starRingEnd ℂ Q := by
    simpa [Q] using elementaryBlaschke_neg_conj p z
  have hqw : elementaryUpperHalfPlaneBlaschke (-starRingEnd ℂ p)
      (-starRingEnd ℂ z) = starRingEnd ℂ P := by
    simpa [P] using
      elementaryBlaschke_neg_conj (-starRingEnd ℂ p) z
  have hAw : elementaryPickFeature p (-starRingEnd ℂ z) =
      -starRingEnd ℂ G := by
    simpa [G] using elementaryFeature_neg_conj p z
  have hGw : elementaryPickFeature (-starRingEnd ℂ p)
      (-starRingEnd ℂ z) = -starRingEnd ℂ A := by
    simpa [A] using
      elementaryFeature_neg_conj (-starRingEnd ℂ p) z
  have hcore := conjugateSymmetric_core_identity hpim hzim
  change -Q * (Complex.normSq A : ℂ) +
      starRingEnd ℂ P * (Complex.normSq G : ℂ) =
    starRingEnd ℂ p / p *
      (-starRingEnd ℂ Q * (Complex.normSq A : ℂ) +
        P * (Complex.normSq G : ℂ)) at hcore
  simp only [Complex.normSq_eq_conj_mul_self] at hcore
  unfold conjugateSymmetricBlaschke conjugateSymmetricFeature0
    conjugateSymmetricFeature1 conjugateSymmetricPhase
  rw [hpw, hqw, hAw, hGw]
  change
    (P * Q) * k * A * (starRingEnd ℂ Q * -starRingEnd ℂ A) -
        (starRingEnd ℂ Q * starRingEnd ℂ P) * k *
          (-starRingEnd ℂ G) * (P * G) =
      k * (starRingEnd ℂ p / p * P * starRingEnd ℂ Q) *
        (A * (starRingEnd ℂ Q * -starRingEnd ℂ A) -
          (P * G) * -starRingEnd ℂ G)
  calc
    (P * Q) * k * A * (starRingEnd ℂ Q * -starRingEnd ℂ A) -
          (starRingEnd ℂ Q * starRingEnd ℂ P) * k *
            (-starRingEnd ℂ G) * (P * G) =
        k * P * starRingEnd ℂ Q *
          (-Q * (starRingEnd ℂ A * A) +
            starRingEnd ℂ P * (starRingEnd ℂ G * G)) := by ring
    _ = k * P * starRingEnd ℂ Q *
        (starRingEnd ℂ p / p *
          (-starRingEnd ℂ Q * (starRingEnd ℂ A * A) +
            P * (starRingEnd ℂ G * G))) := by rw [hcore]
    _ = k * (starRingEnd ℂ p / p * P * starRingEnd ℂ Q) *
        (A * (starRingEnd ℂ Q * -starRingEnd ℂ A) -
          (P * G) * -starRingEnd ℂ G) := by ring

theorem symmetricPickMixedRatio_eq_scaled_phase
    {tau a x v : ℝ} (htau : tau ≠ 0) (ha : 0 < a) (hv : 0 < v) :
    (symmetricPickVPlus tau a x v *
            symmetricPickFeature1 x v (symmetricPickAlphaMinus tau a) -
          symmetricPickVMinus tau a x v *
            symmetricPickFeature1 x v (symmetricPickAlphaPlus tau a)) /
        (symmetricPickFeature0 x v (symmetricPickAlphaPlus tau a) *
            symmetricPickFeature1 x v (symmetricPickAlphaMinus tau a) -
          symmetricPickFeature1 x v (symmetricPickAlphaPlus tau a) *
            symmetricPickFeature0 x v (symmetricPickAlphaMinus tau a)) =
      (Complex.I / (Real.sqrt (2 * v) : ℂ)) *
        symmetricPickPhaseRatio tau a x v := by
  rw [div_eq_iff (symmetricPickFeature_det_ne_zero htau ha hv)]
  rw [symmetricPickVPlus_eq_scaled_feature0 ha hv,
    symmetricPickVMinus_eq_scaled_feature0 ha hv]
  simpa [conjugateSymmetricBlaschke, conjugateSymmetricFeature0,
    conjugateSymmetricFeature1, conjugateSymmetricPhase,
    symmetricPickBlaschke, symmetricTwoPointBlaschke,
    upperHalfPlaneBlaschkeFactor, symmetricPickFeature0,
    symmetricPickFeature1, symmetricPickPhaseRatio,
    symmetricPickPole, elementaryUpperHalfPlaneBlaschke] using
      (conjugateSymmetric_mixed_identity
        (p := symmetricPickPole x v)
        (z := symmetricPickAlphaPlus tau a)
        (k := Complex.I / (Real.sqrt (2 * v) : ℂ))
        (by simpa using hv) (by simpa using ha))

theorem symmetricPickInvForm_v_u_eq_h_mul_conj_phase
    {tau a x v : ℝ} (htau : tau ≠ 0) (ha : 0 < a) (hv : 0 < v) :
    twoHermitianInvForm
        (symmetricPickBaseA tau a x v)
        (symmetricPickBaseD tau a x v)
        (symmetricPickBaseC tau a x v)
        (symmetricPickVPlus tau a x v)
        (symmetricPickVMinus tau a x v)
        (symmetricPickUPlus tau a x v)
        (symmetricPickUMinus tau a x v) =
      (symmetricPickH v : ℂ) *
        starRingEnd ℂ (symmetricPickPhaseRatio tau a x v) := by
  rw [symmetricPickInvForm_v_u_eq_feature_ratio htau ha hv]
  rw [symmetricPickMixedRatio_eq_scaled_phase htau ha hv]
  simp only [map_mul]
  rw [← mul_assoc]
  rw [show Complex.I / (Real.sqrt (2 * v) : ℂ) *
          starRingEnd ℂ (Complex.I / (Real.sqrt (2 * v) : ℂ)) =
        (Complex.normSq
          (Complex.I / (Real.sqrt (2 * v) : ℂ)) : ℂ) by
    rw [mul_comm, Complex.normSq_eq_conj_mul_self]]
  rw [normSq_I_div_sqrt_two_mul hv]
  rfl

theorem norm_symmetricPickInvForm_v_u
    {tau a x v : ℝ} (htau : tau ≠ 0) (ha : 0 < a) (hv : 0 < v) :
    ‖twoHermitianInvForm
        (symmetricPickBaseA tau a x v)
        (symmetricPickBaseD tau a x v)
        (symmetricPickBaseC tau a x v)
        (symmetricPickVPlus tau a x v)
        (symmetricPickVMinus tau a x v)
        (symmetricPickUPlus tau a x v)
        (symmetricPickUMinus tau a x v)‖ =
      symmetricPickH v *
        ‖symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a)‖ := by
  rw [symmetricPickInvForm_v_u_eq_h_mul_conj_phase htau ha hv]
  rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (by unfold symmetricPickH; positivity)]
  rw [norm_symmetricPickPhaseRatio hv]

/-- The sampled Pick matrix at the two symmetric interpolation nodes and the
candidate pole is exactly the general Schur-complement block. -/
theorem symmetricPickMatrix_eq_generalTwoNodePickMatrix
    {S : ℂ → ℂ} {s : ℂ} {tau a x v : ℝ}
    (ha : 0 < a) (hv : 0 < v)
    (hplus : S (symmetricPickAlphaPlus tau a) =
      -symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a))
    (hminus : S (symmetricPickAlphaMinus tau a) =
      -symmetricPickBlaschke x v (symmetricPickAlphaMinus tau a))
    (hpole : S (symmetricPickPole x v) = s) :
    upperHalfPlanePickMatrix S (symmetricPickNodes tau a x v) =
      generalTwoNodePickMatrix
        (symmetricPickBaseA tau a x v)
        (symmetricPickBaseD tau a x v)
        (symmetricPickBaseC tau a x v)
        (symmetricPickH v)
        (symmetricPickUPlus tau a x v)
        (symmetricPickUMinus tau a x v)
        (symmetricPickVPlus tau a x v)
        (symmetricPickVMinus tau a x v) s := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact symmetricPickKernel_self_plus_eq_baseA ha hplus
  · exact symmetricPickKernel_plus_minus_eq_baseC hplus hminus
  · exact symmetricPickKernel_plus_pole_eq_cross hplus hpole
  · change upperHalfPlanePickKernel S
        (symmetricPickAlphaMinus tau a) (symmetricPickAlphaPlus tau a) =
      starRingEnd ℂ (symmetricPickBaseC tau a x v)
    rw [upperHalfPlanePickKernel_conj_transpose]
    exact congrArg (starRingEnd ℂ)
      (symmetricPickKernel_plus_minus_eq_baseC hplus hminus)
  · exact symmetricPickKernel_self_minus_eq_baseD ha hminus
  · exact symmetricPickKernel_minus_pole_eq_cross hminus hpole
  · change upperHalfPlanePickKernel S
        (symmetricPickPole x v) (symmetricPickAlphaPlus tau a) =
      starRingEnd ℂ
        (normalizedPickCross
          (symmetricPickUPlus tau a x v)
          (symmetricPickVPlus tau a x v) s)
    rw [upperHalfPlanePickKernel_conj_transpose]
    exact congrArg (starRingEnd ℂ)
      (symmetricPickKernel_plus_pole_eq_cross hplus hpole)
  · change upperHalfPlanePickKernel S
        (symmetricPickPole x v) (symmetricPickAlphaMinus tau a) =
      starRingEnd ℂ
        (normalizedPickCross
          (symmetricPickUMinus tau a x v)
          (symmetricPickVMinus tau a x v) s)
    rw [upperHalfPlanePickKernel_conj_transpose]
    exact congrArg (starRingEnd ℂ)
      (symmetricPickKernel_minus_pole_eq_cross hminus hpole)
  · exact symmetricPickKernel_self_pole_eq_h hv hpole

/-- Separation-free symmetric two-node Pick bound for any function whose
sampled Pick matrix is positive semidefinite. -/
theorem norm_pole_le_symmetricPickBound_of_posSemidef
    {S : ℂ → ℂ} {s : ℂ} {tau a x v : ℝ}
    (htau : tau ≠ 0) (ha : 0 < a) (hv : 0 < v)
    (hplus : S (symmetricPickAlphaPlus tau a) =
      -symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a))
    (hminus : S (symmetricPickAlphaMinus tau a) =
      -symmetricPickBlaschke x v (symmetricPickAlphaMinus tau a))
    (hpole : S (symmetricPickPole x v) = s)
    (hpsd :
      (upperHalfPlanePickMatrix S
        (symmetricPickNodes tau a x v)).PosSemidef) :
    ‖s‖ ≤
      2 * ‖symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a)‖ /
        (1 +
          ‖symmetricPickBlaschke x v
            (symmetricPickAlphaPlus tau a)‖ ^ 2) := by
  apply norm_le_two_mul_div_one_add_sq_of_generalTwoNodePickMatrix
      (A := symmetricPickBaseA tau a x v)
      (D := symmetricPickBaseD tau a x v)
      (C := symmetricPickBaseC tau a x v)
      (h := symmetricPickH v)
      (u₀ := symmetricPickUPlus tau a x v)
      (u₁ := symmetricPickUMinus tau a x v)
      (v₀ := symmetricPickVPlus tau a x v)
      (v₁ := symmetricPickVMinus tau a x v)
  · unfold symmetricPickH
    positivity
  · positivity
  · rw [symmetricPickBase_det_eq_feature_normSq ha hv]
    exact Complex.normSq_pos.mpr
      (symmetricPickFeature_det_ne_zero htau ha hv)
  · exact symmetricPickInvNorm_u_eq_h htau ha hv
  · exact norm_symmetricPickInvForm_v_u htau ha hv
  · rw [← symmetricPickMatrix_eq_generalTwoNodePickMatrix
      ha hv hplus hminus hpole]
    exact hpsd

/-- Fully finite residual-inner specialization.  Its Pick positivity comes
from the checked factorization over the lower-root multiset. -/
theorem norm_lowerRootInnerValue_at_pole_le_symmetricPickBound
    (p : Polynomial ℂ) {tau a x v : ℝ}
    (htau : tau ≠ 0) (ha : 0 < a) (hv : 0 < v)
    (hplus : lowerRootInnerValue p (symmetricPickAlphaPlus tau a) =
      -symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a))
    (hminus : lowerRootInnerValue p (symmetricPickAlphaMinus tau a) =
      -symmetricPickBlaschke x v (symmetricPickAlphaMinus tau a)) :
    ‖lowerRootInnerValue p (symmetricPickPole x v)‖ ≤
      2 * ‖symmetricPickBlaschke x v (symmetricPickAlphaPlus tau a)‖ /
        (1 +
          ‖symmetricPickBlaschke x v
            (symmetricPickAlphaPlus tau a)‖ ^ 2) := by
  have hnodes : ∀ i,
      0 < (symmetricPickNodes tau a x v i).im := by
    intro i
    fin_cases i
    · simpa [symmetricPickNodes, symmetricPickAlphaPlus,
        upperHalfPlanePoint] using ha
    · simpa [symmetricPickNodes, symmetricPickAlphaMinus,
        upperHalfPlanePoint] using ha
    · simpa [symmetricPickNodes, symmetricPickPole,
        upperHalfPlanePoint] using hv
  exact norm_pole_le_symmetricPickBound_of_posSemidef
    htau ha hv hplus hminus rfl
    (lowerRootInnerValue_pickMatrix_posSemidef p
      (symmetricPickNodes tau a x v) hnodes)

theorem symmetricPickBase_det_pos
    {tau a x v : ℝ} (htau : tau ≠ 0) (ha : 0 < a) (hv : 0 < v) :
    0 < twoHermitianDet
      (symmetricPickBaseA tau a x v)
      (symmetricPickBaseD tau a x v)
      (symmetricPickBaseC tau a x v) := by
  rw [symmetricPickBase_det_eq_feature_normSq ha hv]
  exact Complex.normSq_pos.mpr
    (symmetricPickFeature_det_ne_zero htau ha hv)

end

end RiemannGaussian

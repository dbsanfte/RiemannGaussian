import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.Compact

/-!
# Montgomery--Taylor inverse sampling

This file isolates the exact translate kernel used by the Montgomery--Taylor
window and begins a proof-producing replacement for numerical inverse-sampling
certificates.  The key observation is qualitative but strong enough for a
strict improvement: below normalized span `6 * π`, three consecutive
correlations cannot vanish simultaneously.
-/

noncomputable section

open Real Set

namespace RiemannGaussian

/-- The angle occurring in the endpoint Montgomery--Taylor profile. -/
def montgomeryTaylorTheta : ℝ := Real.sqrt 2 / 2

/-- The normalized sharp Montgomery--Taylor translate correlation.  The sinc
form fills both removable singularities definitionally and is continuous on
all of `ℝ`. -/
def montgomeryTaylorKernel (x : ℝ) : ℝ :=
  (Real.sinc ((x - Real.sqrt 2) / 2) +
      Real.sinc ((x + Real.sqrt 2) / 2)) /
    (2 * Real.sinc montgomeryTaylorTheta)

/-- A division-free numerator for the Montgomery--Taylor kernel away from its
removable singularities. -/
def montgomeryTaylorNumerator (x : ℝ) : ℝ :=
  x * Real.cos montgomeryTaylorTheta * Real.sin (x / 2) -
    Real.sqrt 2 * Real.sin montgomeryTaylorTheta * Real.cos (x / 2)

lemma montgomeryTaylorTheta_pos : 0 < montgomeryTaylorTheta := by
  unfold montgomeryTaylorTheta
  positivity

lemma montgomeryTaylorTheta_lt_pi : montgomeryTaylorTheta < Real.pi := by
  have hsqrt : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hpi := Real.pi_gt_three
  unfold montgomeryTaylorTheta
  linarith

lemma sinc_montgomeryTaylorTheta_pos : 0 < Real.sinc montgomeryTaylorTheta := by
  rw [Real.sinc_of_ne_zero montgomeryTaylorTheta_pos.ne']
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi montgomeryTaylorTheta_pos
    montgomeryTaylorTheta_lt_pi) montgomeryTaylorTheta_pos

lemma montgomeryTaylorTheta_lt_pi_div_two :
    montgomeryTaylorTheta < Real.pi / 2 := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold montgomeryTaylorTheta
  linarith [Real.pi_gt_three]

lemma cos_montgomeryTaylorTheta_pos :
    0 < Real.cos montgomeryTaylorTheta := by
  exact Real.cos_pos_of_mem_Ioo
    ⟨by linarith [montgomeryTaylorTheta_pos, Real.pi_pos],
      montgomeryTaylorTheta_lt_pi_div_two⟩

lemma sin_montgomeryTaylorTheta_pos :
    0 < Real.sin montgomeryTaylorTheta :=
  Real.sin_pos_of_pos_of_lt_pi montgomeryTaylorTheta_pos montgomeryTaylorTheta_lt_pi

lemma three_fourths_le_cos_montgomeryTaylorTheta :
    (3 : ℝ) / 4 ≤ Real.cos montgomeryTaylorTheta := by
  have h := Real.one_sub_sq_div_two_le_cos (x := montgomeryTaylorTheta)
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold montgomeryTaylorTheta at h
  rw [div_pow, hsqrt_sq] at h
  norm_num at h ⊢
  exact h

lemma eleven_twelfths_le_sqrt_two_mul_sin_theta :
    (11 : ℝ) / 12 ≤ Real.sqrt 2 * Real.sin montgomeryTaylorTheta := by
  have hs := Real.sin_ge_sub_cube montgomeryTaylorTheta_pos.le
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold montgomeryTaylorTheta at hs ⊢
  have := mul_le_mul_of_nonneg_left hs hsqrt0
  nlinarith [hsqrt_sq]

lemma sqrt_two_mul_sin_theta_le_one :
    Real.sqrt 2 * Real.sin montgomeryTaylorTheta ≤ 1 := by
  have hs := Real.sin_le montgomeryTaylorTheta_pos.le
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold montgomeryTaylorTheta at hs ⊢
  have := mul_le_mul_of_nonneg_left hs hsqrt0
  nlinarith [hsqrt_sq]

lemma montgomeryTaylorKernel_continuous : Continuous montgomeryTaylorKernel := by
  unfold montgomeryTaylorKernel
  fun_prop

lemma montgomeryTaylorKernel_at_sqrt_two_pos :
    0 < montgomeryTaylorKernel (Real.sqrt 2) := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_lt_pi : Real.sqrt 2 < Real.pi := by
    have hsqrt_lt_two : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [Real.pi_gt_three]
  have hsinc : 0 < Real.sinc (Real.sqrt 2) := by
    rw [Real.sinc_of_ne_zero hsqrt.ne']
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hsqrt hsqrt_lt_pi) hsqrt
  rw [montgomeryTaylorKernel]
  have hzero : (Real.sqrt 2 - Real.sqrt 2) / 2 = 0 := by ring
  have htwo : (Real.sqrt 2 + Real.sqrt 2) / 2 = Real.sqrt 2 := by ring
  rw [hzero, htwo, Real.sinc_zero]
  exact div_pos (add_pos zero_lt_one hsinc)
    (mul_pos (by norm_num) sinc_montgomeryTaylorTheta_pos)

/-- Away from the positive removable singularity, a zero of the sinc kernel
is a zero of the elementary trigonometric numerator. -/
lemma montgomeryTaylorNumerator_eq_zero_of_kernel_eq_zero
    {x : ℝ} (hx0 : 0 ≤ x) (hx : montgomeryTaylorKernel x = 0) :
    montgomeryTaylorNumerator x = 0 := by
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hxr : x ≠ Real.sqrt 2 := by
    intro h
    subst x
    exact (ne_of_gt montgomeryTaylorKernel_at_sqrt_two_pos) hx
  have hxm : (x - Real.sqrt 2) / 2 ≠ 0 := by
    intro h
    apply hxr
    linarith
  have hxp : (x + Real.sqrt 2) / 2 ≠ 0 := by
    intro h
    linarith
  have hden : 2 * Real.sinc montgomeryTaylorTheta ≠ 0 := by
    exact (mul_pos (by norm_num) sinc_montgomeryTaylorTheta_pos).ne'
  rw [montgomeryTaylorKernel, div_eq_zero_iff] at hx
  rcases hx with hx | hx
  · rw [Real.sinc_of_ne_zero hxm, Real.sinc_of_ne_zero hxp] at hx
    have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have htheta : montgomeryTaylorTheta = Real.sqrt 2 / 2 := rfl
    have hsin_add := Real.sin_add (x / 2) montgomeryTaylorTheta
    have hsin_sub := Real.sin_sub (x / 2) montgomeryTaylorTheta
    rw [htheta] at hsin_add hsin_sub
    have hargm : (x - Real.sqrt 2) / 2 = x / 2 - Real.sqrt 2 / 2 := by ring
    have hargp : (x + Real.sqrt 2) / 2 = x / 2 + Real.sqrt 2 / 2 := by ring
    rw [hargm, hargp, hsin_sub, hsin_add] at hx
    unfold montgomeryTaylorNumerator montgomeryTaylorTheta
    field_simp at hx
    nlinarith
  · exact (hden hx).elim

/-- On the first half-period, the division-free numerator has only the
removable zero `sqrt 2`. -/
lemma montgomeryTaylorNumerator_zero_of_mem_zero_two_pi
    {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2 * Real.pi)
    (hx : montgomeryTaylorNumerator x = 0) : x = Real.sqrt 2 := by
  have hr0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hrpi : Real.sqrt 2 < Real.pi := by
    have hr2 : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [Real.pi_gt_three]
  rcases lt_or_ge x Real.pi with hxpi | hpix
  · have hxhalf_nonneg : 0 ≤ x / 2 := by linarith
    have hxhalf_lt : x / 2 < Real.pi / 2 := by linarith
    have hcx : 0 < Real.cos (x / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxhalf_lt⟩
    have hct := cos_montgomeryTaylorTheta_pos
    have heq : x * Real.tan (x / 2) =
        Real.sqrt 2 * Real.tan montgomeryTaylorTheta := by
      rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
      unfold montgomeryTaylorNumerator at hx
      field_simp [hcx.ne', hct.ne']
      nlinarith
    rcases lt_trichotomy x (Real.sqrt 2) with hlt | he | hgt
    · have htanlt : Real.tan (x / 2) < Real.tan montgomeryTaylorTheta := by
        apply Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hxhalf_nonneg
          montgomeryTaylorTheta_lt_pi_div_two
        unfold montgomeryTaylorTheta
        linarith
      have htan0 : 0 ≤ Real.tan (x / 2) :=
        Real.tan_nonneg_of_nonneg_of_le_pi_div_two hxhalf_nonneg hxhalf_lt.le
      have h1 : x * Real.tan (x / 2) ≤ Real.sqrt 2 * Real.tan (x / 2) :=
        mul_le_mul_of_nonneg_right hlt.le htan0
      have h2 : Real.sqrt 2 * Real.tan (x / 2) <
          Real.sqrt 2 * Real.tan montgomeryTaylorTheta :=
        mul_lt_mul_of_pos_left htanlt hr0
      linarith
    · exact he
    · have htanlt : Real.tan montgomeryTaylorTheta < Real.tan (x / 2) := by
        apply Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two montgomeryTaylorTheta_pos.le
          hxhalf_lt
        unfold montgomeryTaylorTheta
        linarith
      have htan0 : 0 ≤ Real.tan montgomeryTaylorTheta :=
        Real.tan_nonneg_of_nonneg_of_le_pi_div_two montgomeryTaylorTheta_pos.le
          montgomeryTaylorTheta_lt_pi_div_two.le
      have h1 : Real.sqrt 2 * Real.tan montgomeryTaylorTheta ≤
          x * Real.tan montgomeryTaylorTheta :=
        mul_le_mul_of_nonneg_right hgt.le htan0
      have h2 : x * Real.tan montgomeryTaylorTheta < x * Real.tan (x / 2) :=
        mul_lt_mul_of_pos_left htanlt (lt_of_lt_of_le hr0 hgt.le)
      linarith
  · have hsin : 0 ≤ Real.sin (x / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith)
    have hcos : Real.cos (x / 2) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
    have hxpos : 0 < x := Real.pi_pos.trans_le hpix
    have hA : 0 < x * Real.cos montgomeryTaylorTheta :=
      mul_pos hxpos cos_montgomeryTaylorTheta_pos
    have hB : 0 < Real.sqrt 2 * Real.sin montgomeryTaylorTheta :=
      mul_pos hr0 sin_montgomeryTaylorTheta_pos
    unfold montgomeryTaylorNumerator at hx
    have hAs : 0 ≤ x * Real.cos montgomeryTaylorTheta * Real.sin (x / 2) :=
      mul_nonneg hA.le hsin
    have hBc : Real.sqrt 2 * Real.sin montgomeryTaylorTheta * Real.cos (x / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hB.le hcos
    have hs0 : Real.sin (x / 2) = 0 := by
      have : x * Real.cos montgomeryTaylorTheta * Real.sin (x / 2) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hA.ne'
    have hc0 : Real.cos (x / 2) = 0 := by
      have : Real.sqrt 2 * Real.sin montgomeryTaylorTheta * Real.cos (x / 2) = 0 := by
        linarith
      exact (mul_eq_zero.mp this).resolve_left hB.ne'
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]

/-- The first genuine kernel zero lies strictly to the right of `13/2`.
This deliberately coarse rational localization is all the compactness
certificate needs. -/
lemma montgomeryTaylorNumerator_pos_of_two_pi_le_of_le_thirteen_halves
    {x : ℝ} (hxlo : 2 * Real.pi ≤ x) (hxhi : x ≤ (13 : ℝ) / 2) :
    0 < montgomeryTaylorNumerator x := by
  let t : ℝ := x / 2 - Real.pi
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht11 : t ≤ (11 : ℝ) / 100 := by
    dsimp [t]
    linarith [Real.pi_gt_d2]
  have htpi : t ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hs0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hst : Real.sin t ≤ t := Real.sin_le ht0
  have hc0 : 0 ≤ Real.cos t := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [Real.pi_gt_three]
  have hc99 : (99 : ℝ) / 100 ≤ Real.cos t := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := t)
    have ht_sq : t ^ 2 ≤ ((11 : ℝ) / 100) ^ 2 :=
      pow_le_pow_left₀ ht0 ht11 2
    nlinarith
  have hcosle : Real.cos montgomeryTaylorTheta ≤ 1 := Real.cos_le_one _
  have hfirst : x * Real.cos montgomeryTaylorTheta * Real.sin t ≤ (143 : ℝ) / 200 := by
    calc
      x * Real.cos montgomeryTaylorTheta * Real.sin t
          ≤ ((13 : ℝ) / 2) * Real.cos montgomeryTaylorTheta * Real.sin t := by
            gcongr
            exact cos_montgomeryTaylorTheta_pos.le
      _ ≤ ((13 : ℝ) / 2) * 1 * Real.sin t := by
            gcongr
      _ ≤ ((13 : ℝ) / 2) * 1 * t := by
            gcongr
      _ ≤ ((13 : ℝ) / 2) * 1 * ((11 : ℝ) / 100) := by
            gcongr
      _ = (143 : ℝ) / 200 := by norm_num
  have hsecond : (363 : ℝ) / 400 ≤
      Real.sqrt 2 * Real.sin montgomeryTaylorTheta * Real.cos t := by
    calc
      (363 : ℝ) / 400 = ((11 : ℝ) / 12) * ((99 : ℝ) / 100) := by norm_num
      _ ≤ (Real.sqrt 2 * Real.sin montgomeryTaylorTheta) * ((99 : ℝ) / 100) := by
        gcongr
        exact eleven_twelfths_le_sqrt_two_mul_sin_theta
      _ ≤ Real.sqrt 2 * Real.sin montgomeryTaylorTheta * Real.cos t := by
        gcongr
        exact (mul_pos (Real.sqrt_pos.2 (by norm_num))
          sin_montgomeryTaylorTheta_pos).le
  have hxhalf : x / 2 = t + Real.pi := by dsimp [t]; ring
  unfold montgomeryTaylorNumerator
  rw [hxhalf, Real.sin_add_pi, Real.cos_add_pi]
  linarith

/-- There are no numerator zeros on the negative-sine quadrant
`[3π,4π]`. -/
lemma montgomeryTaylorNumerator_ne_zero_of_three_pi_le_of_le_four_pi
    {x : ℝ} (hxlo : 3 * Real.pi ≤ x) (hxhi : x ≤ 4 * Real.pi) :
    montgomeryTaylorNumerator x ≠ 0 := by
  let t : ℝ := x / 2 - 2 * Real.pi
  have htlo : -(Real.pi / 2) ≤ t := by dsimp [t]; linarith
  have hthi : t ≤ 0 := by dsimp [t]; linarith
  have hs : Real.sin t ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le hthi (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨htlo, by linarith [Real.pi_pos]⟩
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity : 0 < 3 * Real.pi) hxlo
  let A : ℝ := x * Real.cos montgomeryTaylorTheta
  let B : ℝ := Real.sqrt 2 * Real.sin montgomeryTaylorTheta
  have hA : 0 < A :=
    mul_pos hxpos cos_montgomeryTaylorTheta_pos
  have hB : 0 < B := mul_pos (Real.sqrt_pos.2 (by norm_num)) sin_montgomeryTaylorTheta_pos
  have hxhalf : x / 2 = t + 2 * Real.pi := by dsimp [t]; ring
  unfold montgomeryTaylorNumerator
  rw [hxhalf, Real.sin_add_two_pi, Real.cos_add_two_pi]
  change A * Real.sin t - B * Real.cos t ≠ 0
  intro hzero
  have hs0 : Real.sin t = 0 := by
    have hAs : A * Real.sin t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA.le hs
    have hBc : 0 ≤ B * Real.cos t := mul_nonneg hB.le hc
    have : A * Real.sin t = 0 := by
      linarith
    exact (mul_eq_zero.mp this).resolve_left hA.ne'
  have hc0 : Real.cos t = 0 := by
    have hAs : A * Real.sin t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA.le hs
    have hBc : 0 ≤ B * Real.cos t := mul_nonneg hB.le hc
    have : B * Real.cos t = 0 := by
      linarith
    exact (mul_eq_zero.mp this).resolve_left hB.ne'
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- The second possible zero band ends before `13`. -/
lemma montgomeryTaylorNumerator_pos_of_thirteen_le_of_le_five_pi
    {x : ℝ} (hxlo : (13 : ℝ) ≤ x) (hxhi : x ≤ 5 * Real.pi) :
    0 < montgomeryTaylorNumerator x := by
  let t : ℝ := x / 2 - 2 * Real.pi
  have ht0 : 0 ≤ t := by
    dsimp [t]
    linarith [Real.pi_lt_d4]
  have htpi2 : t ≤ Real.pi / 2 := by dsimp [t]; linarith
  have ht15 : (1 : ℝ) / 5 ≤ t := by
    dsimp [t]
    linarith [Real.pi_lt_d4]
  have hs : (8 : ℝ) / 63 ≤ Real.sin t := by
    have hlin := Real.mul_le_sin ht0 htpi2
    have hcoef : (40 : ℝ) / 63 ≤ 2 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_lt_d2]
    have hm : (8 : ℝ) / 63 ≤ (2 / Real.pi) * t := by
      calc
        (8 : ℝ) / 63 = ((40 : ℝ) / 63) * ((1 : ℝ) / 5) := by norm_num
        _ ≤ (2 / Real.pi) * t := by gcongr
    exact hm.trans hlin
  have hc0 : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], htpi2⟩
  have hfirst : (26 : ℝ) / 21 ≤
      x * Real.cos montgomeryTaylorTheta * Real.sin t := by
    calc
      (26 : ℝ) / 21 = (13 : ℝ) * ((3 : ℝ) / 4) * ((8 : ℝ) / 63) := by norm_num
      _ ≤ x * ((3 : ℝ) / 4) * ((8 : ℝ) / 63) := by
        gcongr
      _ ≤ x * Real.cos montgomeryTaylorTheta * ((8 : ℝ) / 63) := by
        gcongr
        exact three_fourths_le_cos_montgomeryTaylorTheta
      _ ≤ x * Real.cos montgomeryTaylorTheta * Real.sin t := by
        gcongr
        exact mul_nonneg (by linarith) cos_montgomeryTaylorTheta_pos.le
  have hsecond :
      Real.sqrt 2 * Real.sin montgomeryTaylorTheta * Real.cos t ≤ 1 := by
    calc
      Real.sqrt 2 * Real.sin montgomeryTaylorTheta * Real.cos t
          ≤ 1 * Real.cos t := by
            gcongr
            exact sqrt_two_mul_sin_theta_le_one
      _ ≤ 1 * 1 := by
            gcongr
            exact Real.cos_le_one _
      _ = 1 := by norm_num
  have hxhalf : x / 2 = t + 2 * Real.pi := by dsimp [t]; ring
  unfold montgomeryTaylorNumerator
  rw [hxhalf, Real.sin_add_two_pi, Real.cos_add_two_pi]
  linarith

/-- There are no numerator zeros on `[5π,6π]`. -/
lemma montgomeryTaylorNumerator_ne_zero_of_five_pi_le_of_le_six_pi
    {x : ℝ} (hxlo : 5 * Real.pi ≤ x) (hxhi : x ≤ 6 * Real.pi) :
    montgomeryTaylorNumerator x ≠ 0 := by
  let t : ℝ := x / 2 - 2 * Real.pi
  have htlo : Real.pi / 2 ≤ t := by dsimp [t]; linarith
  have hthi : t ≤ Real.pi := by dsimp [t]; linarith
  have hs : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) hthi
  have hc : Real.cos t ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le htlo (by linarith)
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity : 0 < 5 * Real.pi) hxlo
  let A : ℝ := x * Real.cos montgomeryTaylorTheta
  let B : ℝ := Real.sqrt 2 * Real.sin montgomeryTaylorTheta
  have hA : 0 < A :=
    mul_pos hxpos cos_montgomeryTaylorTheta_pos
  have hB : 0 < B := mul_pos (Real.sqrt_pos.2 (by norm_num)) sin_montgomeryTaylorTheta_pos
  have hxhalf : x / 2 = t + 2 * Real.pi := by dsimp [t]; ring
  unfold montgomeryTaylorNumerator
  rw [hxhalf, Real.sin_add_two_pi, Real.cos_add_two_pi]
  change A * Real.sin t - B * Real.cos t ≠ 0
  intro hzero
  have hs0 : Real.sin t = 0 := by
    have hAs : 0 ≤ A * Real.sin t := mul_nonneg hA.le hs
    have hBc : B * Real.cos t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hB.le hc
    have : A * Real.sin t = 0 := by
      linarith
    exact (mul_eq_zero.mp this).resolve_left hA.ne'
  have hc0 : Real.cos t = 0 := by
    have hAs : 0 ≤ A * Real.sin t := mul_nonneg hA.le hs
    have hBc : B * Real.cos t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hB.le hc
    have : B * Real.cos t = 0 := by
      linarith
    exact (mul_eq_zero.mp this).resolve_left hB.ne'
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- Every nonnegative zero of the sharp kernel below `6π` lies in one of two
coarse, disjoint bands. -/
theorem montgomeryTaylorKernel_zero_localization
    {x : ℝ} (hx0 : 0 ≤ x) (hx6 : x ≤ 6 * Real.pi)
    (hx : montgomeryTaylorKernel x = 0) :
    ((13 : ℝ) / 2 < x ∧ x < 3 * Real.pi) ∨
      (4 * Real.pi < x ∧ x < 13) := by
  have hn := montgomeryTaylorNumerator_eq_zero_of_kernel_eq_zero hx0 hx
  rcases le_or_gt x (2 * Real.pi) with h2 | h2
  · have hxr := montgomeryTaylorNumerator_zero_of_mem_zero_two_pi hx0 h2 hn
    subst x
    exact (ne_of_gt montgomeryTaylorKernel_at_sqrt_two_pos hx).elim
  rcases lt_or_ge x (3 * Real.pi) with h3 | h3
  · left
    refine ⟨?_, h3⟩
    by_contra hnot
    exact (ne_of_gt
      (montgomeryTaylorNumerator_pos_of_two_pi_le_of_le_thirteen_halves h2.le
        (not_lt.mp hnot))) hn
  rcases le_or_gt x (4 * Real.pi) with h4 | h4
  · exact (montgomeryTaylorNumerator_ne_zero_of_three_pi_le_of_le_four_pi h3 h4 hn).elim
  rcases lt_or_ge x (5 * Real.pi) with h5 | h5
  · right
    refine ⟨h4, ?_⟩
    by_contra hnot
    exact (ne_of_gt
      (montgomeryTaylorNumerator_pos_of_thirteen_le_of_le_five_pi
        (not_lt.mp hnot) h5.le)) hn
  · exact (montgomeryTaylorNumerator_ne_zero_of_five_pi_le_of_le_six_pi h5 hx6 hn).elim

/-- The three correlations carried by two consecutive gaps. -/
def montgomeryTaylorTripleEnergy (a b : ℝ) : ℝ :=
  2 * (montgomeryTaylorKernel a ^ 2 + montgomeryTaylorKernel b ^ 2 +
    montgomeryTaylorKernel (a + b) ^ 2)

lemma montgomeryTaylorTripleEnergy_continuous :
    Continuous (fun p : ℝ × ℝ => montgomeryTaylorTripleEnergy p.1 p.2) := by
  unfold montgomeryTaylorTripleEnergy
  have ha : Continuous (fun p : ℝ × ℝ => montgomeryTaylorKernel p.1) :=
    montgomeryTaylorKernel_continuous.comp continuous_fst
  have hb : Continuous (fun p : ℝ × ℝ => montgomeryTaylorKernel p.2) :=
    montgomeryTaylorKernel_continuous.comp continuous_snd
  have hab : Continuous (fun p : ℝ × ℝ => montgomeryTaylorKernel (p.1 + p.2)) :=
    montgomeryTaylorKernel_continuous.comp (continuous_fst.add continuous_snd)
  exact continuous_const.mul (((ha.pow 2).add (hb.pow 2)).add (hab.pow 2))

lemma montgomeryTaylorTripleEnergy_nonneg (a b : ℝ) :
    0 ≤ montgomeryTaylorTripleEnergy a b := by
  unfold montgomeryTaylorTripleEnergy
  positivity

/-- The kernel-zero bands cannot form an additive triple below span `6π`.
This is the information-preserving obstruction behind the certificate: two
adjacent gaps and their sum cannot all sit at kernel zeros. -/
theorem montgomeryTaylorKernel_no_additive_zero_below_six_pi
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hab6 : a + b ≤ 6 * Real.pi)
    (ha : montgomeryTaylorKernel a = 0)
    (hb : montgomeryTaylorKernel b = 0) :
    montgomeryTaylorKernel (a + b) ≠ 0 := by
  have ha6 : a ≤ 6 * Real.pi := by linarith
  have hb6 : b ≤ 6 * Real.pi := by linarith
  have hla := montgomeryTaylorKernel_zero_localization ha0 ha6 ha
  have hlb := montgomeryTaylorKernel_zero_localization hb0 hb6 hb
  intro hab
  have hlab := montgomeryTaylorKernel_zero_localization (by linarith) hab6 hab
  have hfour : (13 : ℝ) / 2 < 4 * Real.pi := by
    linarith [Real.pi_gt_three]
  have htwo : 2 * Real.pi < (13 : ℝ) / 2 := by
    linarith [Real.pi_lt_d4]
  rcases hla with ha₁ | ha₂
  · rcases hlb with hb₁ | hb₂
    · have hsum13 : (13 : ℝ) < a + b := by linarith
      rcases hlab with hab₁ | hab₂
      · linarith [Real.pi_lt_d4]
      · linarith
    · have : 6 * Real.pi < a + b := by linarith
      linarith
  · have hb65 : (13 : ℝ) / 2 < b := by
      rcases hlb with hb₁ | hb₂
      · exact hb₁.1
      · linarith
    have : 6 * Real.pi < a + b := by linarith
    linarith

theorem montgomeryTaylorTripleEnergy_pos_of_mem_six_pi
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab6 : a + b ≤ 6 * Real.pi) :
    0 < montgomeryTaylorTripleEnergy a b := by
  have hnonneg := montgomeryTaylorTripleEnergy_nonneg a b
  apply lt_of_le_of_ne hnonneg
  intro hzero
  have hsum : montgomeryTaylorKernel a ^ 2 + montgomeryTaylorKernel b ^ 2 +
      montgomeryTaylorKernel (a + b) ^ 2 = 0 := by
    unfold montgomeryTaylorTripleEnergy at hzero
    linarith
  have ha_sq : montgomeryTaylorKernel a ^ 2 = 0 := by
    nlinarith [sq_nonneg (montgomeryTaylorKernel b),
      sq_nonneg (montgomeryTaylorKernel (a + b))]
  have hb_sq : montgomeryTaylorKernel b ^ 2 = 0 := by
    nlinarith [sq_nonneg (montgomeryTaylorKernel a),
      sq_nonneg (montgomeryTaylorKernel (a + b))]
  have hab_sq : montgomeryTaylorKernel (a + b) ^ 2 = 0 := by
    nlinarith [sq_nonneg (montgomeryTaylorKernel a),
      sq_nonneg (montgomeryTaylorKernel b)]
  have ha := sq_eq_zero_iff.mp ha_sq
  have hb := sq_eq_zero_iff.mp hb_sq
  have hab := sq_eq_zero_iff.mp hab_sq
  exact montgomeryTaylorKernel_no_additive_zero_below_six_pi ha0 hb0 hab6 ha hb hab

/-- The compact triangle on which the affine span term alone does not yet
close the certificate. -/
def montgomeryTaylorTripleDomain : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 6 * Real.pi}

lemma montgomeryTaylorTripleDomain_nonempty :
    montgomeryTaylorTripleDomain.Nonempty := by
  refine ⟨(0, 0), ?_⟩
  simp [montgomeryTaylorTripleDomain, Real.pi_pos.le]

lemma montgomeryTaylorTripleDomain_isCompact :
    IsCompact montgomeryTaylorTripleDomain := by
  have hclosed : IsClosed montgomeryTaylorTripleDomain := by
    unfold montgomeryTaylorTripleDomain
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  have hsub : montgomeryTaylorTripleDomain ⊆
      Set.Icc (0 : ℝ) (6 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (6 * Real.pi) := by
    rintro p ⟨hp0, hp1, hp2⟩
    exact ⟨⟨hp0, by linarith⟩, ⟨hp1, by linarith⟩⟩
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed hsub

/-- Compactness upgrades the zero-band obstruction to a uniform positive
energy floor.  No floating-point or interval-oracle premise occurs. -/
theorem exists_montgomeryTaylorTripleEnergy_floor :
    ∃ m : ℝ, 0 < m ∧ ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b ≤ 6 * Real.pi → m ≤ montgomeryTaylorTripleEnergy a b := by
  obtain ⟨m, hm, hfloor⟩ := montgomeryTaylorTripleDomain_isCompact.exists_forall_le'
    montgomeryTaylorTripleEnergy_continuous.continuousOn
    (a := 0) (fun p hp =>
      montgomeryTaylorTripleEnergy_pos_of_mem_six_pi hp.1 hp.2.1 hp.2.2)
  refine ⟨m, hm, ?_⟩
  intro a b ha hb hab
  exact hfloor (a, b) ⟨ha, hb, hab⟩

/-- A fully rigorous affine consecutive-triple certificate exists with span
cutoff exactly `6π`.  Its positive constant is supplied by the proved compact
minimum, rather than by a trusted numerical enclosure. -/
theorem exists_montgomeryTaylorTripleAffineCertificate :
    ∃ A B : ℝ,
      0 < A ∧ 0 < B ∧ A ≤ 1 ∧ B = A / (6 * Real.pi) ∧
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
        A ≤ montgomeryTaylorTripleEnergy a b + B * (a + b) := by
  obtain ⟨m, hm, hfloor⟩ := exists_montgomeryTaylorTripleEnergy_floor
  let A : ℝ := min (m / 2) 1
  let B : ℝ := A / (6 * Real.pi)
  have hA : 0 < A := by
    dsimp [A]
    exact lt_min (by positivity) zero_lt_one
  have hA1 : A ≤ 1 := min_le_right _ _
  have hAm : A ≤ m := by
    calc
      A ≤ m / 2 := min_le_left _ _
      _ ≤ m := by linarith
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨A, B, hA, hB, hA1, rfl, ?_⟩
  intro a b ha hb
  rcases le_or_gt (a + b) (6 * Real.pi) with hab | hab
  · have hE := hfloor a b ha hb hab
    have hspan : 0 ≤ B * (a + b) := mul_nonneg hB.le (add_nonneg ha hb)
    linarith
  · have hspan : A ≤ B * (a + b) := by
      dsimp [B]
      rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
      exact mul_le_mul_of_nonneg_left hab.le hA.le
    exact hspan.trans (le_add_of_nonneg_left (montgomeryTaylorTripleEnergy_nonneg a b))

lemma sqrt_two_lt_thirteen_halves : Real.sqrt 2 < (13 : ℝ) / 2 := by
  have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [Real.sqrt_nonneg 2]

lemma two_pi_lt_thirteen_halves : 2 * Real.pi < (13 : ℝ) / 2 := by
  have hpi := Real.pi_lt_d4
  linarith

lemma three_pi_lt_thirteen : 3 * Real.pi < (13 : ℝ) := by
  linarith [Real.pi_lt_d4]

lemma six_pi_lt_nineteen : 6 * Real.pi < (19 : ℝ) := by
  linarith [Real.pi_lt_d4]

end RiemannGaussian

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierLocalCancellation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Real-node principal values of the separated Suzuki carrier

The two carrier channels have the same real simple-pole coefficient at a
real xi node. Subtracting one explicit odd counterterm makes each channel
absolutely integrable, while leaving their signed difference unchanged.
The counterterm has zero integral outside every centered positive-radius
gap. This justifies the actual principal value, including multiple nodes.

These real-axis statements do not discard any off-axis carrier poles or
assert a global contour estimate.
-/

open Complex Filter MeasureTheory Metric Set
open scoped Classical Topology

namespace RiemannGaussian
noncomputable section

private theorem integrable_of_local_bound_inverse_square
    {f : ℝ → ℂ} (hf : Measurable f) (a : ℝ) {k : ℝ} (hk : 0 ≤ k)
    (htail : ∀ x : ℝ, ‖f x‖ ≤ k / (x - a) ^ 2)
    (hlocal : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, |x - a| < r → ‖f x‖ ≤ C) : Integrable f := by
  obtain ⟨r, hr, C, hC, hlocal⟩ := hlocal
  let d := r / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdr : d < r := by dsimp [d]; linarith
  let g : ℝ → ℝ := fun x ↦
    (Icc (a - d) (a + d)).indicator (fun _ ↦ C) x +
      (k * (1 + (d ^ 2)⁻¹)) * (1 + (x - a) ^ 2)⁻¹
  have hg : Integrable g := by
    exact ((integrableOn_const (s := Icc (a - d) (a + d))
      (by simp)).integrable_indicator measurableSet_Icc).add
        ((integrable_suzukiShiftedCauchyDensity a).const_mul _)
  apply hg.mono hf.aestronglyMeasurable
  filter_upwards with x
  have hg0 : 0 ≤ g x := by
    dsimp [g]
    exact add_nonneg (indicator_nonneg (fun _ _ ↦ hC) x) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg hg0]
  by_cases hx : |x - a| ≤ d
  · have hxmem : x ∈ Icc (a - d) (a + d) := by
      rcases abs_le.mp hx with ⟨hl, hu⟩
      constructor <;> linarith
    dsimp [g]
    rw [indicator_of_mem hxmem]
    exact (hlocal x (hx.trans_lt hdr)).trans
      (le_add_of_nonneg_right (by positivity))
  · have hdx : d < |x - a| := lt_of_not_ge hx
    have hu : 0 < (x - a) ^ 2 := sq_pos_of_ne_zero
      (abs_pos.mp (hd.trans hdx))
    have hdu : d ^ 2 ≤ (x - a) ^ 2 := by
      rw [← sq_abs (x - a)]
      exact (sq_le_sq₀ hd.le (abs_nonneg _)).2 hdx.le
    have hrecip : 1 / (x - a) ^ 2 ≤
        (1 + (d ^ 2)⁻¹) * (1 + (x - a) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ hu (by positivity)]
      have hds : 0 < d ^ 2 := sq_pos_of_pos hd
      field_simp [hds.ne']
      nlinarith
    calc
      ‖f x‖ ≤ k / (x - a) ^ 2 := htail x
      _ ≤ k * ((1 + (d ^ 2)⁻¹) * (1 + (x - a) ^ 2)⁻¹) := by
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hrecip hk
      _ ≤ g x := by
        dsimp [g]
        rw [← mul_assoc]
        exact le_add_of_nonneg_left (indicator_nonneg (fun _ _ ↦ hC) x)

/-- The real odd counterterm with the genuine reciprocal multiplicity.
Its quadratic normalization preserves the residue and supplies cubic decay. -/
def suzukiXiRealNodeCounterterm (rho : NontrivialZetaZero) (x : ℝ) : ℂ :=
  (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ /
    (((x - (zetaSpectralCoordinate rho.1).re : ℝ) : ℂ) *
      (1 + ((x - (zetaSpectralCoordinate rho.1).re : ℝ) : ℂ) ^ 2))

/-- The separated carrier after its common real-node counterterm is
subtracted. The original totalized values are retained. -/
def suzukiXiRealNodeRegularizedChannel (rho : NontrivialZetaZero) (x : ℝ) : ℂ :=
  suzukiRealAxisXiZeroCarrier x /
      ((x : ℂ) - zetaSpectralCoordinate rho.1) ^ 2 -
    suzukiXiRealNodeCounterterm rho x

/-- The odd counterterm is Borel measurable. -/
theorem measurable_suzukiXiRealNodeCounterterm (rho : NontrivialZetaZero) :
    Measurable (suzukiXiRealNodeCounterterm rho) := by
  unfold suzukiXiRealNodeCounterterm
  fun_prop

/-- The counterterm keeps its real sign under complex conjugation. -/
theorem conj_suzukiXiRealNodeCounterterm (rho : NontrivialZetaZero) (x : ℝ) :
    starRingEnd ℂ (suzukiXiRealNodeCounterterm rho x) =
      suzukiXiRealNodeCounterterm rho x := by
  simp [suzukiXiRealNodeCounterterm]

/-- The counterterm's exact norm, including its totalized central value. -/
theorem norm_suzukiXiRealNodeCounterterm (rho : NontrivialZetaZero) (x : ℝ) :
    ‖suzukiXiRealNodeCounterterm rho x‖ =
      ‖(analyticZetaZeroMultiplicity rho : ℂ)⁻¹‖ /
        (|x - (zetaSpectralCoordinate rho.1).re| *
          (1 + (x - (zetaSpectralCoordinate rho.1).re) ^ 2)) := by
  unfold suzukiXiRealNodeCounterterm
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcast (y : ℝ) : 1 + (y : ℂ) ^ 2 = ((1 + y ^ 2 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (show 0 < 1 + (x - (zetaSpectralCoordinate rho.1).re) ^ 2 by positivity)]

/-- The meromorphic extension of the subtraction has two explicit auxiliary
poles as well as the real pole. Its exact partial fractions keep those
additional terms available for a later contour calculation. -/
theorem suzukiXiRealNodeCounterterm_complex_partialFractions
    (rho : NontrivialZetaZero) {z : ℂ}
    (hzero : z ≠ ((zetaSpectralCoordinate rho.1).re : ℂ))
    (hplus : z ≠ ((zetaSpectralCoordinate rho.1).re : ℂ) + I)
    (hminus : z ≠ ((zetaSpectralCoordinate rho.1).re : ℂ) - I) :
    (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ /
        ((z - ((zetaSpectralCoordinate rho.1).re : ℂ)) *
          (1 + (z - ((zetaSpectralCoordinate rho.1).re : ℂ)) ^ 2)) =
      (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ /
          (z - ((zetaSpectralCoordinate rho.1).re : ℂ)) -
        ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ / 2) /
          (z - (((zetaSpectralCoordinate rho.1).re : ℂ) + I)) -
        ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ / 2) /
          (z - (((zetaSpectralCoordinate rho.1).re : ℂ) - I)) := by
  let a : ℂ := (zetaSpectralCoordinate rho.1).re
  have hquad : 1 + (z - a) ^ 2 = (z - (a + I)) * (z - (a - I)) := by
    ring_nf
    simp only [I_sq]
    ring
  dsimp [a] at hquad
  have hm : (analyticZetaZeroMultiplicity rho : ℂ) ≠ 0 := by
    exact_mod_cast (analyticZetaZeroMultiplicity_positive rho).ne'
  rw [hquad]
  field_simp [hm, sub_ne_zero.mpr hzero, sub_ne_zero.mpr hplus, sub_ne_zero.mpr hminus]
  ring_nf
  simp only [I_sq]
  ring

/-- The literal regularized channel is Borel measurable. -/
theorem measurable_suzukiXiRealNodeRegularizedChannel (rho : NontrivialZetaZero) :
    Measurable (suzukiXiRealNodeRegularizedChannel rho) := by
  exact (measurable_suzukiRealAxisXiZeroCarrier.div
    ((Complex.continuous_ofReal.sub continuous_const).pow 2).measurable).sub
      (measurable_suzukiXiRealNodeCounterterm rho)

private theorem local_bound_regularized_channel
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, |x - (zetaSpectralCoordinate rho.1).re| < r →
        ‖suzukiXiRealNodeRegularizedChannel rho x‖ ≤ C := by
  let a := zetaSpectralCoordinate rho.1
  let L : ℂ := (analyticZetaZeroMultiplicity rho : ℂ)⁻¹
  have ha : (a.re : ℂ) = a := Complex.ext (by simp) (by simpa [a] using hrho.symm)
  obtain ⟨p, q, hp, _hq, he⟩ := exists_suzukiXiCarrier_diagonal_polar_models rho
  change AnalyticAt ℂ p a at hp
  let F : ℂ → ℂ := fun z ↦ p z + L * (z - a) / (1 + (z - a) ^ 2)
  have hF : AnalyticAt ℂ F a := by
    exact hp.add ((analyticAt_const.mul
      (analyticAt_id.sub analyticAt_const)).div
        (analyticAt_const.add ((analyticAt_id.sub analyticAt_const).pow 2)) (by simp))
  have hnear : ∀ᶠ z in 𝓝 a, ‖F z - F a‖ < 1 :=
    hF.continuousAt.tendsto.eventually (eventually_norm_sub_lt (F a) (by norm_num))
  have hquadCont : ContinuousAt (fun z : ℂ ↦ 1 + (z - a) ^ 2) a := by fun_prop
  have hquad : ∀ᶠ z in 𝓝 a, 1 + (z - a) ^ 2 ≠ 0 :=
    hquadCont.eventually_ne (by simp)
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (he.and (hnear.and hquad))
  refine ⟨r, hr, ‖F a‖ + 1, by positivity, ?_⟩
  intro x hx
  by_cases hxa : x = a.re
  · subst x
    have hden : (a.re : ℂ) - zetaSpectralCoordinate rho.1 = 0 := by
      rw [ha]; exact sub_self _
    simp only [suzukiXiRealNodeRegularizedChannel, suzukiXiRealNodeCounterterm,
      hden, a, sub_self, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul, div_zero, norm_zero]
    positivity
  have hca : (x : ℂ) ≠ a := by
    intro hz
    apply hxa
    simpa using congrArg Complex.re hz
  have hdist : dist (x : ℂ) a = |x - a.re| := by
    calc
      dist (x : ℂ) a = dist (x : ℂ) (a.re : ℂ) := congrArg (dist (x : ℂ)) ha.symm
      _ = |x - a.re| := by
        rw [dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨hpolar, hnorm, hquadx⟩ := hball (y := (x : ℂ)) (by
    change dist (x : ℂ) a < r
    rw [hdist]
    exact hx)
  have hsub : (x : ℂ) - a ≠ 0 := sub_ne_zero.mpr hca
  have heq : suzukiXiRealNodeRegularizedChannel rho x = F (x : ℂ) := by
    have hpol : suzukiXiZeroCarrier (x : ℂ) / ((x : ℂ) - a) ^ 2 =
        L / ((x : ℂ) - a) + p (x : ℂ) := (hpolar hca).1
    change suzukiXiZeroCarrier (x : ℂ) / ((x : ℂ) - a) ^ 2 -
      L / (((x - a.re : ℝ) : ℂ) * (1 + ((x - a.re : ℝ) : ℂ) ^ 2)) = _
    rw [hpol, Complex.ofReal_sub, ha]
    dsimp [F]
    field_simp [hsub, hquadx]
    ring
  rw [heq]
  calc
    ‖F (x : ℂ)‖ ≤ ‖F (x : ℂ) - F a‖ + ‖F a‖ := by
      simpa only [sub_add_cancel] using norm_add_le (F (x : ℂ) - F a) (F a)
    _ ≤ ‖F a‖ + 1 := by linarith

/-- Subtracting the explicit common pole leaves an absolutely integrable
channel at every real xi node, without a simplicity assumption. -/
theorem integrable_suzukiXiRealNodeRegularizedChannel
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    Integrable (suzukiXiRealNodeRegularizedChannel rho) := by
  let a := (zetaSpectralCoordinate rho.1).re
  let L : ℂ := (analyticZetaZeroMultiplicity rho : ℂ)⁻¹
  have ha : (a : ℂ) = zetaSpectralCoordinate rho.1 :=
    Complex.ext (by simp [a]) (by simpa using hrho.symm)
  apply integrable_of_local_bound_inverse_square
    (measurable_suzukiXiRealNodeRegularizedChannel rho) a (k := 1 + ‖L‖)
    (by positivity) ?_ (local_bound_regularized_channel rho hrho)
  intro x
  have hc : ‖suzukiRealAxisXiZeroCarrier x /
      ((x : ℂ) - zetaSpectralCoordinate rho.1) ^ 2‖ ≤ 1 / (x - a) ^ 2 := by
    rw [norm_div, norm_pow, ← ha, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact div_le_div_of_nonneg_right (norm_suzukiXiZeroCarrier_ofReal_le_one x)
      (sq_nonneg _)
  have hcounter : ‖suzukiXiRealNodeCounterterm rho x‖ ≤ ‖L‖ / (x - a) ^ 2 := by
    rw [norm_suzukiXiRealNodeCounterterm]
    change ‖L‖ / (|x - a| * (1 + (x - a) ^ 2)) ≤ ‖L‖ / (x - a) ^ 2
    by_cases hx : x - a = 0
    · simp [hx]
    have hpos : 0 < |x - a| := abs_pos.mpr hx
    have hsq : 0 < (x - a) ^ 2 := sq_pos_of_ne_zero hx
    have habs : |x - a| ≤ 1 + (x - a) ^ 2 := by
      nlinarith [sq_nonneg (|x - a| - 1), sq_abs (x - a)]
    apply div_le_div_of_nonneg_left (norm_nonneg _) hsq
    calc
      (x - a) ^ 2 = |x - a| * |x - a| := by rw [← sq_abs]; ring
      _ ≤ |x - a| * (1 + (x - a) ^ 2) :=
        mul_le_mul_of_nonneg_left habs hpos.le
  exact (norm_sub_le _ _).trans ((add_le_add hc hcounter).trans_eq (by ring))

private theorem measurableSet_real_node_exterior (a e : ℝ) :
    MeasurableSet {x : ℝ | e ≤ |x - a|} := by measurability

/-- Outside every positive symmetric gap the pole counterterm is
absolutely integrable, with its original signed value. -/
theorem integrableOn_suzukiXiRealNodeCounterterm_exterior
    (rho : NontrivialZetaZero) {e : ℝ} (he : 0 < e) :
    IntegrableOn (suzukiXiRealNodeCounterterm rho)
      {x : ℝ | e ≤ |x - (zetaSpectralCoordinate rho.1).re|} := by
  let a := (zetaSpectralCoordinate rho.1).re
  let L : ℂ := (analyticZetaZeroMultiplicity rho : ℂ)⁻¹
  have hdom := ((integrable_suzukiShiftedCauchyDensity a).const_mul (‖L‖ / e)).integrableOn
    (s := {x : ℝ | e ≤ |x - a|})
  apply hdom.mono' (measurable_suzukiXiRealNodeCounterterm rho).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_real_node_exterior a e)] with x hx
  rw [norm_suzukiXiRealNodeCounterterm]
  change ‖L‖ / (|x - a| * (1 + (x - a) ^ 2)) ≤
    ‖L‖ / e * (1 + (x - a) ^ 2)⁻¹
  rw [← div_eq_mul_inv, div_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _)
    (mul_pos he (by positivity))
    (mul_le_mul_of_nonneg_right hx (by positivity))

/-- Reflection about the real node negates the counterterm exactly. -/
theorem suzukiXiRealNodeCounterterm_reflect (rho : NontrivialZetaZero) (x : ℝ) :
    suzukiXiRealNodeCounterterm rho (2 * (zetaSpectralCoordinate rho.1).re - x) =
      -suzukiXiRealNodeCounterterm rho x := by
  have he (a : ℝ) : 2 * a - x - a = -(x - a) := by ring
  simp only [suzukiXiRealNodeCounterterm, he, Complex.ofReal_neg, neg_sq, neg_mul, div_neg]

/-- The common counterterm contributes exactly zero on every symmetric
real-axis exterior. This equality retains, rather than estimates, its sign. -/
theorem integral_suzukiXiRealNodeCounterterm_exterior_eq_zero
    (rho : NontrivialZetaZero) (e : ℝ) :
    (∫ x in {x : ℝ | e ≤ |x - (zetaSpectralCoordinate rho.1).re|},
      suzukiXiRealNodeCounterterm rho x) = 0 := by
  let a := (zetaSpectralCoordinate rho.1).re
  let f : ℝ → ℂ := {x : ℝ | e ≤ |x - a|}.indicator (suzukiXiRealNodeCounterterm rho)
  have href : ∀ x : ℝ, f (2 * a - x) = -f x := by
    intro x
    have hdist : |2 * a - x - a| = |x - a| := by
      rw [show 2 * a - x - a = -(x - a) by ring, abs_neg]
    dsimp [f]
    by_cases hx : e ≤ |x - a|
    · rw [indicator_of_mem (by simpa only [mem_ofPred_eq, hdist] using hx),
        indicator_of_mem (show x ∈ {x : ℝ | e ≤ |x - a|} from hx)]
      exact suzukiXiRealNodeCounterterm_reflect rho x
    · rw [indicator_of_notMem (by simpa only [mem_ofPred_eq, hdist] using hx),
        indicator_of_notMem (show x ∉ {x : ℝ | e ≤ |x - a|} from hx), neg_zero]
  have hi := integral_sub_left_eq_self f volume (2 * a)
  have hf : (fun x ↦ f (2 * a - x)) = fun x ↦ -f x := funext href
  rw [hf, integral_neg] at hi
  rw [← integral_indicator (measurableSet_real_node_exterior a e)]
  exact self_eq_neg.mp hi.symm

/-- At every positive cutoff the actual separated carrier is integrable
and its integral equals that of the regularized channel on the same set. -/
theorem suzukiXiRealNode_exterior_integral_eq_regularized
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) {e : ℝ} (he : 0 < e) :
    IntegrableOn (fun x : ℝ ↦ suzukiRealAxisXiZeroCarrier x /
      ((x : ℂ) - zetaSpectralCoordinate rho.1) ^ 2)
      {x : ℝ | e ≤ |x - (zetaSpectralCoordinate rho.1).re|} ∧
    (∫ x in {x : ℝ | e ≤ |x - (zetaSpectralCoordinate rho.1).re|},
      suzukiRealAxisXiZeroCarrier x / ((x : ℂ) - zetaSpectralCoordinate rho.1) ^ 2) =
    ∫ x in {x : ℝ | e ≤ |x - (zetaSpectralCoordinate rho.1).re|},
      suzukiXiRealNodeRegularizedChannel rho x := by
  have hf := (integrable_suzukiXiRealNodeRegularizedChannel rho hrho).integrableOn
    (s := {x : ℝ | e ≤ |x - (zetaSpectralCoordinate rho.1).re|})
  have hc := integrableOn_suzukiXiRealNodeCounterterm_exterior rho he
  have heq : (fun x : ℝ ↦ suzukiRealAxisXiZeroCarrier x /
      ((x : ℂ) - zetaSpectralCoordinate rho.1) ^ 2) =
      fun x ↦ suzukiXiRealNodeRegularizedChannel rho x +
        suzukiXiRealNodeCounterterm rho x := by
    funext x
    exact (sub_add_cancel _ _).symm
  rw [heq]
  refine ⟨hf.add hc, ?_⟩
  rw [integral_add hf hc, integral_suzukiXiRealNodeCounterterm_exterior_eq_zero, add_zero]

/-- The genuine centered principal value exists at every real xi node
and equals the ordinary integral after the exact common subtraction. -/
theorem tendsto_suzukiXiRealNode_principalValue
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    Tendsto (fun e : ℝ ↦
      ∫ x in {x : ℝ | e ≤ |x - (zetaSpectralCoordinate rho.1).re|},
        suzukiRealAxisXiZeroCarrier x / ((x : ℂ) - zetaSpectralCoordinate rho.1) ^ 2)
      (𝓝[>] 0) (𝓝 (∫ x : ℝ, suzukiXiRealNodeRegularizedChannel rho x)) := by
  let a := (zetaSpectralCoordinate rho.1).re
  let f := suzukiXiRealNodeRegularizedChannel rho
  have hf := integrable_suzukiXiRealNodeRegularizedChannel rho hrho
  have ht : Tendsto (fun e : ℝ ↦ ∫ x : ℝ, {x : ℝ | e ≤ |x - a|}.indicator f x)
      (𝓝[>] 0) (𝓝 (∫ x : ℝ, f x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖)
    · exact Eventually.of_forall fun e ↦
        hf.aestronglyMeasurable.indicator (measurableSet_real_node_exterior a e)
    · exact Eventually.of_forall fun e ↦ Eventually.of_forall fun x ↦
        norm_indicator_le_norm_self _ _
    · exact hf.norm
    · have hne : ∀ᵐ x : ℝ, x ≠ a := by
        rw [ae_iff]
        simpa only [not_not, ofPred_eq_eq_singleton] using
          (measure_singleton a : volume ({a} : Set ℝ) = 0)
      filter_upwards [hne] with x hx
      have hpos : 0 < |x - a| := abs_pos.mpr (sub_ne_zero.mpr hx)
      have heq : (fun e : ℝ ↦ {x : ℝ | e ≤ |x - a|}.indicator f x) =ᶠ[𝓝[>] 0]
          fun _ ↦ f x := by
        filter_upwards [(eventually_lt_nhds hpos).filter_mono nhdsWithin_le_nhds] with e he
        exact indicator_of_mem (show x ∈ {x : ℝ | e ≤ |x - a|} from he.le) f
      exact tendsto_const_nhds.congr' heq.symm
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  rw [integral_indicator (measurableSet_real_node_exterior a e)]
  exact (suzukiXiRealNode_exterior_integral_eq_regularized rho hrho he).2.symm

/-- Conjugation gives the other channel with precisely the same real
subtraction, at every real node and every real argument. -/
theorem conj_suzukiXiRealNodeRegularizedChannel
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) (x : ℝ) :
    starRingEnd ℂ (suzukiXiRealNodeRegularizedChannel rho x) =
      suzukiXiSharpCarrier (x : ℂ) / ((x : ℂ) - zetaSpectralCoordinate rho.1) ^ 2 -
        suzukiXiRealNodeCounterterm rho x := by
  have ha : starRingEnd ℂ (zetaSpectralCoordinate rho.1) = zetaSpectralCoordinate rho.1 := by
    exact Complex.conj_eq_iff_im.mpr hrho
  rw [suzukiXiRealNodeRegularizedChannel, map_sub, map_div₀, map_pow, map_sub,
    Complex.conj_ofReal, ha, conj_suzukiXiRealNodeCounterterm,
    suzukiXiSharpCarrier_ofReal]

/-- The reflected channel is absolutely integrable after that same
subtraction; no separate principal part has been dropped. -/
theorem integrable_suzukiXiRealNodeRegularizedSharpChannel
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    Integrable (fun x : ℝ ↦ suzukiXiSharpCarrier (x : ℂ) /
      ((x : ℂ) - zetaSpectralCoordinate rho.1) ^ 2 - suzukiXiRealNodeCounterterm rho x) := by
  apply ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp
    (integrable_suzukiXiRealNodeRegularizedChannel rho hrho)).congr
  exact Eventually.of_forall (conj_suzukiXiRealNodeRegularizedChannel rho hrho)

/-- The actual real-node Gram is the signed difference of two ordinary
integrals after regularization. The common counterterm cancels exactly. -/
theorem suzukiXiBoundaryCarrierGramKernel_real_eq_regularized_integral
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    suzukiXiBoundaryCarrierGramKernel rho rho =
      ((∫ x : ℝ, suzukiXiRealNodeRegularizedChannel rho x) -
        starRingEnd ℂ (∫ x : ℝ, suzukiXiRealNodeRegularizedChannel rho x)) / (2 * I) := by
  have hf := integrable_suzukiXiRealNodeRegularizedChannel rho hrho
  have hc : Integrable (fun x : ℝ ↦
      starRingEnd ℂ (suzukiXiRealNodeRegularizedChannel rho x)) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf
  have ha : starRingEnd ℂ (zetaSpectralCoordinate rho.1) = zetaSpectralCoordinate rho.1 :=
    Complex.conj_eq_iff_im.mpr hrho
  rw [suzukiXiBoundaryCarrierGramKernel_eq_continuation_integral]
  calc
    _ = ∫ x : ℝ, (suzukiXiRealNodeRegularizedChannel rho x -
        starRingEnd ℂ (suzukiXiRealNodeRegularizedChannel rho x)) / (2 * I) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [conj_suzukiXiRealNodeRegularizedChannel rho hrho]
      unfold suzukiXiRealNodeRegularizedChannel suzukiXiCarrierGramContinuation
      rw [ha]
      change _ = ((suzukiXiZeroCarrier (x : ℂ) / ((x : ℂ) - zetaSpectralCoordinate rho.1) ^ 2 - _) -
        (suzukiXiSharpCarrier (x : ℂ) / ((x : ℂ) - zetaSpectralCoordinate rho.1) ^ 2 - _)) / _
      simp only [pow_two, div_eq_mul_inv, mul_inv]
      ring
    _ = _ := by rw [integral_div, integral_sub hf hc, integral_conj]

private theorem memLp_carrier_resolvent (rho : NontrivialZetaZero) :
    MemLp (fun x : ℝ ↦ suzukiRealAxisXiZeroCarrier x /
      ((x : ℂ) - zetaSpectralCoordinate rho.1)) 2 := by
  let N : ℂ := suzukiXiZeroNormalization rho
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast (suzukiXiZeroNormalization_pos rho).ne'
  apply (memLp_congr_ae ?_).mp
    ((memLp_two_suzukiRealAxisZeroFunction rho).const_mul N⁻¹)
  filter_upwards with x
  change N⁻¹ * (N * suzukiRealAxisXiZeroCarrier x /
    ((x : ℂ) - zetaSpectralCoordinate rho.1)) = _
  field_simp [hN]

private theorem ae_ofReal_ne (a : ℂ) : ∀ᵐ x : ℝ, (x : ℂ) ≠ a := by
  have hne : ∀ᵐ x : ℝ, x ≠ a.re := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using
      (measure_singleton a.re : volume ({a.re} : Set ℝ) = 0)
  filter_upwards [hne] with x hx hxa
  exact hx (by simpa using congrArg Complex.re hxa)

/-- Distinct genuine nodes give an absolutely integrable separated carrier
entry, even when either or both nodes are real. A safe resolvent preserves
the cancellation of the two tails before integration. -/
theorem integrable_suzukiXiCarrier_two_resolvents_of_ne
    (rho sigma : NontrivialZetaZero)
    (hne : zetaSpectralCoordinate rho.1 ≠ zetaSpectralCoordinate sigma.1) :
    Integrable (fun x : ℝ ↦ suzukiRealAxisXiZeroCarrier x /
      (((x : ℂ) - zetaSpectralCoordinate rho.1) *
        ((x : ℂ) - zetaSpectralCoordinate sigma.1))) := by
  let a := zetaSpectralCoordinate rho.1
  let b := zetaSpectralCoordinate sigma.1
  have hi := memLp_two_suzukiRealAxisCauchyKernel_of_im_ne_zero
    (show I.im ≠ 0 by simp)
  have hr := ((memLp_carrier_resolvent rho).integrable_mul hi).const_mul (a - I)
  have hs := ((memLp_carrier_resolvent sigma).integrable_mul hi).const_mul (b - I)
  apply ((hr.sub hs).div_const (a - b)).congr
  filter_upwards [ae_ofReal_ne a, ae_ofReal_ne b] with x hxa hxb
  have hxi : (x : ℂ) - I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
  have hab : a - b ≠ 0 := sub_ne_zero.mpr hne
  change ((a - I) * (suzukiRealAxisXiZeroCarrier x / ((x : ℂ) - a) * (1 / ((x : ℂ) - I))) -
    (b - I) * (suzukiRealAxisXiZeroCarrier x / ((x : ℂ) - b) * (1 / ((x : ℂ) - I)))) /
    (a - b) = suzukiRealAxisXiZeroCarrier x / (((x : ℂ) - a) * ((x : ℂ) - b))
  field_simp [sub_ne_zero.mpr hxa, sub_ne_zero.mpr hxb, hxi, hab]
  ring

/-- The separated carrier is absolutely integrable for every two-node
entry except a repeated real node, the case handled by the principal value. -/
theorem integrable_suzukiXiCarrier_two_resolvents_of_no_real_collision
    (rho sigma : NontrivialZetaZero)
    (h : zetaSpectralCoordinate rho.1 ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) :
    Integrable (fun x : ℝ ↦ suzukiRealAxisXiZeroCarrier x /
      (((x : ℂ) - zetaSpectralCoordinate rho.1) *
        ((x : ℂ) - zetaSpectralCoordinate sigma.1))) := by
  rcases h with hne | him
  · exact integrable_suzukiXiCarrier_two_resolvents_of_ne rho sigma hne
  · apply ((memLp_carrier_resolvent rho).integrable_mul
      (memLp_two_suzukiRealAxisCauchyKernel_of_im_ne_zero him)).congr
    exact Eventually.of_forall fun x ↦ by
      change suzukiRealAxisXiZeroCarrier x / _ * (1 / _) = _
      simp only [div_eq_mul_inv, mul_inv, one_mul, mul_assoc]

/-- The reflected separated channel has the same integrability domain,
with both node reflections retained. -/
theorem integrable_suzukiXiSharpCarrier_two_resolvents_of_no_real_collision
    (rho sigma : NontrivialZetaZero)
    (h : zetaSpectralCoordinate rho.1 ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) :
    Integrable (fun x : ℝ ↦ suzukiXiSharpCarrier (x : ℂ) /
      (((x : ℂ) - zetaSpectralCoordinate rho.1) *
        ((x : ℂ) - zetaSpectralCoordinate sigma.1))) := by
  have hpartner :
      zetaSpectralCoordinate (NontrivialZetaZero.conjugatePartner rho).1 ≠
          zetaSpectralCoordinate (NontrivialZetaZero.conjugatePartner sigma).1 ∨
      (zetaSpectralCoordinate (NontrivialZetaZero.conjugatePartner sigma).1).im ≠ 0 := by
    simp only [NontrivialZetaZero.spectralCoordinate_conjugatePartner,
      Complex.conj_im, neg_ne_zero]
    rcases h with hne | him
    · exact Or.inl fun hc ↦ hne (by simpa using congrArg (starRingEnd ℂ) hc)
    · exact Or.inr him
  have hf := integrable_suzukiXiCarrier_two_resolvents_of_no_real_collision
    (NontrivialZetaZero.conjugatePartner rho)
    (NontrivialZetaZero.conjugatePartner sigma) hpartner
  apply ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf).congr
  filter_upwards with x
  change starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x / _) = _
  rw [map_div₀, map_mul]
  simp only [NontrivialZetaZero.spectralCoordinate_conjugatePartner,
    map_sub, Complex.conj_ofReal, starRingEnd_self_apply, suzukiXiSharpCarrier_ofReal]

/-- Every mixed Gram entry without a repeated real denominator has a
genuine split into the two ordinary channel integrals. No reflected-pair
entry is replaced by a diagonal approximation. -/
theorem suzukiXiBoundaryCarrierGramKernel_eq_separated_integrals
    (rho sigma : NontrivialZetaZero)
    (h : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate sigma.1 ∨
      (zetaSpectralCoordinate sigma.1).im ≠ 0) :
    suzukiXiBoundaryCarrierGramKernel rho sigma =
      ((∫ x : ℝ, suzukiRealAxisXiZeroCarrier x /
        (((x : ℂ) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          ((x : ℂ) - zetaSpectralCoordinate sigma.1))) -
      (∫ x : ℝ, suzukiXiSharpCarrier (x : ℂ) /
        (((x : ℂ) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          ((x : ℂ) - zetaSpectralCoordinate sigma.1)))) / (2 * I) := by
  have hp : zetaSpectralCoordinate (NontrivialZetaZero.conjugatePartner rho).1 ≠
      zetaSpectralCoordinate sigma.1 ∨ (zetaSpectralCoordinate sigma.1).im ≠ 0 := by
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] using h
  have hf := integrable_suzukiXiCarrier_two_resolvents_of_no_real_collision
    (NontrivialZetaZero.conjugatePartner rho) sigma hp
  have hg := integrable_suzukiXiSharpCarrier_two_resolvents_of_no_real_collision
    (NontrivialZetaZero.conjugatePartner rho) sigma hp
  simp only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] at hf hg
  rw [suzukiXiBoundaryCarrierGramKernel_eq_continuation_integral]
  calc
    _ = ∫ x : ℝ, (suzukiRealAxisXiZeroCarrier x /
        (((x : ℂ) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          ((x : ℂ) - zetaSpectralCoordinate sigma.1)) -
      suzukiXiSharpCarrier (x : ℂ) /
        (((x : ℂ) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          ((x : ℂ) - zetaSpectralCoordinate sigma.1))) / (2 * I) := by
      apply integral_congr_ae
      filter_upwards with x
      unfold suzukiXiCarrierGramContinuation suzukiRealAxisXiZeroCarrier
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ = _ := by rw [integral_div, integral_sub hf hg]

/-- The other real-node principal value also exists and is exactly the
conjugate of the first one, with the common pole coefficient unchanged. -/
theorem tendsto_suzukiXiRealNode_sharp_principalValue
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    Tendsto (fun e : ℝ ↦
      ∫ x in {x : ℝ | e ≤ |x - (zetaSpectralCoordinate rho.1).re|},
        suzukiXiSharpCarrier (x : ℂ) / ((x : ℂ) - zetaSpectralCoordinate rho.1) ^ 2)
      (𝓝[>] 0) (𝓝 (starRingEnd ℂ (∫ x : ℝ, suzukiXiRealNodeRegularizedChannel rho x))) := by
  have ht := Complex.continuous_conj.continuousAt.tendsto.comp
    (tendsto_suzukiXiRealNode_principalValue rho hrho)
  apply ht.congr'
  filter_upwards with e
  rw [Function.comp_apply, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  have ha : starRingEnd ℂ (zetaSpectralCoordinate rho.1) = zetaSpectralCoordinate rho.1 :=
    Complex.conj_eq_iff_im.mpr hrho
  rw [map_div₀, map_pow, map_sub, Complex.conj_ofReal, ha, suzukiXiSharpCarrier_ofReal]

end
end RiemannGaussian

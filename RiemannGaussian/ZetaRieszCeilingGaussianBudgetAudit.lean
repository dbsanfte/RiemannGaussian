/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingAllHeightMultiplicity

/-!
# A fixed-strip gate for the complete positive Gaussian budget

The preceding all-height simplicity curve is a genuine arithmetic payment,
but it must not be mistaken for a way to close the fixed candidate strip.
Here the SAME complete explicit budget is audited at its weakest multiple
source: multiplicity two and real part `19999/20000`.

At order nine, every allowed dilation and every summable nonnegative
coefficient family obeys the bounds `40001*mass a` on the earlier source
certificate and `(25/1023)*mass a*log(abs t+2)` below the ACTUAL budget.

More strongly, every derivative line reaching the fixed boundary has
index at most sixteen. The exact cotangent source, not only its earlier
lower certificate, is at most `280000*mass a`, including the full positive
Poisson reserve; the literal budget is at least `mass a*log(abs t+2)/45`.
Thus a single-double-source surplus requires log-height below `12600000`,
uniformly over the stated dilation and phase families. These are lower
bounds on the budget itself, not on its previously used upper majorant.

This is a no-go for that specified positive-budget certificate, not for the
SIGNED Gaussian formula, additional coupled zero sources, the literal
Riesz ceiling, or RH. It supplies no new arithmetic ceiling credit.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real MeasureTheory Set
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingGaussianBudgetAudit
open ZetaGaussianScaledBandBudget (width shift gaussianScale)
open ZetaGaussianExpandedScale GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds
open ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily ZetaStripEulerConstraint
open ZetaAngularPhaseAllowance DerivativeOrderComparison
open ZetaNearOneBudgetLimit (scale)
open GaussianFermiZeroPair GaussianFermiGaussianMixture

/-- The true Gaussian half transform at positive damping is bounded by
the exponential integral, at EVERY positive Gaussian scale. -/
theorem halfGaussian_le_recip {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    halfGaussian b x <= 1/x := by
  have he : (∫ u in Ioi (0 : ℝ), Real.exp (-x*u)) = 1/x := by
    simpa using integral_exp_mul_Ioi (neg_neg_of_pos hx) 0
  rw [halfGaussian, <-he]
  apply integral_mono (integrable_window_exp hb x).integrableOn
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hx) 0)
  intro u
  apply mul_le_of_le_one_left (Real.exp_pos _).le
  unfold window
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg u]

/-- A single nonconstant coefficient never exceeds the complete
nonconstant mass, even for an infinite eligible family. -/
theorem first_le_mass {a : ℕ -> ℝ} (ha : ∀ n, 0 <= a n) (hs : Summable a) :
    a 1 <= mass a := by
  simpa only [tail, if_false, show (1 : ℕ) ≠ 0 by omega, mass] using
    (tail_summable ha hs).le_tsum 1 (fun n _ => tail_nonneg ha n)

/-- The full nonconstant logarithmic frequency cost is nonnegative.
No finite support or optimized coefficient row is assumed. -/
theorem frequencyCost_nonneg {a ω : ℕ -> ℝ} (ha : ∀ n, 0 <= a n)
    (hω : ∀ n, n ≠ 0 -> 1 <= ω n) : 0 <= frequencyCost a ω := by
  apply tsum_nonneg
  intro n
  by_cases hn : n = 0
  · simp [tail, hn]
  exact mul_nonneg (tail_nonneg ha n) (Real.log_nonneg (hω n hn))

/-- The literal existing left allowance has this height lower bound.
This does NOT lower-bound the actual signed clipped left mean. -/
theorem left_allowance_ge_height {t b : ℝ} (hL : 1 <= scale t) :
    scale t/2046 <= ZetaClippedEulerMean.allowance 9 t b := by
  have hc : 0 <= Real.log (8192 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : 0 <= Real.log (scale t) := Real.log_nonneg hL
  have hs := mul_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) <= 2))
    (ZetaLogarithmicShiftAllowance.shiftCost_nonneg 9 t b)
  unfold ZetaClippedEulerMean.allowance ZetaEulerLogProfile.profile
  norm_num [DerivativePowerExponents.alpha]
  change scale t/2046 <= Real.log 8192+(1/2046)*scale t+Real.log (scale t)+_
  linarith

/-- The height term in the literal allowance survives at every derivative
order. This is a budget statement, not an estimate of the signed mean. -/
theorem left_allowance_ge_linear (k : ℕ) {t b : ℝ} (hL : 1 <= scale t) :
    DerivativePowerExponents.alpha k*scale t <=
      ZetaClippedEulerMean.allowance k t b := by
  have hc : 0 <= Real.log (8192 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : 0 <= Real.log (scale t) := Real.log_nonneg hL
  have hs := mul_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) <= 2))
    (ZetaLogarithmicShiftAllowance.shiftCost_nonneg k t b)
  unfold ZetaClippedEulerMean.allowance ZetaEulerLogProfile.profile
  change DerivativePowerExponents.alpha k*scale t <=
    Real.log 8192+DerivativePowerExponents.alpha k*scale t+Real.log (scale t)+_
  linarith

/-- Extract the complete left allowance from the ACTUAL explicit budget.
All the other terms are nonnegative. No phase optimization, coefficient
search or upper majorant is involved in this lower bound. -/
theorem budget_ge_left {a ω : ℕ -> ℝ} (ha : ∀ n, 0 <= a n)
    (hω : ∀ n, n ≠ 0 -> 1 <= ω n) (k : ℕ) {B x t : ℝ}
    (hB : 0 < B) (hx : 0 < x) :
    mass a*ZetaClippedEulerMean.allowance k t (verticalScale k x)/(2*halfWidth k x)
      <= budget k B x t a ω := by
  have ha0 := ha 0
  have hη := halfWidth_pos k hx
  have hD : 0 < delta k+2*x := by linarith [delta_pos k]
  have hright := rightLine_gt_one k hx
  have hfactor : 0 <= factor k B x := by unfold factor; positivity
  have hmass : 0 <= mass a := tsum_nonneg (tail_nonneg ha)
  have hfreq := frequencyCost_nonneg ha hω
  have hG : 0 <= halfGaussian B x := halfGaussian_nonneg _ _
  have hcomp := GaussianPolynomialTransport.mass_pos hB
  have hlog1 : 0 <= Real.log (1+x) := Real.log_nonneg (by linarith)
  have hlocal : 0 <= localZetaLogHeight 0 := by
    apply Real.log_nonneg
    norm_num [localZetaLogHeight]
  have hlog2 : 0 <= Real.log (1+1/(delta k+2*x)) :=
    Real.log_nonneg (by linarith [one_div_pos.mpr hD])
  have hrat := RationalVerticalCorrection.profile_nonneg
    (by linarith : 0 <= rightLine k x) (by linarith : rightLine k x ≠ 1) 0
  have hlogright : 0 <= Real.log (rightLine k x+|t|) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  have hconstant : 0 <= a 0 * (halfGaussian B x+
      Real.log (1+x)/2+4*B/GaussianPolynomialTransport.mass B+
      factor k B x*(1/(delta k+2*x)+448*localZetaLogHeight 0)+
      Real.log (1+1/(delta k+2*x))/(2*halfWidth k x)) := by positivity
  have hextra : 0 <= mass a*(12*B/|t|^3+
      4*B/GaussianPolynomialTransport.mass B) := by positivity
  have hresponse : 0 <= factor k B x *
      (mass a*((delta k+2*x)/t^2+Real.log (rightLine k x+|t|)/2)+
        frequencyCost a ω/2) := by positivity
  have hratterms : 0 <= 8*rightLine k x/t^2+
      2*RationalVerticalCorrection.profile (rightLine k x) 0*
        Real.exp (-|t|/|verticalScale k x|) := by positivity
  have hnum : mass a*ZetaClippedEulerMean.allowance k t (verticalScale k x) <=
      mass a*(ZetaClippedEulerMean.allowance k t (verticalScale k x)+
        8*rightLine k x/t^2+2*RationalVerticalCorrection.profile (rightLine k x) 0*
          Real.exp (-|t|/|verticalScale k x|))+2*frequencyCost a ω := by
    nlinarith only [mul_nonneg hmass hratterms, hfreq]
  have hboundary := div_le_div_of_nonneg_right hnum
    (by positivity : 0 <= 2*halfWidth k x)
  unfold budget
  linarith only [hconstant, hextra, hresponse, hboundary]

/-- The ACTUAL complete explicit positive budget has a linearly growing
height price at every dilation. All its other components are nonnegative.
This is not an inference from the upper bound used in earlier payments. -/
theorem budget_ge_height {a ω : ℕ -> ℝ} (ha : ∀ n, 0 <= a n)
    (hω : ∀ n, n ≠ 0 -> 1 <= ω n) {q t : ℝ} (hq : 9/100 <= q)
    (hL : 1 <= scale t) :
    (25/1023)*mass a*scale t <= budget 9 (gaussianScale q) (shift q) t a ω := by
  have hx := (ZetaGaussianExpandedScale.shift_bounds hq).1
  have hB := (ZetaGaussianExpandedScale.gaussianScale_bounds hq).1
  have hη := (ZetaGaussianExpandedScale.geometry hq).1
  have hηu := (ZetaGaussianExpandedScale.geometry hq).2.1
  have hmass : 0 <= mass a := tsum_nonneg (tail_nonneg ha)
  have hallowance := left_allowance_ge_height (b := verticalScale 9 (shift q)) hL
  have hboundary := (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hallowance hmass)
    (by positivity : 0 <= 2*halfWidth 9 (shift q))).trans
    (budget_ge_left ha hω 9 hB hx)
  have hi : (50 : ℝ) <= 1/(2*halfWidth 9 (shift q)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*halfWidth 9 (shift q))).mpr
    linarith
  have hlower := mul_le_mul_of_nonneg_left hi
    (show 0 <= mass a*(scale t/2046) by positivity)
  rw [mul_one_div] at hlower
  nlinarith only [hboundary, hlower]

/-- At the fixed candidate boundary the entire hypothetical double-zero
source is bounded, at ALL allowed Gaussian dilations. The positive
Poisson reserve is bounded rather than omitted. -/
theorem double_boundary_source_le {a : ℕ -> ℝ} (ha : ∀ n, 0 <= a n)
    (hs : Summable a) {q : ℝ} (hq : 9/100 <= q) :
    a 1 * (2*(halfGaussian (gaussianScale q) (shift q+1/20000)-
        Real.pi^2*(shift q+1/20000)/(8*halfWidth 9 (shift q)^2))+
      factor 9 (gaussianScale q) (shift q)*(2/(shift q+1/20000+halfWidth 9 (shift q)))) <=
      40001*mass a := by
  have hx := (ZetaGaussianExpandedScale.shift_bounds hq).1
  have hB := (ZetaGaussianExpandedScale.gaussianScale_bounds hq).1
  have hη := (ZetaGaussianExpandedScale.geometry hq).1
  have hx0 : 0 < shift q+1/20000 := by linarith
  have hG : halfGaussian (gaussianScale q) (shift q+1/20000) <= 20000 := by
    apply (halfGaussian_le_recip hB hx0).trans
    apply (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/20000)
      (by linarith : 1/20000 <= shift q+1/20000)).trans_eq
    norm_num
  have hcot : 0 <= Real.pi^2*(shift q+1/20000)/(8*halfWidth 9 (shift q)^2) := by positivity
  have hreserve : factor 9 (gaussianScale q) (shift q)*
      (2/(shift q+1/20000+halfWidth 9 (shift q))) <= 1 := by
    calc
      _ <= (1/400 : ℝ)*(2/(1/200)) := by
        gcongr
        · exact (ZetaGaussianExpandedScale.factor_bounds hq).2
        · linarith
      _ = _ := by norm_num
  have hsource : 2*(halfGaussian (gaussianScale q) (shift q+1/20000)-
        Real.pi^2*(shift q+1/20000)/(8*halfWidth 9 (shift q)^2))+
      factor 9 (gaussianScale q) (shift q)*(2/(shift q+1/20000+halfWidth 9 (shift q))) <= 40001 := by
    linarith only [hG, hcot, hreserve]
  have hw := mul_le_mul_of_nonneg_left hsource (ha 1)
  have hm := mul_le_mul_of_nonneg_left (first_le_mass ha hs) (by norm_num : (0 : ℝ) <= 40001)
  linarith only [hw, hm]

/-- At log-height at least two million the ACTUAL explicit allowance
dominates the fixed-boundary double source by at least 8000 times the
entire nonconstant mass. No scale or coefficient-family search can undo
this. It gives ZERO arithmetic credit for the Riesz ceiling. -/
theorem budget_dominates_double_boundary {a ω : ℕ -> ℝ} (ha : ∀ n, 0 <= a n)
    (hs : Summable a) (hω : ∀ n, n ≠ 0 -> 1 <= ω n) {q t : ℝ}
    (hq : 9/100 <= q) (hL : 2000000 <= scale t) :
    a 1 * (2*(halfGaussian (gaussianScale q) (shift q+1/20000)-
        Real.pi^2*(shift q+1/20000)/(8*halfWidth 9 (shift q)^2))+
      factor 9 (gaussianScale q) (shift q)*(2/(shift q+1/20000+halfWidth 9 (shift q))))+
      8000*mass a <= budget 9 (gaussianScale q) (shift q) t a ω := by
  have hm : 0 <= mass a := tsum_nonneg (tail_nonneg ha)
  have hb := budget_ge_height ha hω hq (by linarith : 1 <= scale t)
  have hs' := double_boundary_source_le ha hs hq
  have hprice : (48001 : ℝ) <= (25/1023)*scale t := by linarith only [hL]
  have hp := mul_le_mul_of_nonneg_right hprice hm
  nlinarith only [hb, hs', hp]

/-- Any strict surplus for the weakest multiple source at the fixed
strip boundary necessarily lies below this explicit log-height ceiling,
for EVERY allowed dilation and every eligible countable family. This
is a necessary limit of the stated budget, not a maximal valid height. -/
theorem surplus_log_height_bound {a ω : ℕ -> ℝ} (ha : ∀ n, 0 <= a n)
    (hs : Summable a) (ha1 : 0 < a 1) (hω : ∀ n, n ≠ 0 -> 1 <= ω n)
    {q t : ℝ} (hq : 9/100 <= q) (hL : 1 <= scale t)
    (hsurplus : budget 9 (gaussianScale q) (shift q) t a ω <
      a 1 * (2*(halfGaussian (gaussianScale q) (shift q+1/20000)-
        Real.pi^2*(shift q+1/20000)/(8*halfWidth 9 (shift q)^2))+
      factor 9 (gaussianScale q) (shift q)*(2/(shift q+1/20000+halfWidth 9 (shift q))))) :
    scale t < 40921023/25 := by
  have hm : 0 < mass a := ha1.trans_le (first_le_mass ha hs)
  have hb := budget_ge_height ha hω hq hL
  have hu := double_boundary_source_le ha hs hq
  have h : (25/1023)*mass a*scale t < 40001*mass a := hb.trans_lt (hsurplus.trans_le hu)
  have he : mass a*((25/1023)*scale t) < mass a*40001 := by nlinarith only [h]
  have hc := (mul_lt_mul_iff_right₀ hm).mp he
  linarith only [hc]

/-- No balanced derivative line of index seventeen or higher reaches the
fixed candidate boundary. This is the exact repository exponent, with
denominator `2^(k+2)-2`, not a shifted numerical convention. -/
theorem boundary_order_le {k : ℕ}
    (hline : DirichletPowerParameters.line k < 19999/20000) : k <= 16 := by
  have he := delta_eq_one_sub_line k
  by_contra hk
  have hd := delta_antitone (by omega : 17 <= k)
  have h17 : delta 17 = 1/27594 := by norm_num [delta, DerivativePowerExponents.alpha]
  rw [h17] at hd
  linarith

/-- Every derivative strip that reaches the candidate boundary has a
uniformly positive half-width. All lower orders are included. -/
theorem boundary_halfWidth_lower {k : ℕ}
    (hline : DirichletPowerParameters.line k < 19999/20000)
    {x : ℝ} (hx : 0 < x) : 1/15000 <= halfWidth k x := by
  have hd := delta_antitone (boundary_order_le hline)
  have h16 : delta 16 = 9/131071 := by norm_num [delta, DerivativePowerExponents.alpha]
  rw [h16] at hd
  unfold halfWidth
  linarith

/-- Every admissible derivative order pays at least `L/45` per unit
nonconstant mass in the literal positive budget. The shift condition is
exactly the condition required by the existing source theorem. -/
theorem budget_ge_height_all_orders {a ω : ℕ -> ℝ} (ha : ∀ n, 0 <= a n)
    (hω : ∀ n, n ≠ 0 -> 1 <= ω n) {k : ℕ} {B x t : ℝ}
    (hB : 0 < B) (hx : 0 < x) (hx' : x <= delta k/4)
    (hline : DirichletPowerParameters.line k < 19999/20000)
    (hL : 1 <= scale t) :
    mass a*scale t/45 <= budget k B x t a ω := by
  have hη := halfWidth_pos k hx
  have hα := DerivativePowerExponents.alpha_pos k
  have hk : (k : ℝ) <= 16 := by exact_mod_cast boundary_order_le hline
  have hδ : delta k <= 18*DerivativePowerExponents.alpha k := by
    unfold delta
    nlinarith
  have hηu : 2*halfWidth k x <= 45*DerivativePowerExponents.alpha k := by
    unfold halfWidth
    linarith
  have hratio : (1/45 : ℝ) <= DerivativePowerExponents.alpha k/(2*halfWidth k x) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*halfWidth k x)).mpr
    linarith
  have hm : 0 <= mass a := tsum_nonneg (tail_nonneg ha)
  have hp := mul_le_mul_of_nonneg_right hratio
    (show 0 <= mass a*scale t by positivity)
  have hal := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (left_allowance_ge_linear k (b := verticalScale k x) hL) hm)
    (by positivity : 0 <= 2*halfWidth k x)
  have hb := budget_ge_left ha hω k (t := t) hB hx
  calc
    mass a*scale t/45 <=
      (DerivativePowerExponents.alpha k/(2*halfWidth k x))*(mass a*scale t) := by
        linarith only [hp]
    _ = mass a*(DerivativePowerExponents.alpha k*scale t)/(2*halfWidth k x) := by ring
    _ <= _ := hal.trans hb

/-- The Gaussian-plus-reserve envelope of the complete double source is
uniformly bounded for ALL derivative lines reaching the fixed boundary
and ALL dilations in the existing normalized scale family. -/
theorem double_envelope_le_all_orders {a : ℕ -> ℝ}
    (ha : ∀ n, 0 <= a n) (hs : Summable a) {k : ℕ} {q : ℝ}
    (hq : 9/100 <= q) (hline : DirichletPowerParameters.line k < 19999/20000) :
    a 1 * (2*halfGaussian (gaussianScale q) (shift q+1/20000)+
      factor k (gaussianScale q) (shift q)*
        (2/(shift q+1/20000+halfWidth k (shift q)))) <= 280000*mass a := by
  have hx := (ZetaGaussianExpandedScale.shift_bounds hq).1
  obtain ⟨hB,hBu⟩ := ZetaGaussianExpandedScale.gaussianScale_bounds hq
  have hη := boundary_halfWidth_lower hline hx
  have hη0 : 0 < halfWidth k (shift q) := by linarith
  have hx0 : 0 < shift q+1/20000 := by linarith
  have hG : halfGaussian (gaussianScale q) (shift q+1/20000) <= 20000 := by
    apply (halfGaussian_le_recip hB hx0).trans
    apply (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/20000)
      (by linarith : 1/20000 <= shift q+1/20000)).trans_eq
    norm_num
  have hfactor : factor k (gaussianScale q) (shift q) <= 14 := by
    unfold factor
    apply (div_le_iff₀ (sq_pos_of_pos hη0)).mpr
    nlinarith only [hBu, hη, sq_nonneg (halfWidth k (shift q)-1/15000)]
  have hfactor0 : 0 <= factor k (gaussianScale q) (shift q) := by
    unfold factor
    positivity
  have hreserve : factor k (gaussianScale q) (shift q)*
      (2/(shift q+1/20000+halfWidth k (shift q))) <= 240000 := by
    calc
      _ <= (14 : ℝ)*(2/(1/20000+1/15000)) := by
        gcongr
        linarith
      _ = _ := by norm_num
  have hsource : 2*halfGaussian (gaussianScale q) (shift q+1/20000)+
      factor k (gaussianScale q) (shift q)*
        (2/(shift q+1/20000+halfWidth k (shift q))) <= 280000 := by
    linarith only [hG, hreserve]
  have hw := mul_le_mul_of_nonneg_left hsource (ha 1)
  have hm := mul_le_mul_of_nonneg_left (first_le_mass ha hs)
    (by norm_num : (0 : ℝ) <= 280000)
  linarith only [hw, hm]

/-- The cotangent-minus-pole correction has nonpositive sign on the
entire real interior of the selected strip. No small-angle approximation
is used, so sharpening its earlier lower bound cannot escape this gate. -/
theorem scaled_cot_real_nonpos {η v : ℝ} (hη : 0 < η) (hv : 0 < v) (hvη : v < η) :
    CotangentRegularization.frequency η *
        Real.cot (CotangentRegularization.frequency η*v)-1/v <= 0 := by
  let f := CotangentRegularization.frequency η
  have hf : 0 < f := by
    dsimp [f,CotangentRegularization.frequency]
    exact div_pos Real.pi_pos (by positivity)
  have hy : 0 < f*v := mul_pos hf hv
  have hyu : f*v < Real.pi/2 := by
    calc
      f*v < f*η := mul_lt_mul_of_pos_left hvη hf
      _ = _ := by dsimp [f,CotangentRegularization.frequency]; field_simp
  have hsin := Real.sin_pos_of_pos_of_lt_pi hy (by linarith [Real.pi_pos])
  have hcos := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hyu⟩
  have htan : f*v <= Real.sin (f*v)/Real.cos (f*v) := by
    simpa only [Real.tan_eq_sin_div_cos] using Real.le_tan hy.le hyu
  have hm := (le_div_iff₀ hcos).mp htan
  have hc : Real.cot (f*v) <= 1/(f*v) := by
    rw [Real.cot_eq_cos_div_sin]
    apply (div_le_div_iff₀ hsin hy).mpr
    nlinarith only [hm]
  have hp := mul_le_mul_of_nonneg_left hc hf.le
  have he : f*(1/(f*v))=1/v := by field_simp
  rw [he] at hp
  linarith only [hp]

/-- The source used by the earlier checked Gaussian certificate satisfies
this gate at every reaching derivative order. -/
theorem double_boundary_source_le_all_orders {a : ℕ -> ℝ}
    (ha : ∀ n, 0 <= a n) (hs : Summable a) {k : ℕ} {q : ℝ}
    (hq : 9/100 <= q) (hline : DirichletPowerParameters.line k < 19999/20000) :
    a 1 * (2*(halfGaussian (gaussianScale q) (shift q+1/20000)-
        Real.pi^2*(shift q+1/20000)/(8*halfWidth k (shift q)^2))+
      factor k (gaussianScale q) (shift q)*
        (2/(shift q+1/20000+halfWidth k (shift q)))) <= 280000*mass a := by
  have hx := (ZetaGaussianExpandedScale.shift_bounds hq).1
  have hcot : 0 <= Real.pi^2*(shift q+1/20000)/(8*halfWidth k (shift q)^2) := by positivity
  have hsmall := mul_le_mul_of_nonneg_left
    (show 2*(halfGaussian (gaussianScale q) (shift q+1/20000)-
        Real.pi^2*(shift q+1/20000)/(8*halfWidth k (shift q)^2))+
        factor k (gaussianScale q) (shift q)*
          (2/(shift q+1/20000+halfWidth k (shift q))) <=
      2*halfGaussian (gaussianScale q) (shift q+1/20000)+
        factor k (gaussianScale q) (shift q)*
          (2/(shift q+1/20000+halfWidth k (shift q))) by linarith only [hcot]) (ha 1)
  exact hsmall.trans (double_envelope_le_all_orders ha hs hq hline)

/-- The EXACT cotangent source obeys the same all-order envelope. This
is the real expression in `compensated_at_ordinate`, retaining its full
positive Poisson reserve and every analytic multiplicity when instantiated. -/
theorem exact_double_boundary_source_le {a : ℕ -> ℝ}
    (ha : ∀ n, 0 <= a n) (hs : Summable a) {k : ℕ} {q : ℝ}
    (hq : 9/100 <= q) (hline : DirichletPowerParameters.line k < 19999/20000) :
    a 1 * (2*(halfGaussian (gaussianScale q) (shift q+1/20000)+
        CotangentRegularization.frequency (halfWidth k (shift q))*
          Real.cot (CotangentRegularization.frequency (halfWidth k (shift q))*(shift q+1/20000))-
        1/(shift q+1/20000))+
      factor k (gaussianScale q) (shift q)*
        (2/(shift q+1/20000+halfWidth k (shift q)))) <= 280000*mass a := by
  have hx := (ZetaGaussianExpandedScale.shift_bounds hq).1
  have hη := halfWidth_pos k hx
  have he := delta_eq_one_sub_line k
  have hvη : shift q+1/20000 < halfWidth k (shift q) := by
    unfold halfWidth
    linarith only [hline,he]
  have hc := scaled_cot_real_nonpos hη (by linarith : 0 < shift q+1/20000) hvη
  have hsmall := mul_le_mul_of_nonneg_left
    (show 2*(halfGaussian (gaussianScale q) (shift q+1/20000)+
        CotangentRegularization.frequency (halfWidth k (shift q))*
          Real.cot (CotangentRegularization.frequency (halfWidth k (shift q))*(shift q+1/20000))-
        1/(shift q+1/20000))+
        factor k (gaussianScale q) (shift q)*
          (2/(shift q+1/20000+halfWidth k (shift q))) <=
      2*halfGaussian (gaussianScale q) (shift q+1/20000)+
        factor k (gaussianScale q) (shift q)*
          (2/(shift q+1/20000+halfWidth k (shift q))) by linarith only [hc]) (ha 1)
  exact hsmall.trans (double_envelope_le_all_orders ha hs hq hline)

/-- No derivative-order, dilation or eligible coefficient-family tuning
of this complete positive budget closes the fixed boundary at all heights.
At the stated height the price exceeds the entire double source by at
least `20000*mass a`. No signed arithmetic ceiling credit follows. -/
theorem budget_dominates_double_boundary_all_orders {a ω : ℕ -> ℝ}
    (ha : ∀ n, 0 <= a n) (hs : Summable a) (hω : ∀ n, n ≠ 0 -> 1 <= ω n)
    {k : ℕ} {q t : ℝ} (hq : 9/100 <= q)
    (hx' : shift q <= delta k/4)
    (hline : DirichletPowerParameters.line k < 19999/20000)
    (hL : 13500000 <= scale t) :
    a 1 * (2*(halfGaussian (gaussianScale q) (shift q+1/20000)+
        CotangentRegularization.frequency (halfWidth k (shift q))*
          Real.cot (CotangentRegularization.frequency (halfWidth k (shift q))*(shift q+1/20000))-
        1/(shift q+1/20000))+
      factor k (gaussianScale q) (shift q)*
        (2/(shift q+1/20000+halfWidth k (shift q))))+20000*mass a
      <= budget k (gaussianScale q) (shift q) t a ω := by
  have hm : 0 <= mass a := tsum_nonneg (tail_nonneg ha)
  have hb := budget_ge_height_all_orders ha hω
    (ZetaGaussianExpandedScale.gaussianScale_bounds hq).1
    (ZetaGaussianExpandedScale.shift_bounds hq).1 hx' hline (by linarith : 1 <= scale t)
  have hu := exact_double_boundary_source_le ha hs hq hline
  have hp := mul_le_mul_of_nonneg_right
    (show (300000 : ℝ) <= scale t/45 by linarith only [hL]) hm
  nlinarith only [hb, hu, hp]

/-- The fixed boundary has a finite necessary log-height ceiling for
EVERY admissible derivative order, dilation and summable phase family.
This does not assert a valid surplus below that ceiling. -/
theorem surplus_log_height_bound_all_orders {a ω : ℕ -> ℝ}
    (ha : ∀ n, 0 <= a n) (hs : Summable a) (ha1 : 0 < a 1)
    (hω : ∀ n, n ≠ 0 -> 1 <= ω n) {k : ℕ} {q t : ℝ}
    (hq : 9/100 <= q) (hx' : shift q <= delta k/4)
    (hline : DirichletPowerParameters.line k < 19999/20000) (hL : 1 <= scale t)
    (hsurplus : budget k (gaussianScale q) (shift q) t a ω <
      a 1 * (2*(halfGaussian (gaussianScale q) (shift q+1/20000)+
        CotangentRegularization.frequency (halfWidth k (shift q))*
          Real.cot (CotangentRegularization.frequency (halfWidth k (shift q))*(shift q+1/20000))-
        1/(shift q+1/20000))+
      factor k (gaussianScale q) (shift q)*
        (2/(shift q+1/20000+halfWidth k (shift q))))) : scale t < 12600000 := by
  have hm : 0 < mass a := ha1.trans_le (first_le_mass ha hs)
  have hb := budget_ge_height_all_orders ha hω
    (ZetaGaussianExpandedScale.gaussianScale_bounds hq).1
    (ZetaGaussianExpandedScale.shift_bounds hq).1 hx' hline hL
  have hu := exact_double_boundary_source_le ha hs hq hline
  have h : mass a*scale t/45 < 280000*mass a := hb.trans_lt (hsurplus.trans_le hu)
  have he : mass a*(scale t/45) < mass a*280000 := by nlinarith only [h]
  have hc := (mul_lt_mul_iff_right₀ hm).mp he
  linarith only [hc]

end RiemannGaussian.ZetaRieszCeilingGaussianBudgetAudit

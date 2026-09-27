/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCapacityCheck
import RiemannGaussian.ZetaRieszCapacityCover
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Complete cells in the favorable five-prime angular integral

The three pair caps are summed with their exact incidence factor before
the symmetric large-pair integration. The remaining two-dimensional
density keeps the curved ordering and saturation boundaries. Common
least-share fibres give lower bounds on whole outer cells, rather than
sampled values. These are integral budgets; the literal prime-population
comparison is a separate obligation.
-/

namespace RiemannGaussian.ZetaRieszFiveCapacityCover
open MeasureTheory ZetaRieszCapacityCover ZetaRieszOrderedCapacity
open scoped BigOperators Classical

/-- The surviving least-share integrand after the exact symmetric
large-pair integration. -/
noncomputable def fibre (lo hi v z r : ℝ) : ℝ :=
  let S := 1-v-z
  let d := max (S-r) (max (1-lo-z) (v-1/2))
  min r (max 0 (min (lo-v) (1-hi-z)))/(r*(S-r))*Real.log ((v-d)/d)

/-- Saturation conditions on the two outer shares. Every discarded outer
point contributes zero to this supply minorant. -/
def admissible (lo hi v z : ℝ) : Prop :=
  1-lo ≤ v ∧ hi ≤ v+z ∧ 2*(1-lo) ≤ v+2*z

/-- Exact five-prime supply density used in the ordered capacity test.
The least prime has share at least `eps`, and both small primes lie below
all three large primes. Empty fibres have integral zero. -/
noncomputable def density (lo hi eps : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  if admissible lo hi (x 0) (x 1) then
    (∫ r in Set.Ioc (max eps (max (1-x 0-x 1-x 1) (1-x 0-x 1-x 0/2)))
        ((1-x 0-x 1)/2), fibre lo hi (x 0) (x 1) r)/(hi*x 0*x 1)
  else 0

/-- Measurability includes every ordering and saturation boundary. -/
theorem measurable_density (lo hi eps : ℝ) : Measurable (density lo hi eps) := by
  classical
  let E : Set ((Fin 2 → ℝ) × ℝ) := {v |
    max eps (max (1-v.1 0-v.1 1-v.1 1) (1-v.1 0-v.1 1-v.1 0/2)) < v.2 ∧
      v.2 ≤ (1-v.1 0-v.1 1)/2}
  have hE : MeasurableSet E := by
    have hl : MeasurableSet {v : ((Fin 2 → ℝ) × ℝ) |
        max eps (max (1-v.1 0-v.1 1-v.1 1) (1-v.1 0-v.1 1-v.1 0/2)) < v.2} :=
      measurableSet_lt (by fun_prop) measurable_snd
    have hu : MeasurableSet {v : ((Fin 2 → ℝ) × ℝ) |
        v.2 ≤ (1-v.1 0-v.1 1)/2} :=
      measurableSet_le measurable_snd (by fun_prop)
    exact hl.inter hu
  have hg : Measurable (fun v : ((Fin 2 → ℝ) × ℝ) =>
      fibre lo hi (v.1 0) (v.1 1) v.2) := by
    unfold fibre
    fun_prop
  have hA : MeasurableSet {x : Fin 2 → ℝ | admissible lo hi (x 0) (x 1)} := by
    have h₁ : MeasurableSet {x : Fin 2 → ℝ | 1-lo ≤ x 0} :=
      measurableSet_le measurable_const (measurable_pi_apply 0)
    have h₂ : MeasurableSet {x : Fin 2 → ℝ | hi ≤ x 0+x 1} :=
      measurableSet_le measurable_const (by fun_prop)
    have h₃ : MeasurableSet {x : Fin 2 → ℝ | 2*(1-lo) ≤ x 0+2*x 1} :=
      measurableSet_le measurable_const (by fun_prop)
    exact h₁.inter (h₂.inter h₃)
  have hI : Measurable (fun x : Fin 2 → ℝ =>
      ∫ r : ℝ, E.indicator (fun v => fibre lo hi (v.1 0) (v.1 1) v.2) (x,r)) :=
    ((hg.indicator hE).stronglyMeasurable.integral_prod_right').measurable
  have he (x : Fin 2 → ℝ) :
      (∫ r : ℝ, E.indicator (fun v => fibre lo hi (v.1 0) (v.1 1) v.2) (x,r)) =
      ∫ r in Set.Ioc (max eps (max (1-x 0-x 1-x 1) (1-x 0-x 1-x 0/2)))
        ((1-x 0-x 1)/2), fibre lo hi (x 0) (x 1) r := by
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  have hd : density lo hi eps = {x : Fin 2 → ℝ | admissible lo hi (x 0) (x 1)}.indicator
      (fun x => (∫ r : ℝ, E.indicator
        (fun v => fibre lo hi (v.1 0) (v.1 1) v.2) (x,r))/(hi*x 0*x 1)) := by
    funext x
    change density lo hi eps x = if admissible lo hi (x 0) (x 1) then
      (∫ r : ℝ, E.indicator (fun v => fibre lo hi (v.1 0) (v.1 1) v.2) (x,r)) /
        (hi*x 0*x 1) else 0
    rw [he]
    rfl
  rw [hd]
  exact (hI.div (by fun_prop)).indicator hA

/-- The pair boundary stays strictly positive and below half the pair
share throughout the actual least-share fibre. -/
theorem pair_boundary_bounds {lo hi eps v z r : ℝ}
    (hv1 : v ≤ 1)
    (hA : admissible lo hi v z)
    (hr : max eps (max (1-v-z-z) (1-v-z-v/2)) ≤ r ∧ r ≤ (1-v-z)/2) :
    eps ≤ max (1-v-z-r) (max (1-lo-z) (v-1/2)) ∧
      max (1-v-z-r) (max (1-lo-z) (v-1/2)) ≤ v/2 := by
  have hrl : eps ≤ r := (le_max_left _ _).trans hr.1
  have hrv : 1-v-z-v/2 ≤ r :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hr.1)
  refine ⟨le_trans (by linarith [hr.2]) (le_max_left _ _),?_⟩
  apply max_le (by linarith)
  exact max_le (by linarith [hA.2.2]) (by linarith)

/-- The actual fibre is nonnegative; no negative logarithm is silently
replaced by its positive part. -/
theorem fibre_nonneg {lo hi eps v z r : ℝ}
    (heps : 0 < eps) (hv1 : v ≤ 1)
    (hA : admissible lo hi v z)
    (hr : max eps (max (1-v-z-z) (1-v-z-v/2)) ≤ r ∧ r ≤ (1-v-z)/2) :
    0 ≤ fibre lo hi v z r := by
  have hrl : 0 < r := heps.trans_le ((le_max_left _ _).trans hr.1)
  have hd := pair_boundary_bounds hv1 hA hr
  unfold fibre
  apply mul_nonneg
  · exact div_nonneg (le_min hrl.le (le_max_left _ _))
      (mul_nonneg hrl.le (by linarith [hr.2]))
  · apply Real.log_nonneg
    exact (le_div_iff₀ (heps.trans_le hd.1)).mpr (by linarith [hd.2])

/-- Every point of the symmetric large-pair interval satisfies the
literal ordering, one-half upper bounds and common saturation inequalities.
This is the geometry behind the positive three-cap atom estimate. -/
theorem pair_geometry {lo hi eps v z r x : ℝ} (hA : admissible lo hi v z)
    (hr : max eps (max (1-v-z-z) (1-v-z-v/2)) ≤ r ∧ r ≤ (1-v-z)/2)
    (hx : max (1-v-z-r) (max (1-lo-z) (v-1/2)) ≤ x ∧
      x ≤ v-max (1-v-z-r) (max (1-lo-z) (v-1/2))) :
    eps ≤ r ∧ r ≤ 1-v-z-r ∧
    1-v-z-r ≤ x ∧ 1-v-z-r ≤ v-x ∧ 1-v-z-r ≤ z ∧
    x ≤ 1/2 ∧ v-x ≤ 1/2 ∧
    x+(1-v-z) ≤ lo ∧ (v-x)+(1-v-z) ≤ lo ∧ z+(1-v-z) ≤ lo ∧
    hi ≤ x+(v-x)+z := by
  have hsmall := le_max_left (1-v-z-r) (max (1-lo-z) (v-1/2))
  have hcut := (le_max_left (1-lo-z) (v-1/2)).trans (le_max_right (1-v-z-r) _)
  have hhalf := (le_max_right (1-lo-z) (v-1/2)).trans (le_max_right (1-v-z-r) _)
  have hrz := (le_max_left (1-v-z-z) (1-v-z-v/2)).trans
    (le_max_right eps (max (1-v-z-z) (1-v-z-v/2)))
  refine ⟨(le_max_left _ _).trans hr.1,by linarith [hr.2],
    hsmall.trans hx.1,by linarith [hx.2],by linarith [hr.1],
    by linarith [hx.2],by linarith [hx.1],by linarith [hx.2],
    by linarith [hx.1],by linarith [hA.1],by linarith [hA.2.1]⟩

/-- The factor one half from the six ordered incidences cancels exactly
the factor two from integrating the symmetric pair. This identifies the
numerical fibre with the integrated normalized one-pair credit. -/
theorem fibre_eq_half_pair_integral {lo hi eps v z r : ℝ}
    (heps : 0 < eps) (hv1 : v ≤ 1) (hA : admissible lo hi v z)
    (hr : max eps (max (1-v-z-z) (1-v-z-v/2)) ≤ r ∧ r ≤ (1-v-z)/2) :
    fibre lo hi v z r/(hi*v*z) =
      (1/2)*(∫ x : ℝ in max (1-v-z-r) (max (1-lo-z) (v-1/2))..
          (v-max (1-v-z-r) (max (1-lo-z) (v-1/2))),
        min r (max 0 (min (lo-v) (1-hi-z)))/
          (hi*z*r*(1-v-z-r)*x*(v-x))) := by
  let d := max (1-v-z-r) (max (1-lo-z) (v-1/2))
  have hd := pair_boundary_bounds hv1 hA hr
  have hd0 : 0 < d := heps.trans_le hd.1
  have he : (fun x : ℝ => min r (max 0 (min (lo-v) (1-hi-z)))/
      (hi*z*r*(1-v-z-r)*x*(v-x))) =
      fun x => (min r (max 0 (min (lo-v) (1-hi-z)))/(hi*z*r*(1-v-z-r)))*
        (1/(x*(v-x))) := by
    funext x
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he,intervalIntegral.integral_const_mul,symmetric_pair_integral hd0 (by linarith [hd.2])]
  simp only [fibre,div_eq_mul_inv,mul_inv_rev]
  dsimp [d]
  ring

/-- The exact fibre is continuous on its closed ordering interval. The
positive least-share cutoff removes every possible denominator zero. -/
theorem continuousOn_fibre {lo hi eps v z : ℝ}
    (heps : 0 < eps) (hv1 : v ≤ 1) (hA : admissible lo hi v z) :
    ContinuousOn (fibre lo hi v z)
      (Set.Icc (max eps (max (1-v-z-z) (1-v-z-v/2))) ((1-v-z)/2)) := by
  let d : ℝ → ℝ := fun r => max (1-v-z-r) (max (1-lo-z) (v-1/2))
  have hd : Continuous d := by dsimp [d]; fun_prop
  have hb (r : ℝ)
      (hr : r ∈ Set.Icc (max eps (max (1-v-z-z) (1-v-z-v/2))) ((1-v-z)/2)) :
      0 < r ∧ 0 < 1-v-z-r ∧ 0 < d r ∧ 0 < v-d r := by
    have hrl : 0 < r := heps.trans_le ((le_max_left _ _).trans hr.1)
    have hb := pair_boundary_bounds hv1 hA hr
    have hd0 : 0 < d r := heps.trans_le hb.1
    exact ⟨hrl,by linarith [hr.2],hd0,by dsimp [d] at *; linarith [hb.2]⟩
  unfold fibre
  apply ContinuousOn.mul
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro r hr
    exact mul_ne_zero (hb r hr).1.ne' (hb r hr).2.1.ne'
  · apply ContinuousOn.log
    · exact (continuous_const.sub hd).continuousOn.div hd.continuousOn
        (fun r hr => (hb r hr).2.2.1.ne')
    · intro r hr
      exact (div_pos (hb r hr).2.2.2 (hb r hr).2.2.1).ne'

/-- A crude uniform bound is used only for integrability of the lower
certificate, never as the numerical supply budget. -/
theorem fibre_le_coarse {lo hi v z r : ℝ} (hv1 : v ≤ 1)
    (hA : admissible lo hi v z)
    (hr : max (1/100 : ℝ) (max (1-v-z-z) (1-v-z-v/2)) ≤ r ∧ r ≤ (1-v-z)/2) :
    fibre lo hi v z r ≤ 10000 := by
  have hrl : (1/100 : ℝ) ≤ r := (le_max_left _ _).trans hr.1
  have hr0 : 0 < r := by linarith
  have hS : (1/100 : ℝ) ≤ 1-v-z-r := by linarith [hr.2]
  have hS0 : 0 < 1-v-z-r := by linarith
  let d := max (1-v-z-r) (max (1-lo-z) (v-1/2))
  have hd := pair_boundary_bounds hv1 hA hr
  change (1/100 : ℝ) ≤ d ∧ d ≤ v/2 at hd
  have hd0 : 0 < d := by linarith [hd.1]
  have hratio : 0 < (v-d)/d := div_pos (by linarith [hd.2]) hd0
  have hlog : Real.log ((v-d)/d) ≤ 100 := by
    apply (Real.log_le_sub_one_of_pos hratio).trans
    have hratio' : (v-d)/d ≤ 100 := (div_le_iff₀ hd0).mpr (by linarith [hd.1])
    linarith
  have hlog0 : 0 ≤ Real.log ((v-d)/d) :=
    Real.log_nonneg ((le_div_iff₀ hd0).mpr (by linarith [hd.2]))
  have hcap : min r (max 0 (min (lo-v) (1-hi-z)))/(r*(1-v-z-r)) ≤ 100 := by
    rw [div_le_iff₀ (mul_pos hr0 hS0)]
    have hmul := mul_le_mul_of_nonneg_left hS hr0.le
    nlinarith [min_le_left r (max 0 (min (lo-v) (1-hi-z)))]
  change _*Real.log ((v-d)/d) ≤ _
  calc
    _ ≤ 100*Real.log ((v-d)/d) := mul_le_mul_of_nonneg_right hcap hlog0
    _ ≤ 100*100 := mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ = _ := by norm_num

/-- The whole supply density is nonnegative and integrable under the
fixed one-percent prime-share cutoff. Its enormous upper bound is solely
an integrability witness, not a usable debit allowance. -/
theorem density_bounds {lo hi v z : ℝ} (hhi : 1/100 ≤ hi)
    (hv : 1/100 ≤ v ∧ v ≤ 1) (hz : 1/100 ≤ z) :
    0 ≤ density lo hi (1/100) ![v,z] ∧
      density lo hi (1/100) ![v,z] ≤ 10000000000 := by
  let a := max (1/100 : ℝ) (max (1-v-z-z) (1-v-z-v/2))
  let b := (1-v-z)/2
  have ha : (1/100 : ℝ) ≤ a := le_max_left _ _
  have hden : (1/1000000 : ℝ) ≤ hi*v*z := by
    have hprod := mul_le_mul (mul_le_mul hhi hv.1 (by norm_num) (by linarith))
      hz (by norm_num) (mul_nonneg (by linarith) (by linarith))
    norm_num at hprod
    exact hprod
  have hden0 : 0 < hi*v*z := by linarith
  by_cases hA : admissible lo hi v z
  · simp only [density,Matrix.cons_val_zero,Matrix.cons_val_one,hA,if_true]
    change 0 ≤ (∫ r in Set.Ioc a b, fibre lo hi v z r)/(hi*v*z) ∧ _
    by_cases hab : a ≤ b
    · have hc := continuousOn_fibre (lo := lo) (hi := hi) (eps := (1/100 : ℝ))
        (by norm_num) hv.2 hA
      have hint : IntervalIntegrable (fibre lo hi v z) volume a b :=
        hc.intervalIntegrable_of_Icc hab
      have hpos : 0 ≤ ∫ r : ℝ in a..b, fibre lo hi v z r :=
        intervalIntegral.integral_nonneg hab (fun r hr => fibre_nonneg (by norm_num) hv.2 hA hr)
      have hbound : (∫ r : ℝ in a..b, fibre lo hi v z r) ≤ 10000 := by
        have hb := intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
          (fun r hr => fibre_le_coarse hv.2 hA hr)
        rw [intervalIntegral.integral_const] at hb
        have hlen : b-a ≤ 1 := by dsimp [b]; linarith [hv.1]
        simpa only [smul_eq_mul] using hb.trans (mul_le_of_le_one_left (by norm_num) hlen)
      rw [← intervalIntegral.integral_of_le hab]
      exact ⟨div_nonneg hpos hden0.le,(div_le_iff₀ hden0).mpr (by nlinarith)⟩
    · rw [Set.Ioc_eq_empty_of_le (le_of_not_ge hab)]
      simp
  · simp [density,hA]

/-- Adjacent common fibres add before the outer integration. The endpoints
are retained exactly, and the nonnegative exterior pieces remain available. -/
theorem sum_fibres_le_density {lo hi eps v z : ℝ}
    (heps : 0 < eps) (hhi : 0 < hi) (hv : 0 < v ∧ v ≤ 1) (hz : 0 < z)
    (hA : admissible lo hi v z) (a : ℕ → ℝ) (n : ℕ)
    (hleft : max eps (max (1-v-z-z) (1-v-z-v/2)) ≤ a 0)
    (hright : a n ≤ (1-v-z)/2)
    (ha : MonotoneOn a (Set.Icc 0 n)) :
    (∑ i ∈ Finset.range n, ∫ r : ℝ in a i..a (i+1), fibre lo hi v z r)/(hi*v*z) ≤
      density lo hi eps ![v,z] := by
  have hab : a 0 ≤ a n := ha (by simp) (by simp) (Nat.zero_le n)
  have hbase : max eps (max (1-v-z-z) (1-v-z-v/2)) ≤ (1-v-z)/2 :=
    hleft.trans (hab.trans hright)
  have hc := continuousOn_fibre heps hv.2 hA
  have hint : IntervalIntegrable (fibre lo hi v z) volume
      (max eps (max (1-v-z-z) (1-v-z-v/2))) ((1-v-z)/2) :=
    hc.intervalIntegrable_of_Icc hbase
  have hs (i : ℕ) (hinlt : i < n) :
      IntervalIntegrable (fibre lo hi v z) volume (a i) (a (i+1)) := by
    have h0i : a 0 ≤ a i := ha (by simp) ⟨Nat.zero_le _,hinlt.le⟩ (Nat.zero_le _)
    have hin : a (i+1) ≤ a n := ha ⟨Nat.zero_le _,hinlt⟩ (by simp) hinlt
    have hii : a i ≤ a (i+1) := ha ⟨Nat.zero_le _,hinlt.le⟩ ⟨Nat.zero_le _,hinlt⟩ (by omega)
    apply hint.mono_set
    rw [Set.uIcc_of_le hii,Set.uIcc_of_le hbase]
    exact Set.Icc_subset_Icc (hleft.trans h0i) (hin.trans hright)
  rw [intervalIntegral.sum_integral_adjacent_intervals hs]
  simp only [density,Matrix.cons_val_zero,Matrix.cons_val_one,hA,if_true]
  rw [← intervalIntegral.integral_of_le hbase]
  apply div_le_div_of_nonneg_right _ (mul_nonneg (mul_nonneg hhi.le hv.1.le) hz.le)
  apply intervalIntegral.integral_mono_interval hleft hab hright _ hint
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact fibre_nonneg heps hv.2 hA ⟨hr.1.le,hr.2⟩

/-- Elementary rational domain required on every supply-cover leaf. -/
def valid (lo hi : ℚ) (B : Box) : Prop :=
  1/100 ≤ hi ∧ lo ≤ hi ∧
  1/100 ≤ (B 0).1 ∧ (B 0).1 ≤ (B 0).2 ∧ (B 0).2 ≤ 1 ∧
  1/100 ≤ (B 1).1 ∧ (B 1).1 ≤ (B 1).2 ∧ (B 0).2+(B 1).2 < 1

instance (lo hi : ℚ) (B : Box) : Decidable (valid lo hi B) := by
  unfold valid
  infer_instance

/-- Lower endpoint common to every actual least-share fibre in the cell. -/
def left (B : Box) : ℚ :=
  max (1/100) (max (1-(B 0).1-(B 1).1-(B 1).1)
    (1-(B 0).1-(B 1).1-(B 0).1/2))

/-- Upper endpoint common to every actual least-share fibre in the cell. -/
def right (B : Box) : ℚ := (1-(B 0).2-(B 1).2)/2

/-- The nine exact endpoints of the eight common subintervals. -/
def point (B : Box) (i : ℕ) : ℚ := left B+(right B-left B)*(i : ℚ)/8

/-- Whole-cell cap height; both cutoff endpoints are used. -/
def height (lo hi : ℚ) (B : Box) : ℚ := max 0 (min (lo-(B 0).2) (1-hi-(B 1).2))

/-- Cells with positive credit must have a common nonempty fibre and
uniform saturation; a rejected cell still has the proved lower bound zero. -/
def active (lo hi : ℚ) (B : Box) : Prop :=
  left B < right B ∧ 0 < height lo hi B ∧
  1-lo ≤ (B 0).1 ∧ hi ≤ (B 0).1+(B 1).1 ∧ 2*(1-lo) ≤ (B 0).1+2*(B 1).1

instance (lo hi : ℚ) (B : Box) : Decidable (active lo hi B) := by
  unfold active
  infer_instance

/-- The moving pair boundary is bounded above on each common subinterval. -/
def pairEndpoint (lo : ℚ) (B : Box) (i : ℕ) : ℚ :=
  max (1-(B 0).1-(B 1).1-point B i)
    (max (1-lo-(B 1).1) ((B 0).2-1/2))

/-- Exact rational parameters for one common cap integral. Only its
expression is used here; no independently guessed fibre budget is assumed. -/
def fibreCap (lo hi : ℚ) (B : Box) (i : ℕ) : ZetaRieszCapacityCheck.Cap :=
  ⟨point B i,point B (i+1),1-(B 0).1-(B 1).1,height lo hi B,0,0⟩

open LeanCert.Core LeanCert.Engine

/-- Exact closed-form credit for one complete subinterval; a nonpositive
pair logarithm gives the safe zero minorant. -/
def fibreExpression (lo hi : ℚ) (B : Box) (i : ℕ) : Expr :=
  let d := pairEndpoint lo B i
  if 2*d < (B 0).1 then
    .mul (.const (1/(hi*(B 0).2*(B 1).2)))
      (.mul (.log (.const (((B 0).1-d)/d)))
        (ZetaRieszCapacityCheck.expression (fibreCap lo hi B i)))
  else .const 0

/-- The complete finite sum of fibre expressions, evaluated with shared
parameters and with every one of the eight subintervals accounted for. -/
def expressionSum (lo hi : ℚ) (B : Box) : ℕ → Expr
  | 0 => .const 0
  | n+1 => .add (expressionSum lo hi B n) (fibreExpression lo hi B n)

private theorem eval_expressionSum (lo hi : ℚ) (B : Box) (n : ℕ) :
    Expr.eval (fun _ => 0) (expressionSum lo hi B n) =
      ∑ i ∈ Finset.range n, Expr.eval (fun _ => 0) (fibreExpression lo hi B i) := by
  induction n with
  | zero => simp [expressionSum]
  | succ n ih => simp only [expressionSum,Expr.eval,Finset.sum_range_succ,ih]

private theorem point_bounds {lo hi : ℚ} {B : Box} (ha : active lo hi B)
    {i : ℕ} (hi8 : i < 8) :
    0 < point B i ∧ point B i < point B (i+1) ∧ point B (i+1) ≤ right B ∧
      left B ≤ point B i := by
  have hleft : (1/100 : ℚ) ≤ left B := le_max_left _ _
  have hi0 : (0 : ℚ) ≤ i := Nat.cast_nonneg _
  have hi1 : (i : ℚ)+1 ≤ 8 := by exact_mod_cast hi8
  dsimp [point]
  push_cast
  have hd := ha.1
  have hp := mul_nonneg (sub_nonneg.mpr hd.le) hi0
  have hq := mul_le_mul_of_nonneg_left hi1 (sub_nonneg.mpr hd.le)
  constructor
  · linarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

private theorem geometry {lo hi : ℚ} {B : Box} (hB : valid lo hi B)
    (hA : active lo hi B) {v z : ℝ}
    (hv : (B 0).1 ≤ v ∧ v ≤ (B 0).2) (hz : (B 1).1 ≤ z ∧ z ≤ (B 1).2) :
    0 < (hi : ℝ) ∧ 0 < v ∧ v ≤ 1 ∧ 0 < z ∧ admissible lo hi v z ∧
    max (1/100 : ℝ) (max (1-v-z-z) (1-v-z-v/2)) ≤ (left B : ℝ) ∧
    (right B : ℝ) ≤ (1-v-z)/2 ∧
    1-v-z ≤ ((1-(B 0).1-(B 1).1 : ℚ) : ℝ) ∧
    (height lo hi B : ℝ) ≤ max 0 (min ((lo : ℝ)-v) (1-hi-z)) ∧
    (hi : ℝ)*v*z ≤ (hi : ℝ)*(B 0).2*(B 1).2 := by
  have hh : (1/100 : ℝ) ≤ hi := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hB.1
  have hvl : (1/100 : ℝ) ≤ (B 0).1 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hB.2.2.1
  have hvr : ((B 0).2 : ℝ) ≤ 1 := by exact_mod_cast hB.2.2.2.2.1
  have hzl : (1/100 : ℝ) ≤ (B 1).1 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hB.2.2.2.2.2.1
  have hA₁ : 1-(lo : ℝ) ≤ (B 0).1 := by exact_mod_cast hA.2.2.1
  have hA₂ : (hi : ℝ) ≤ (B 0).1+(B 1).1 := by exact_mod_cast hA.2.2.2.1
  have hA₃ : 2*(1-(lo : ℝ)) ≤ (B 0).1+2*(B 1).1 := by
    exact_mod_cast hA.2.2.2.2
  have hv0 : 0 < v := by linarith [hv.1]
  have hz0 : 0 < z := by linarith [hz.1]
  refine ⟨by linarith,hv0,hv.2.trans hvr,hz0,
    ⟨by linarith [hv.1],by linarith [hv.1,hz.1],by linarith [hv.1,hz.1]⟩,?_,?_,?_,?_,?_⟩
  · simp only [left,Rat.cast_max,Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one]
    apply max_le_max le_rfl
    exact max_le_max (by linarith [hv.1,hz.1]) (by linarith [hv.1,hz.1])
  · simp only [right,Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one]
    linarith [hv.2,hz.2]
  · push_cast
    linarith [hv.1,hz.1]
  · simp only [height,Rat.cast_max,Rat.cast_min,Rat.cast_sub,Rat.cast_one,Rat.cast_zero]
    exact max_le_max le_rfl (min_le_min (by linarith [hv.2]) (by linarith [hz.2]))
  · exact mul_le_mul (mul_le_mul_of_nonneg_left hv.2 (by linarith)) hz.2 hz0.le
      (mul_nonneg (by linarith) (by linarith [hv.2]))

private theorem cap_expression_integral {c : ZetaRieszCapacityCheck.Cap}
    (ha : 0 < c.a) (hab : c.a ≤ c.b) (hbS : c.b < c.total) :
    Expr.eval (fun _ => 0) (ZetaRieszCapacityCheck.expression c) =
      ∫ r : ℝ in (c.a : ℝ)..(c.b : ℝ), min r (c.height : ℝ)/(r*(c.total-r)) := by
  rw [cap_integral_eq (by exact_mod_cast ha) (by exact_mod_cast hab)
    (by exact_mod_cast hbS)]
  simp [ZetaRieszCapacityCheck.expression,Expr.eval,Rat.cast_max,Rat.cast_min]

/-- One common subinterval controls its full moving fibre throughout the
outer cell. This is the analytic soundness step used by the numerical
checker; the full correlated boundary remains in `fibre`. -/
theorem fibreExpression_le {lo hi : ℚ} {B : Box} (hB : valid lo hi B)
    (hA : active lo hi B) {v z : ℝ}
    (hv : (B 0).1 ≤ v ∧ v ≤ (B 0).2) (hz : (B 1).1 ≤ z ∧ z ≤ (B 1).2)
    {i : ℕ} (hi8 : i < 8) :
    Expr.eval (fun _ => 0) (fibreExpression lo hi B i) ≤
      (∫ r : ℝ in (point B i : ℝ)..(point B (i+1) : ℝ), fibre lo hi v z r) /
        ((hi : ℝ)*v*z) := by
  obtain ⟨hhi,hv0,hv1,hz0,hgeom,hl,hr,hS,hm,hden⟩ := geometry hB hA hv hz
  obtain ⟨hai,haii,hibr,hali⟩ := point_bounds hA hi8
  have ha0 : (0 : ℝ) < point B i := by exact_mod_cast hai
  have hab : (point B i : ℝ) ≤ point B (i+1) := by exact_mod_cast haii.le
  have ha' : max (1/100 : ℝ) (max (1-v-z-z) (1-v-z-v/2)) ≤ point B i :=
    hl.trans (by exact_mod_cast hali)
  have hb' : (point B (i+1) : ℝ) ≤ (1-v-z)/2 :=
    le_trans (by exact_mod_cast hibr) hr
  have hbS : (point B (i+1) : ℝ) < 1-v-z := by linarith
  have hraw0 : 0 ≤ ∫ r : ℝ in (point B i : ℝ)..(point B (i+1) : ℝ), fibre lo hi v z r := by
    apply intervalIntegral.integral_nonneg hab
    intro r hri
    exact fibre_nonneg (by norm_num) hv1 hgeom ⟨ha'.trans hri.1,hri.2.trans hb'⟩
  unfold fibreExpression
  by_cases hd : 2*pairEndpoint lo B i < (B 0).1
  · rw [if_pos hd]
    have hd₁ : 1-v-z-(point B i : ℝ) ≤ (pairEndpoint lo B i : ℝ) := by
      simp only [pairEndpoint,Rat.cast_max,Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one]
      apply le_trans _ (le_max_left _ _)
      linarith [hv.1,hz.1]
    have hd₂ : 1-(lo : ℝ)-z ≤ (pairEndpoint lo B i : ℝ) := by
      simp only [pairEndpoint,Rat.cast_max,Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one]
      apply le_trans _ ((le_max_left _ _).trans (le_max_right _ _))
      linarith [hz.1]
    have hd₃ : v-1/2 ≤ (pairEndpoint lo B i : ℝ) := by
      simp only [pairEndpoint,Rat.cast_max,Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one]
      apply le_trans _ ((le_max_right _ _).trans (le_max_right _ _))
      linarith [hv.2]
    have hnum := five_fibre_lower ha0 hab hbS hS
      (m₀ := (height lo hi B : ℝ)) (by exact_mod_cast hA.2.1.le) hm hv.1
      hd₁ hd₂ hd₃ (by exact_mod_cast hd)
    change _ ≤ ∫ r : ℝ in (point B i : ℝ)..(point B (i+1) : ℝ), fibre lo hi v z r at hnum
    push_cast at hnum
    have hc : Expr.eval (fun _ => 0) (ZetaRieszCapacityCheck.expression (fibreCap lo hi B i)) =
        ∫ r : ℝ in (point B i : ℝ)..(point B (i+1) : ℝ),
          min r (height lo hi B : ℝ)/(r*(((1-(B 0).1-(B 1).1 : ℚ) : ℝ)-r)) := by
      apply cap_expression_integral hai haii.le
      exact_mod_cast hbS.trans_le hS
    simp only [Expr.eval,Rat.cast_div,Rat.cast_one,Rat.cast_sub,Rat.cast_mul,hc]
    rw [one_div,mul_comm,← div_eq_mul_inv]
    exact div_le_div₀ hraw0 hnum (by positivity) hden
  · rw [if_neg hd]
    simp only [Expr.eval,Rat.cast_zero]
    exact div_nonneg hraw0 (by positivity)

/-- All eight checked expressions together bound the entire moving
five-prime fibre from below at every point of the outer cell. -/
theorem expression_le_density {lo hi : ℚ} {B : Box} (hB : valid lo hi B)
    (hA : active lo hi B) {v z : ℝ}
    (hv : (B 0).1 ≤ v ∧ v ≤ (B 0).2) (hz : (B 1).1 ≤ z ∧ z ≤ (B 1).2) :
    Expr.eval (fun _ => 0) (expressionSum lo hi B 8) ≤ density lo hi (1/100) ![v,z] := by
  obtain ⟨hhi,hv0,hv1,hz0,hgeom,hl,hr,-,-,-⟩ := geometry hB hA hv hz
  have hleft : max (1/100 : ℝ) (max (1-v-z-z) (1-v-z-v/2)) ≤ (point B 0 : ℝ) := by
    simpa only [point,Nat.cast_zero,mul_zero,zero_div,add_zero] using hl
  have hright : (point B 8 : ℝ) ≤ (1-v-z)/2 := by
    convert hr using 1
    norm_num [point]
  have hmono : MonotoneOn (fun i => (point B i : ℝ)) (Set.Icc 0 8) := by
    intro i _ j _ hij
    have hij' : (i : ℚ) ≤ j := by exact_mod_cast hij
    have hd : 0 ≤ right B-left B := sub_nonneg.mpr hA.1.le
    apply Rat.cast_le.mpr
    have hmul : (right B-left B)*(i : ℚ) ≤ (right B-left B)*(j : ℚ) :=
      mul_le_mul_of_nonneg_left hij' hd
    dsimp only [point]
    linarith only [hmul]
  have hs := sum_fibres_le_density (by norm_num) hhi ⟨hv0,hv1⟩ hz0 hgeom
    (fun i => (point B i : ℝ)) 8 hleft hright hmono
  rw [eval_expressionSum]
  apply le_trans _ hs
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun i hi8 => fibreExpression_le hB hA hv hz (Finset.mem_range.mp hi8))

/-- Fixed outward-rounded precision for the one-sided supply checks.
Acceptance, rather than the chosen depth, determines validity. -/
def config : DyadicConfig := {precision := -40, taylorDepth := 12}

/-- Check the complete eight-fibre lower expression with outward rounding.
No externally computed floating-point total enters the proof. -/
def check (lo hi : ℚ) (B : Box) (w : ℚ × ℚ) : Bool :=
  decide (valid lo hi B ∧ 0 ≤ w.1 ∧ w.2 = 10000000000) &&
  if w.1 = 0 then true else
  if active lo hi B then
    match evalIntervalDyadicChecked (expressionSum lo hi B 8) (fun _ => default)
        config with
    | .error _ => false
    | .ok I => decide (w.1 ≤ I.lo.toRat)
  else false

/-- Acceptance proves a lower budget for the actual whole supply cell,
with every ordering and saturation mask still present. -/
theorem check_sound {lo hi : ℚ} {B : Box} {w : ℚ × ℚ}
    (hc : check lo hi B w = true) {x : Fin 2 → ℝ} (hx : CertifiedBoxCover.Mem x B) :
    (w.1 : ℝ) ≤ density lo hi (1/100) x ∧ density lo hi (1/100) x ≤ (w.2 : ℝ) := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨hB,hw0,hwu⟩ := hc.1
  have hhi : (1/100 : ℝ) ≤ hi := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hB.1
  have hv0 : (1/100 : ℝ) ≤ (B 0).1 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hB.2.2.1
  have hz0 : (1/100 : ℝ) ≤ (B 1).1 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hB.2.2.2.2.2.1
  have hv1 : ((B 0).2 : ℝ) ≤ 1 := by exact_mod_cast hB.2.2.2.2.1
  have hxe : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  have hb := density_bounds (lo := (lo : ℝ)) hhi
    ⟨hv0.trans (hx 0).1,(hx 0).2.trans hv1⟩ (hz0.trans (hx 1).1)
  rw [← hxe] at hb
  refine ⟨?_,?_⟩
  · by_cases hw : w.1 = 0
    · simpa only [hw,Rat.cast_zero] using hb.1
    · have hc' := hc.2
      rw [if_neg hw] at hc'
      split_ifs at hc' with hA
      · cases he : evalIntervalDyadicChecked (expressionSum lo hi B 8) (fun _ => default)
          config with
        | error err => simp [he] at hc'
        | ok I =>
          have hnum : w.1 ≤ I.lo.toRat := by simpa only [he,decide_eq_true_eq] using hc'
          have henv : envMemDyadic (fun _ => (0 : ℝ)) (fun _ => default) := by
            intro i
            simp [Membership.mem,default,IntervalDyadic.singleton,
              LeanCert.Core.Dyadic.zero,LeanCert.Core.Dyadic.toRat]
          have heval := evalIntervalDyadicChecked_correct (expressionSum lo hi B 8) _ _ henv
            config (by norm_num [config]) I he
          have hl : (w.1 : ℝ) ≤ (I.lo.toRat : ℝ) := by exact_mod_cast hnum
          have hbudget := expression_le_density hB hA (hx 0) (hx 1)
          rw [← hxe] at hbudget
          exact hl.trans (heval.1.trans hbudget)
  · simpa only [hwu,Rat.cast_ofNat] using hb.2

/-- A fully checked exhaustive supply cover proves its rational total as
a lower bound for the entire selected angular region. The arithmetic
prime transport and common-phase comparison are not assumed here. -/
theorem integral_ge_of_checked_cover {lo hi : ℚ} (tree : Tree) {B : Box}
    (hB : ∀ i, (B i).1 ≤ (B i).2)
    (hc : ZetaRieszCapacityCover.check (check lo hi) tree B = true)
    {lower : ℚ} (hlower : decide (lower ≤ (totals tree B).1) = true) :
    (lower : ℝ) ≤ ∫ x in region B, density lo hi (1/100) x := by
  have hleaf (C : Box) (w : ℚ × ℚ) (hw : check lo hi C w = true)
      (x : Fin 2 → ℝ) (hx : x ∈ region C) :
      (w.1 : ℝ) ≤ density lo hi (1/100) x ∧ density lo hi (1/100) x ≤ (w.2 : ℝ) := by
    apply check_sound hw
    intro i
    have hi := Set.mem_pi.mp hx i (Set.mem_univ i)
    exact ⟨hi.1.le,hi.2⟩
  have hint := integrableOn_of_check (density lo hi (1/100))
    (measurable_density lo hi (1/100)) (check lo hi) hleaf tree hc
  have hb := (integral_bounds_of_check (density lo hi (1/100)) (check lo hi) hleaf tree hB hint hc).1
  have hl : (lower : ℝ) ≤ ((totals tree B).1 : ℝ) := by
    simp only [decide_eq_true_eq] at hlower
    exact_mod_cast hlower
  exact hl.trans hb

end RiemannGaussian.ZetaRieszFiveCapacityCover

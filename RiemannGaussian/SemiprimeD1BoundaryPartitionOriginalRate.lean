/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryPartitionWidthRate
import RiemannGaussian.SemiprimeD1AuxiliaryRate
import RiemannGaussian.SemiprimeD1LeafRate

/-! # Uniform half-exponent boundary width at the original stopped-leaf scale -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BoundaryPartitionOriginalRate
open Filter SemiprimeD1BoundaryPlan SemiprimeD1BoundaryPartitionWidthRate
open SemiprimeD1PackingReady

/-- A quantitative sufficient condition for the cube-root correction to be small. -/
theorem cube_correction_small (m d L e : Real) (hm : 0 ≤ m) (hd : 0 ≤ d)
    (hL : 1 ≤ L) (he : 0 < e) (hmL : m ≤ L + 1)
    (hsmall : 864 * d ≤ e^3 * L) :
    3 * ((m^2 * d) ^ ((3 : Real)⁻¹)) ≤ e * L / 2 := by
  let q := (m^2 * d) ^ ((3 : Real)⁻¹)
  have hq : 0 ≤ q := Real.rpow_nonneg (by positivity) _
  have hcube : q^3 = m^2 * d :=
    Real.rpow_inv_natCast_pow (by positivity) (by decide : (3 : Nat) ≠ 0)
  have hm2 : m ≤ 2 * L := by linarith
  have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm hm2 2) hd
  have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg L)
  have htarget : q^3 ≤ (e * L / 6)^3 := by rw [hcube]; nlinarith
  have hbound := (pow_le_pow_iff_left₀ hq (by positivity : 0 ≤ e * L / 6)
    (by decide : 3 ≠ 0)).mp htarget
  change 3 * q ≤ _
  linarith

/-- Explicit real reserve conditions imply half-scale width for the actual code. -/
theorem acquired_width_half_of_reserve (g : Graph)
    (hg : SemiprimeD1BoundaryPotential.Valid g) (hm : 0 < g.edges.length)
    (L e : Real) (hL : 1 ≤ L) (he : 0 < e)
    (hmL : (g.edges.length : Real) ≤ L + 1) (heL : 1 ≤ e * L)
    (hsmall : 864 * (maxDegree g : Real) ≤ e^3 * L) :
    ((acquire g).width : Real) ≤ (1 / 2 + e) * L := by
  have hw := acquired_width_cuberoot g hg hm
  have hc := cube_correction_small (g.edges.length : Real) (maxDegree g : Real) L e
    (by positivity) (by positivity) hL he hmL hsmall
  nlinarith

/-- Uniformly over every valid graph at the actual stopped-leaf size and degree,
the deterministic boundary partition has half the original enumeration exponent. -/
theorem eventually_acquired_width_half (e : Real) (he : 0 < e) :
    ∀ᶠ s : Nat in atTop, ∀ g : Graph,
      SemiprimeD1BoundaryPotential.Valid g → 0 < g.edges.length →
      (g.edges.length : Real) ≤ (s : Real) / Real.sqrt (logarithm s : Real) + 1 →
      maxDegree g ≤ degreeCap s →
      ((acquire g).width : Real) ≤
        (1 / 2 + e) * ((s : Real) / Real.sqrt (logarithm s : Real)) := by
  have ht : Tendsto logarithm atTop atTop :=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (tendsto_add_atTop_nat 2)
  have hroot : Tendsto (fun s : Nat => Real.sqrt (logarithm s : Real)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp ht)
  filter_upwards [SemiprimeD1AuxiliaryRate.eventually_degree_times_log,
    SemiprimeD1AuxiliaryRate.eventually_log_power 1,
    hroot.eventually (eventually_ge_atTop (max 1 (max (1 / e) (864 / e^3))))]
    with s hd hs hr
  intro g hg hm hmL hgD
  let t := Real.sqrt (logarithm s : Real)
  let L := (s : Real) / t
  have ht1 : 1 ≤ t := (le_max_left _ _).trans hr
  have ht0 : 0 < t := by linarith
  have hsq : t^2 = (logarithm s : Real) := Real.sq_sqrt (by positivity)
  have hsR : (logarithm s : Real) ≤ (s : Real) := by
    exact_mod_cast (by simpa only [pow_one] using hs : logarithm s ≤ s)
  have htL : t ≤ L := by
    apply (le_div_iff₀ ht0).mpr
    nlinarith
  have hL : 1 ≤ L := ht1.trans htL
  have heinv : 1 / e ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans hr)
  have heL : 1 ≤ e * L := by
    have hh := mul_le_mul_of_nonneg_left (heinv.trans htL) he.le
    rw [mul_one_div_cancel he.ne'] at hh
    exact hh
  have heroot : 864 / e^3 ≤ t :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hr)
  have het : 864 ≤ e^3 * t := by
    have hh := (div_le_iff₀ (pow_pos he 3)).mp heroot
    nlinarith
  have hdegree : (maxDegree g : Real) * (logarithm s : Real) ≤ (s : Real) := by
    have hh := (Nat.mul_le_mul_right (logarithm s) hgD).trans hd
    exact_mod_cast hh
  have hdL : (maxDegree g : Real) * t ≤ L := by
    apply (le_div_iff₀ ht0).mpr
    nlinarith [hdegree]
  have hsmall : 864 * (maxDegree g : Real) ≤ e^3 * L := by
    have h1 := mul_le_mul_of_nonneg_right het (show 0 ≤ (maxDegree g : Real) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hdL (show 0 ≤ e^3 by positivity)
    nlinarith
  exact acquired_width_half_of_reserve g hg hm L e hL he hmL heL hsmall

/-- An edgeless actual acquisition has exactly zero measured width. -/
theorem acquired_width_zero (g : Graph) (hm : g.edges.length = 0) : (acquire g).width = 0 := by
  have he : g.edges = [] := List.length_eq_zero_iff.mp hm
  have hz {α : Type} (xs : List α) : ((xs.map (fun _ => (0 : Nat))).foldl max 0) = 0 := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa only [List.map_cons, List.foldl_cons, max_self] using ih
  have hv (colours : List Nat) : loadValue g colours = fun _ => 0 := by
    funext load
    simp [loadValue, he]
  change ((loads (chooseK g)).map
    (loadValue g (extend g (chooseK g) g.vertices []).value)).foldl max 0 = 0
  rw [hv]
  exact hz _

/-- The uniform half-exponent statement includes empty stopped leaves exactly. -/
theorem eventually_acquired_width_half_all (e : Real) (he : 0 < e) :
    ∀ᶠ s : Nat in atTop, ∀ g : Graph,
      SemiprimeD1BoundaryPotential.Valid g →
      (g.edges.length : Real) ≤ (s : Real) / Real.sqrt (logarithm s : Real) + 1 →
      maxDegree g ≤ degreeCap s →
      ((acquire g).width : Real) ≤
        (1 / 2 + e) * ((s : Real) / Real.sqrt (logarithm s : Real)) := by
  filter_upwards [eventually_acquired_width_half e he] with s hs
  intro g hg hm hd
  by_cases hp : 0 < g.edges.length
  · exact hs g hg hp hm hd
  · rw [acquired_width_zero g (by omega)]
    norm_num only [Nat.cast_zero]
    positivity

end RiemannGaussian.SemiprimeD1BoundaryPartitionOriginalRate

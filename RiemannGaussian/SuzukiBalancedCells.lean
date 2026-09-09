/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLegendreDivisorDual
import RiemannGaussian.SuzukiActualCutoff

/-!
# The mass-balanced cells of the actual Suzuki signal

Keep the full signed prime hinge sum. A local minimum must coincide with
the mass center of its active integer cell. On such cells the endpoint
entropy cost has a vanishing explicit bound. The arithmetic lower bound on
the remaining signed endpoint statistic is not assumed proved.
-/

namespace RiemannGaussian
noncomputable section
open Filter Set
open scoped Topology

/-- The literal prime hinge sum with the exponential-affine background.
It differs from the pointwise Suzuki function only by its explicit
Archimedean value tail at nonnegative time. -/
def suzukiLegendreSignal (t : ℝ) : ℝ :=
  screwHingeModel
    (fun s => suzukiArchimedeanIntercept + 4 * Real.exp (s / 2) +
      suzukiArchimedeanSlopeConstant * s) suzukiPrimeLocation suzukiPrimeWeight t

/-- A cell is balanced when its corrected prime mass places its exact
exponential minimum between its two physical integer endpoints. -/
def SuzukiMassBalancedCell (count : ℕ) : Prop :=
  2 * Real.sqrt ((count + 2 : ℕ) : ℝ) ≤
      suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant ∧
    suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant ≤
      2 * Real.sqrt ((count + 3 : ℕ) : ℝ)

/-- The original Laplace signal is retained exactly, including its affine
Archimedean correction. -/
theorem suzukiLegendreSignal_eq_laplace_add_affine {t : ℝ} (ht : 0 ≤ t) :
    suzukiLegendreSignal t = suzukiChebyshevLogAverageLaplaceSignal t +
      suzukiArchimedeanSlopeConstant * t + suzukiArchimedeanIntercept := by
  rw [suzukiChebyshevLogAverageLaplaceSignal_eq_main_sub_prime ht]
  unfold suzukiLegendreSignal screwHingeModel
  rw [tsum_suzukiPrimeNegativeHinge_eq_neg_pointwisePrimeContribution ht]
  ring

/-- Local finiteness preserves continuity through every prime-power event. -/
theorem continuous_suzukiLegendreSignal : Continuous suzukiLegendreSignal := by
  classical
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨cutoff, hc⟩ := suzukiPrimeLocation_unbounded (t + 1)
  let f : ℝ → ℝ := fun s =>
    suzukiArchimedeanIntercept + 4 * Real.exp (s / 2) +
      suzukiArchimedeanSlopeConstant * s +
      ∑ n ∈ Finset.range cutoff,
        screwNegativeHinge (suzukiPrimeWeight n) (suzukiPrimeLocation n) s
  have hf : Continuous f := by unfold f screwNegativeHinge; fun_prop
  apply hf.continuousAt.congr
  filter_upwards [gt_mem_nhds (lt_add_one t)] with s hs
  unfold suzukiLegendreSignal screwHingeModel f
  congr 1
  symm
  apply tsum_eq_sum
  intro n hn
  apply screwNegativeHinge_eq_zero_of_le_location
  have hn' : cutoff ≤ n := by simpa using hn
  exact hs.le.trans (hc.le.trans (monotone_suzukiPrimeLocation hn'))

/-- Every frozen exponential regime majorizes the complete signed signal,
including before and after its active cell. -/
theorem suzukiLegendreSignal_le_trial (count : ℕ) (t : ℝ) :
    suzukiLegendreSignal t ≤ suzukiLegendreTrial count t := by
  have h := screwHingeModel_le_frozen (archimedean := fun s =>
      suzukiArchimedeanIntercept + 4 * Real.exp (s / 2) +
        suzukiArchimedeanSlopeConstant * s)
    suzukiPrimeWeight_nonnegative (summable_suzukiPrimeNegativeHinge t) (count + 1)
  rw [frozenScrewHingeModel_eq_arch_sub_mass_add_moment] at h
  unfold suzukiLegendreSignal suzukiLegendreTrial
  rw [suzukiLegendreLinearForm_eq_prefixMoment_sub_mass]
  change _ ≤ _ - t * suzukiOldPrimeMass count + _ at h
  linarith

/-- The active cell's frozen majorant is exact at every point of that cell. -/
theorem suzukiLegendreSignal_eq_trial_of_eventCut (count : ℕ) {t : ℝ}
    (hc : ScrewEventCut suzukiPrimeLocation t (count + 1)) :
    suzukiLegendreSignal t = suzukiLegendreTrial count t := by
  unfold suzukiLegendreSignal
  rw [screwHingeModel_eq_frozen_of_eventCut (summable_suzukiPrimeNegativeHinge t) hc,
    frozenScrewHingeModel_eq_arch_sub_mass_add_moment]
  unfold suzukiLegendreTrial
  rw [suzukiLegendreLinearForm_eq_prefixMoment_sub_mass]
  change _ - t * suzukiOldPrimeMass count + _ = _
  ring

/-- The derivative is the difference of the smooth mass and the same
corrected prime-prefix mass; no independent mass approximation is used. -/
theorem hasDerivAt_suzukiLegendreTrial (count : ℕ) (t : ℝ) :
    HasDerivAt (suzukiLegendreTrial count)
      (2 * Real.exp (t / 2) -
        (suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant)) t := by
  have he : suzukiLegendreTrial count = fun r =>
      suzukiArchimedeanIntercept + 4 * Real.exp (r / 2) +
        suzukiArchimedeanSlopeConstant * r +
        (screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight (count + 1) -
          r * suzukiOldPrimeMass count) := by
    funext r
    rw [suzukiLegendreTrial, suzukiLegendreLinearForm_eq_prefixMoment_sub_mass]
  rw [he]
  convert! (((hasDerivAt_const t suzukiArchimedeanIntercept).add
    (((hasDerivAt_id t).div_const 2).exp.const_mul 4)).add
    ((hasDerivAt_id t).const_mul suzukiArchimedeanSlopeConstant)).add
    ((hasDerivAt_const t
      (screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight (count + 1))).sub
        ((hasDerivAt_id t).mul_const (suzukiOldPrimeMass count))) using 1
  simp
  ring

/-- At a genuine local minimum after the first event, some active integer
cell is mass balanced and its nonlinear potential is exactly the signal.
The global frozen-majorant inequality also covers minima at event points. -/
theorem suzukiLegendreSignal_localMin_balanced {t : ℝ}
    (ht : Real.log 2 < t) (hmin : IsLocalMin suzukiLegendreSignal t) :
    ∃ count : ℕ, SuzukiMassBalancedCell count ∧
      Real.log ((count + 2 : ℕ) : ℝ) ≤ t ∧
      t ≤ Real.log ((count + 3 : ℕ) : ℝ) ∧
      t = suzukiLegendreMassCenter count ∧
      suzukiLegendreSignal t = suzukiMassLegendrePotential count := by
  obtain ⟨cutoff, hc⟩ := suzukiPrimeEventCutsCover t
  cases cutoff with
  | zero =>
    have h := hc.2 0
    simp only [Nat.zero_add, suzukiPrimeLocation, Nat.cast_ofNat] at h
    linarith
  | succ count =>
    have he := suzukiLegendreSignal_eq_trial_of_eventCut count hc
    have hm : IsLocalMin (suzukiLegendreTrial count) t := by
      change ∀ᶠ s in 𝓝 t, suzukiLegendreTrial count t ≤ suzukiLegendreTrial count s
      filter_upwards [hmin] with s hs
      rw [← he]
      exact hs.trans (suzukiLegendreSignal_le_trial count s)
    have hd := hm.hasDerivAt_eq_zero (hasDerivAt_suzukiLegendreTrial count t)
    have hl : Real.log ((count + 2 : ℕ) : ℝ) ≤ t := hc.1 count (by omega)
    have hu : t ≤ Real.log ((count + 3 : ℕ) : ℝ) := by
      simpa [suzukiPrimeLocation, Nat.add_assoc] using hc.2 0
    have hcenter : t = suzukiLegendreMassCenter count := by
      have he' : (suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) / 2 =
          Real.exp (t / 2) := by linarith
      rw [suzukiLegendreMassCenter, he', Real.log_exp]
      ring
    refine ⟨count, ?_, hl, hu, hcenter, ?_⟩
    · have hlow := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hl (by norm_num : (0 : ℝ) ≤ 2))
      have hupp := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hu (by norm_num : (0 : ℝ) ≤ 2))
      rw [Real.exp_half, Real.exp_log (by positivity)] at hlow
      rw [Real.exp_half (Real.log ((count + 3 : ℕ) : ℝ)),
        Real.exp_log (by positivity)] at hupp
      exact ⟨by linarith, by linarith⟩
    · rw [he, hcenter, suzukiLegendreTrial_massCenter]

/-- A hypothetical right-half zero forces arbitrarily late excursions in
both orientations of the complete signal. This uses its genuine Laplace
response and makes no assumption on zero multiplicities. -/
theorem suzukiLegendreSignal_frequently_scaled_below_of_right_half_zero
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {a : ℝ} (ha : a ≠ 0) (B : ℝ) :
    ∃ᶠ t : ℝ in atTop, a * suzukiLegendreSignal t < B := by
  by_contra hn
  have hb : ∀ᶠ t : ℝ in atTop, B ≤ a * suzukiLegendreSignal t := by
    simpa only [not_frequently, not_lt] using hn
  obtain ⟨T, hT⟩ := eventually_atTop.mp hb
  let U := max T 0
  have hU : 0 ≤ U := le_max_right _ _
  obtain ⟨u, _, hu⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc 0 U).Nonempty from ⟨0, le_rfl, hU⟩)
    (continuous_suzukiLegendreSignal.const_mul a).continuousOn
  let L := min B (a * suzukiLegendreSignal u)
  have hl : ∀ t : ℝ, 0 < t → L ≤ a * suzukiLegendreSignal t := by
    intro t ht
    by_cases htU : t ≤ U
    · exact (min_le_right _ _).trans (hu ⟨ht.le, htU⟩)
    · exact (min_le_left _ _).trans (hT t ((le_max_left _ _).trans (le_of_not_ge htU)))
  have hRH := riemannHypothesis_of_suzuki_signal_scaled_affine_lower_bound ha
    (C := |L| + |a * suzukiArchimedeanIntercept|)
    (D := |a * suzukiArchimedeanSlopeConstant|) (by positivity) (by positivity) (by
      intro t ht
      have h := hl t ht
      rw [suzukiLegendreSignal_eq_laplace_add_affine ht.le] at h
      have hc := le_abs_self (a * suzukiArchimedeanIntercept)
      have hd := mul_le_mul_of_nonneg_right
        (le_abs_self (a * suzukiArchimedeanSlopeConstant)) ht.le
      nlinarith [neg_abs_le L])
  have hre := hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
  linarith

/-- Every prescribed negative level has an actual local minimum beyond
every prescribed time under a hypothetical right-half zero. -/
theorem suzukiLegendreSignal_late_localMin_of_right_half_zero
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (T B : ℝ) :
    ∃ t : ℝ, T < t ∧ IsLocalMin suzukiLegendreSignal t ∧ suzukiLegendreSignal t < B := by
  have hlo := suzukiLegendreSignal_frequently_scaled_below_of_right_half_zero
    rho hrho (a := 1) (by norm_num) (min B (suzukiLegendreSignal T))
  obtain ⟨b, hbT, hb⟩ := frequently_atTop'.mp hlo T
  simp only [one_mul, lt_min_iff] at hb
  have hhi := suzukiLegendreSignal_frequently_scaled_below_of_right_half_zero
    rho hrho (a := -1) (by norm_num) (-suzukiLegendreSignal b)
  obtain ⟨c, hcb, hc⟩ := frequently_atTop'.mp hhi b
  have hbc : suzukiLegendreSignal b < suzukiLegendreSignal c := by linarith
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc T c).Nonempty from ⟨b, hbT.le, hcb.le⟩)
    continuous_suzukiLegendreSignal.continuousOn
  have htb := hmin (show b ∈ Icc T c from ⟨hbT.le, hcb.le⟩)
  change suzukiLegendreSignal t ≤ suzukiLegendreSignal b at htb
  have hTt : T < t := lt_of_le_of_ne ht.1 (by
    intro he
    subst t
    linarith [hb.2])
  have htc : t < c := lt_of_le_of_ne ht.2 (by
    intro he
    subst t
    linarith)
  exact ⟨t, hTt, hmin.isLocalMin (Icc_mem_nhds hTt htc), htb.trans_lt hb.1⟩

/-- The bad source cannot escape the balanced cells: every right-half zero
forces their exact nonlinear potential below every finite floor at
arbitrarily large cutoffs. The independent floor is still open. -/
theorem suzuki_balanced_potential_frequently_below_of_right_half_zero
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (B : ℝ) :
    ∃ᶠ count : ℕ in atTop,
      SuzukiMassBalancedCell count ∧ suzukiMassLegendrePotential count < B := by
  rw [frequently_atTop]
  intro start
  obtain ⟨t, ht, hm, hb⟩ := suzukiLegendreSignal_late_localMin_of_right_half_zero
    rho hrho (Real.log ((start + 3 : ℕ) : ℝ)) B
  have ht2 : Real.log 2 < t := lt_of_le_of_lt
    (Real.log_le_log (by norm_num) (by norm_cast; omega)) ht
  obtain ⟨count, hbal, _, hu, _, he⟩ := suzukiLegendreSignal_localMin_balanced ht2 hm
  have hcount : start ≤ count := by
    have hlog : Real.log ((start + 3 : ℕ) : ℝ) <
        Real.log ((count + 3 : ℕ) : ℝ) := ht.trans_le hu
    have hn : (start + 3 : ℕ) < count + 3 := by
      exact_mod_cast (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlog
    omega
  exact ⟨count, hcount, hbal, by rwa [he] at hb⟩

/-- The corrected mass ratio of a balanced cell differs from one by at
most `1 / (2*N)`. The estimate uses the cell's own two endpoints. -/
theorem suzuki_balanced_massRatio_bounds {count : ℕ}
    (hc : SuzukiMassBalancedCell count) :
    0 ≤ suzukiActualEndpointMassRatio count - 1 ∧
      suzukiActualEndpointMassRatio count - 1 ≤ 1 / (2 * ((count + 2 : ℕ) : ℝ)) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let q := suzukiActualEndpointMassRatio count
  have hb : 0 < b := by dsimp [b]; positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hq : 0 < q := suzukiActualEndpointMassRatio_pos count
  have hprod : q * (2 * Real.sqrt b) =
      suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant := by
    dsimp [q, b, suzukiActualEndpointMassRatio]
    field_simp
  have hlo : 2 * Real.sqrt b ≤ q * (2 * Real.sqrt b) := by
    rw [hprod]
    exact hc.1
  have hu : q * (2 * Real.sqrt b) ≤ 2 * Real.sqrt (b + 1) := by
    rw [hprod]
    have he : b + 1 = ((count + 3 : ℕ) : ℝ) := by dsimp [b]; push_cast; ring
    rw [he]
    exact hc.2
  have hq1 : 0 ≤ q - 1 := by nlinarith
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ q * (2 * Real.sqrt b)) hu
  have hsb := Real.sq_sqrt hb.le
  have hs1 := Real.sq_sqrt (by linarith : 0 ≤ b + 1)
  have hsq' : b * q ^ 2 ≤ b + 1 := by nlinarith [hsb, hs1]
  have hh : 2 * b * (q - 1) ≤ 1 := by
    nlinarith [mul_nonneg hb.le (sq_nonneg (q - 1))]
  refine ⟨hq1, ?_⟩
  change q - 1 ≤ 1 / (2 * b)
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

/-- At every balanced cell the entire nonlinear entropy cost is at most
`1 / (N * sqrt N)`. This is an independent, uniform vanishing estimate
for this correction, not a bound on the signed arithmetic remainder. -/
theorem suzuki_balanced_entropy_bounds {count : ℕ}
    (hc : SuzukiMassBalancedCell count) :
    0 ≤ 4 * Real.sqrt ((count + 2 : ℕ) : ℝ) *
        suzukiChebyshevRelativeEntropy (suzukiActualEndpointMassRatio count) ∧
      4 * Real.sqrt ((count + 2 : ℕ) : ℝ) *
        suzukiChebyshevRelativeEntropy (suzukiActualEndpointMassRatio count) ≤
          1 / (((count + 2 : ℕ) : ℝ) * Real.sqrt ((count + 2 : ℕ) : ℝ)) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let q := suzukiActualEndpointMassRatio count
  have hb : 0 < b := by dsimp [b]; positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hq : 0 < q := suzukiActualEndpointMassRatio_pos count
  have hH := suzukiChebyshevRelativeEntropy_nonnegative hq.le
  have hHup : suzukiChebyshevRelativeEntropy q ≤ (q - 1) ^ 2 := by
    have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hq) hq.le
    unfold suzukiChebyshevRelativeEntropy
    nlinarith
  obtain ⟨hl, hu⟩ := suzuki_balanced_massRatio_bounds hc
  change 0 ≤ q - 1 at hl
  change q - 1 ≤ 1 / (2 * b) at hu
  refine ⟨by positivity, ?_⟩
  change 4 * Real.sqrt b * suzukiChebyshevRelativeEntropy q ≤ 1 / (b * Real.sqrt b)
  calc
    _ ≤ 4 * Real.sqrt b * (q - 1) ^ 2 := mul_le_mul_of_nonneg_left hHup (by positivity)
    _ ≤ 4 * Real.sqrt b * (1 / (2 * b)) ^ 2 :=
      mul_le_mul_of_nonneg_left (sq_le_sq₀ hl (by positivity) |>.mpr hu) (by positivity)
    _ = _ := by
      field_simp
      nlinarith [Real.sq_sqrt hb.le]

/-- Uniform decay on all balanced cells, with no need to choose a
particular sequence of cutoffs or to assume RH. -/
theorem suzuki_balanced_entropy_uniformly_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ count : ℕ in atTop, SuzukiMassBalancedCell count →
      4 * Real.sqrt ((count + 2 : ℕ) : ℝ) *
        suzukiChebyshevRelativeEntropy (suzukiActualEndpointMassRatio count) < ε := by
  obtain ⟨start, hs⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop start] with count hc
  intro hbal
  have hn : 1 / ε < ((count + 2 : ℕ) : ℝ) :=
    hs.trans_le (by exact_mod_cast (show start ≤ count + 2 by omega))
  have hN : (1 : ℝ) ≤ ((count + 2 : ℕ) : ℝ) := by norm_cast; omega
  have hroot : (1 : ℝ) ≤ Real.sqrt ((count + 2 : ℕ) : ℝ) := Real.one_le_sqrt.mpr hN
  have hden : ((count + 2 : ℕ) : ℝ) ≤
      ((count + 2 : ℕ) : ℝ) * Real.sqrt ((count + 2 : ℕ) : ℝ) := by nlinarith
  have hu := (suzuki_balanced_entropy_bounds hbal).2
  have hi : 1 / (((count + 2 : ℕ) : ℝ) * Real.sqrt ((count + 2 : ℕ) : ℝ)) ≤
      1 / ((count + 2 : ℕ) : ℝ) := one_div_le_one_div_of_le (by positivity) hden
  apply (hu.trans hi).trans_lt
  apply (div_lt_iff₀ (by positivity)).mpr
  have hh := (div_lt_iff₀ hε).mp hn
  nlinarith

/-- The actual endpoint statistic and nonlinear potential differ by at
most `N^(-3/2)` at every balanced cell. Its sign is retained. -/
theorem suzuki_balanced_potential_endpoint_bounds {count : ℕ}
    (hc : SuzukiMassBalancedCell count) :
    -suzukiChebyshevLogAverageError ((count + 2 : ℕ) : ℝ) +
        suzukiArchimedeanSlopeConstant * Real.log ((count + 2 : ℕ) : ℝ) +
        suzukiArchimedeanIntercept -
        1 / (((count + 2 : ℕ) : ℝ) * Real.sqrt ((count + 2 : ℕ) : ℝ)) ≤
      suzukiMassLegendrePotential count ∧
    suzukiMassLegendrePotential count ≤
      -suzukiChebyshevLogAverageError ((count + 2 : ℕ) : ℝ) +
        suzukiArchimedeanSlopeConstant * Real.log ((count + 2 : ℕ) : ℝ) +
        suzukiArchimedeanIntercept := by
  rw [suzukiMassLegendrePotential_eq_actualEndpoint_sub_entropy]
  obtain ⟨hl, hu⟩ := suzuki_balanced_entropy_bounds hc
  constructor <;> linarith

/-- A finite floor for only the balanced nonlinear potentials suffices.
Every other cutoff is omitted from this arithmetic hypothesis. -/
theorem riemannHypothesis_of_suzuki_balanced_potential_eventual_floor (B : ℝ)
    (hb : ∀ᶠ count : ℕ in atTop,
      SuzukiMassBalancedCell count → -B ≤ suzukiMassLegendrePotential count) :
    RiemannHypothesis := by
  have hz : ∀ rho : NontrivialZetaZero, rho.1.re ≤ 1 / 2 := by
    intro rho
    by_contra hn
    have hlow := suzuki_balanced_potential_frequently_below_of_right_half_zero
      rho (lt_of_not_ge hn) (-B)
    obtain ⟨count, hc, hbad⟩ := (hlow.and_eventually hb).exists
    exact (not_lt_of_ge (hbad hc.1)) hc.2
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hz rho
  have hlower := hz rho.conjugatePartner
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
    Complex.one_re, Complex.conj_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

/-- An eventual upper bound on the single signed logarithmic-average
statistic, restricted to balanced cells, implies RH. The entropy correction
is discharged by its explicit vanishing estimate; this arithmetic premise
remains the open problem. -/
theorem riemannHypothesis_of_suzuki_balanced_endpoint_eventual_floor (B : ℝ)
    (hb : ∀ᶠ count : ℕ in atTop, SuzukiMassBalancedCell count →
      suzukiChebyshevLogAverageError ((count + 2 : ℕ) : ℝ) ≤
        suzukiArchimedeanSlopeConstant * Real.log ((count + 2 : ℕ) : ℝ) +
          suzukiArchimedeanIntercept + B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_balanced_potential_eventual_floor (B + 1)
  filter_upwards [hb] with count hc
  intro hbal
  have h := (suzuki_balanced_potential_endpoint_bounds hbal).1
  have hn : (1 : ℝ) ≤ ((count + 2 : ℕ) : ℝ) := by norm_cast; omega
  have hs : (1 : ℝ) ≤ Real.sqrt ((count + 2 : ℕ) : ℝ) := Real.one_le_sqrt.mpr hn
  have hden : 1 ≤ ((count + 2 : ℕ) : ℝ) * Real.sqrt ((count + 2 : ℕ) : ℝ) := by nlinarith
  have he : 1 / (((count + 2 : ℕ) : ℝ) * Real.sqrt ((count + 2 : ℕ) : ℝ)) ≤ 1 :=
    (div_le_one (by positivity)).mpr hden
  linarith [hc hbal]

end
end RiemannGaussian

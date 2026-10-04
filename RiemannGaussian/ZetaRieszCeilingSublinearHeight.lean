/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingAdaptiveFejer

/-!
# A sublinear height price for the whole unchanged signed carrier

Choose the order in the already-proved signed Fejer inequality for the
ENTIRE actual divisor. No prime mask, factorial endpoint or competing
population is removed. The new price is sublinear in logarithmic height,
and is combined with the older cap by taking their minimum. It still
grows with height and is not the required constant ceiling 42/25.
-/

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingSublinearHeight
open ZetaRieszCeilingAdaptiveFejer ZetaRieszCeilingMomentIsolation
open ZetaRieszCeilingWholeHeightBound
open ZetaNearOneBudgetLimit (scale)

/-- One global degree, chosen for the entire actual signed divisor. -/
def degree (u L : ℝ) : ℕ := ⌊log (L+21)/(64*log (2*u))⌋₊

/-- A complete arithmetic price, not a new carrier or a positive core sum. -/
def price (L : ℝ) : ℝ := sqrt (L+21)+(L+21)/(120*log (L+21))

/-- The source-radius excess enters only through its exact logarithm. -/
theorem log_growth_bounds {u : ℝ} (hu : 1/2 < u) (hU : u <= 10001/20000) :
    0 < log (2*u) ∧ log (2*u) <= 1/10000 := by
  have hp : 1 < 2*u := by linarith only [hu]
  refine ⟨log_pos hp,?_⟩
  exact (log_le_sub_one_of_pos (zero_lt_one.trans hp)).trans (by linarith only [hU])

/-- The chosen factorial order is positive and controls the full height
mass once. No sparse or phase-balance condition is imposed. -/
theorem degree_lower {u L : ℝ} (hu : 1/2 < u) (hU : u <= 10001/20000)
    (hL : 0 <= L) :
    150*log (L+21) <= (degree u L : ℝ) := by
  obtain ⟨hg,hgu⟩ := log_growth_bounds hu hU
  have hd : 0 < L+21 := by linarith only [hL]
  have hl : 1 <= log (L+21) := by
    apply (le_log_iff_exp_le hd).mpr
    exact exp_one_lt_three.le.trans (by linarith only [hL])
  let X := log (L+21)/(64*log (2*u))
  have hx : (625/4)*log (L+21) <= X := by
    apply (le_div_iff₀ (by positivity : 0 < 64*log (2*u))).mpr
    have hh := mul_le_mul_of_nonneg_left hgu (by positivity : 0 <= (625/4)*log (L+21)*64)
    nlinarith only [hh]
  have hfloor := Nat.sub_one_lt_floor X
  change X-1 < (degree u L : ℝ) at hfloor
  linarith only [hx,hfloor,hl]

/-- The exact exponential term in the arithmetic price is at most a
square-root height term at the selected moving order. -/
theorem degree_exponential_le {u L : ℝ} (hu : 1/2 < u) (hU : u <= 10001/20000)
    (hL : 0 <= L) :
    (2*u)^(32*degree u L) <= sqrt (L+21) := by
  obtain ⟨hg,_⟩ := log_growth_bounds hu hU
  have hd : 0 < L+21 := by linarith only [hL]
  have hl : 0 <= log (L+21) := log_nonneg (by linarith only [hL])
  have hfloor := Nat.floor_le (div_nonneg hl (by positivity : 0 <= 64*log (2*u)))
  change (degree u L : ℝ) <= log (L+21)/(64*log (2*u)) at hfloor
  have hexp : (32*(degree u L : ℝ))*log (2*u) <= log (L+21)/2 := by
    have hf := (le_div_iff₀ (by positivity : 0 < 64*log (2*u))).mp hfloor
    nlinarith only [hf]
  have he : exp (log (L+21)/2) = sqrt (L+21) := by
    have hs : (exp (log (L+21)/2))^2 = L+21 := by
      rw [<-exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show 2*(log (L+21)/2) = log (L+21) by ring,exp_log hd]
    exact ((sqrt_eq_iff_eq_sq hd.le (exp_pos _).le).mpr hs.symm).symm
  rw [<-exp_log (by linarith only [hu] : 0 < 2*u),<-exp_nat_mul]
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  exact (exp_le_exp.mpr hexp).trans_eq he

/-- All logarithmic-height conventions are retained with an explicit
fixed displacement; none is silently replaced by its asymptotic value. -/
theorem local_height_le_scale_add_ten (y : ℝ) :
    localZetaLogHeight y <= scale y+10 := by
  have h := log_le_log (by positivity : 0 < |y|+22)
    (show |y|+22 <= 11*(|y|+2) by nlinarith only [abs_nonneg y])
  rw [log_mul (by norm_num : (11 : ℝ) ≠ 0) (by positivity : |y|+2 ≠ 0)] at h
  have hl : log (11 : ℝ) <= 10 := by
    simpa only [show (11 : ℝ)-1 = 10 by norm_num] using
      log_le_sub_one_of_pos (by norm_num : 0 < (11 : ℝ))
  change log (|y|+22) <= log (|y|+2)+10
  linarith only [h,hl]

/-- The global signed Fejer degree-price inequality gives a genuinely
sublinear arithmetic multiplicity price, throughout the original strip. -/
theorem multiplicity_le_price (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho ->
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re <= 10001/20000) :
    (analyticZetaZeroMultiplicity rho : ℝ) <= price (scale rho.1.im) := by
  let u := 3/2-rho.1.re
  let L := scale rho.1.im
  have hu : 1/2 < u := by dsimp only [u]; linarith [rho.re_lt_one]
  have hl : 0 <= L := (ZetaNearOneBudgetLimit.scale_pos rho.1.im).le
  have hg : 0 < log (L+21) := log_pos (by linarith only [hl])
  have hd := degree_lower hu hU hl
  have hdn : 0 < degree u L := by
    have hp : (0 : ℝ) < degree u L := lt_of_lt_of_le (by positivity) hd
    exact_mod_cast hp
  have hb := multiplicity_le_degree_price rho hrho hexposed hU (degree u L) hdn
  have hh := local_height_le_scale_add_ten rho.1.im
  have hdm : (5/4)*(localZetaLogHeight rho.1.im+11)/(degree u L : ℝ) <=
      (L+21)/(120*log (L+21)) := by
    have hden : 0 < (degree u L : ℝ) := by exact_mod_cast hdn
    apply (div_le_div_iff₀ hden (by positivity : 0 < 120*log (L+21))).mpr
    change localZetaLogHeight rho.1.im <= L+10 at hh
    have hp := mul_le_mul_of_nonneg_left hd (by linarith only [hl] : 0 <= L+21)
    have hh' := mul_le_mul_of_nonneg_right
      (show localZetaLogHeight rho.1.im+11 <= L+21 by linarith only [hh])
      (by positivity : 0 <= 150*log (L+21))
    nlinarith only [hp,hh']
  exact hb.trans (add_le_add (degree_exponential_le hu hU hl) hdm)

/-- Preserve every previously proved ceiling cap by taking the minimum. -/
def combinedCap (L : ℝ) : ℝ := min (heightCap L) (price L)

/-- A complete bound on actual multiplicity, not on a synthetic divisor. -/
theorem multiplicity_le_combinedCap (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho ->
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling) :
    (analyticZetaZeroMultiplicity rho : ℝ) <= combinedCap (scale rho.1.im) := by
  have hn : 1-rho.1.re <= 1/20000 := by
    norm_num only [ZetaRieszWideOwnerAudit.radiusCeiling] at hU
    linarith only [hU]
  exact le_min (multiplicity_le_heightCap rho hn) (multiplicity_le_price rho hrho hexposed hU)

/-- The upper comparison remains signed, including its linear prime term. -/
def signedPrice (u L : ℝ) : ℝ :=
  -combinedCap L+ZetaRieszMaskSupport.retainedCost u*(combinedCap L)^2

/-- The actual full source receives the new arithmetic bound at every
fixed height; no literal sector or adjacent-order commutator is dropped. -/
theorem source_le_signedPrice (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho ->
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling) :
    -(analyticZetaZeroMultiplicity rho : ℝ)+
      (analyticZetaZeroMultiplicity rho : ℝ)^2*ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) <=
        signedPrice (3/2-rho.1.re) (scale rho.1.im) := by
  have hm : (1 : ℝ) <= analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hc := multiplicity_le_combinedCap rho hrho hexposed hU
  have hu : 1/2 <= 3/2-rho.1.re := by linarith [rho.re_lt_one]
  have hcost := ZetaRieszJointFloor.retainedCost_gt_nine_tenths hu hU
  have hh : 0 <= ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re)*
      (combinedCap (scale rho.1.im)+analyticZetaZeroMultiplicity rho)-1 := by
    have hsum : (2 : ℝ) <= combinedCap (scale rho.1.im)+analyticZetaZeroMultiplicity rho := by
      linarith only [hm,hc]
    have hp := mul_le_mul_of_nonneg_left hsum
      (by linarith only [hcost] : 0 <= ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re))
    linarith only [hp,hcost]
  have hp := mul_nonneg (sub_nonneg.mpr hc) hh
  unfold signedPrice
  nlinarith only [hp]

/-- An upper inequality for the SAME whole `joinedPhysical` at every
fixed height. The price remains height dependent; 42/25 is still open. -/
theorem eventually_joinedPhysical_signed_ceiling (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho ->
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re <
        signedPrice (3/2-rho.1.re) (scale rho.1.im)+ε := by
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (ZetaRieszJoinedPhysical.tendsto_joinedPhysical_exact_source rho hrho hexposed hU)
  have hb := source_le_signedPrice rho hrho hexposed hU
  have hg : (-(analyticZetaZeroMultiplicity rho : ℂ)+
      (analyticZetaZeroMultiplicity rho : ℂ)^2*
        (ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) : ℂ)).re <
      signedPrice (3/2-rho.1.re) (scale rho.1.im)+ε := by
    norm_num only [Complex.add_re,Complex.neg_re,pow_two,Complex.mul_re,
      Complex.natCast_re,Complex.natCast_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    nlinarith only [hb,hε]
  simpa only [Function.comp_apply] using hs.eventually (gt_mem_nhds hg)

/-- The complete arithmetic price is sublinear in logarithmic height.
This is a height asymptotic, not source-order decay of the main carrier. -/
theorem price_div_height_tendsto_zero :
    Tendsto (fun L : ℝ => price L/L) atTop (𝓝 0) := by
  have hD : Tendsto (fun L : ℝ => L+21) atTop atTop :=
    tendsto_atTop_add_const_right atTop 21 tendsto_id
  have hr : Tendsto (fun L : ℝ => (L+21)/L) atTop (𝓝 1) := by
    have hv : Tendsto (fun L : ℝ => 21/L) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have ht := hv.const_add 1
    norm_num only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hl
    field_simp [hl.ne']
  have hsqrt : Tendsto (fun L : ℝ => 1/sqrt (L+21)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_sqrt_atTop.comp hD)
  have hlog : Tendsto (fun L : ℝ => 1/log (L+21)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_log_atTop.comp hD)
  have h1 := hsqrt.mul hr
  have h2 := (hr.mul hlog).const_mul (1/120 : ℝ)
  have hs := h1.add h2
  norm_num only [zero_mul,mul_zero,zero_add] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hl
  have hd : L+21 ≠ 0 := by linarith only [hl]
  have hg : log (L+21) ≠ 0 := ne_of_gt (log_pos (by linarith only [hl]))
  rw [<-sqrt_div_self']
  unfold price
  field_simp [hl.ne',hd,hg]

/-- The previous COMPLETE Gaussian cap keeps its linear height term.
This lower bound is used only to compare independently proved prices. -/
theorem heightCap_lower {L : ℝ} (hL : 60001 <= L) :
    L/217000 <= heightCap L := by
  have hg : 0 <= log L := log_nonneg (by linarith only [hL])
  unfold heightCap
  rw [if_neg (by linarith only [hL] : ¬ L <= 60000),le_min_iff]
  constructor
  · unfold cost smallUnit
    nlinarith only [hL,hg]
  · unfold cost wideUnit
    nlinarith only [hL,hg]

/-- At all sufficiently large heights the new complete price beats ANY
fixed positive fraction of the old one. No numerical threshold is claimed. -/
theorem eventually_price_lt_fraction_heightCap {q : ℝ} (hq : 0 < q) :
    ∀ᶠ L : ℝ in atTop, price L < q*heightCap L := by
  have ht := price_div_height_tendsto_zero.eventually
    (gt_mem_nhds (show (0 : ℝ) < q/217000 by positivity))
  filter_upwards [ht,eventually_ge_atTop (60001 : ℝ)] with L hp hl
  have hpos : 0 < L := by linarith only [hl]
  have hh := heightCap_lower hl
  have hp' := (div_lt_iff₀ hpos).mp hp
  have hm := mul_le_mul_of_nonneg_left hh hq.le
  nlinarith only [hp',hm]

/-- A polynomial comparison retains the negative ordinary-prime term.
Both multiplicity caps are at least one in its actual application. -/
theorem signed_polynomial_fraction {c M B q : ℝ} (hc : 9/10 < c)
    (hB : 1 <= B) (hBM : B <= q*M) (hq0 : 0 <= q) (hq1 : q <= 1) :
    -B+c*B^2 <= q^2*(-M+c*M^2) := by
  have hqM : 1 <= q*M := hB.trans hBM
  have hM : 0 <= M := by
    by_contra! h
    have hp := mul_nonpos_of_nonneg_of_nonpos hq0 h.le
    linarith only [hqM,hp]
  have hs : 0 <= c*(q*M+B)-1 := by
    have hh : (2 : ℝ) <= q*M+B := by linarith only [hB,hqM]
    have hmul := mul_le_mul_of_nonneg_left hh (by linarith only [hc] : 0 <= c)
    linarith only [hc,hmul]
  have hp := mul_nonneg (sub_nonneg.mpr hBM) hs
  have hq : 0 <= q-q^2 := by nlinarith only [hq0,hq1]
  have hp' := mul_nonneg hq hM
  nlinarith only [hp,hp']

/-- The new signed price preserves the old bound at EVERY actual
eligible height, including all its previously paid simplicity ranges. -/
theorem actual_signedPrice_le_previous (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho ->
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling) :
    signedPrice (3/2-rho.1.re) (scale rho.1.im) <=
      signedCeiling (3/2-rho.1.re) (scale rho.1.im) := by
  have hm : (1 : ℝ) <= analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hb := multiplicity_le_combinedCap rho hrho hexposed hU
  have hc := ZetaRieszJointFloor.retainedCost_gt_nine_tenths
    (show 1/2 <= 3/2-rho.1.re by linarith [rho.re_lt_one]) hU
  have he := signed_polynomial_fraction hc (hm.trans hb)
    (show combinedCap (scale rho.1.im) <= 1*heightCap (scale rho.1.im) by
      simpa only [one_mul,combinedCap] using min_le_left (heightCap (scale rho.1.im)) (price (scale rho.1.im)))
    (by norm_num : (0 : ℝ) <= 1) (le_refl (1 : ℝ))
  simpa only [signedPrice,signedCeiling,one_pow,one_mul] using he

/-- An ACTUAL upper bound for the WHOLE unchanged carrier whose complete
height price is at most one quarter of the previous one at all sufficiently
large heights. This is not one quarter of the constant-ceiling gap. -/
theorem exists_quarter_price_native_ceiling :
    ∃ L0 : ℝ, ∀ rho : NontrivialZetaZero,
      1/2 < rho.1.re ->
      (∀ tau : NontrivialZetaZero, tau ≠ rho ->
        3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖) ->
      3/2-rho.1.re <= ZetaRieszWideOwnerAudit.radiusCeiling ->
      L0 <= scale rho.1.im ->
      ∀ ε : ℝ, 0 < ε -> ∀ᶠ j : ℕ in atTop,
        (((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
          ZetaRieszGammaJoint.joinedPhysical (3/2-rho.1.re) rho.1.im
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
            (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re <
          (1/4)*signedCeiling (3/2-rho.1.re) (scale rho.1.im)+ε := by
  obtain ⟨L0,hL0⟩ := eventually_atTop.mp
    (eventually_price_lt_fraction_heightCap (by norm_num : 0 < (1/2 : ℝ)))
  refine ⟨L0,?_⟩
  intro rho hrho hexposed hU hheight ε hε
  have hm : (1 : ℝ) <= analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hb := multiplicity_le_combinedCap rho hrho hexposed hU
  have hc := ZetaRieszJointFloor.retainedCost_gt_nine_tenths
    (show 1/2 <= 3/2-rho.1.re by linarith [rho.re_lt_one]) hU
  have hfrac : combinedCap (scale rho.1.im) <= (1/2)*heightCap (scale rho.1.im) :=
    (min_le_right _ _).trans (hL0 _ hheight).le
  have hprice := signed_polynomial_fraction hc (hm.trans hb) hfrac
    (by norm_num : 0 <= (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) <= 1)
  have ht := eventually_joinedPhysical_signed_ceiling rho hrho hexposed hU hε
  filter_upwards [ht] with j hj
  apply hj.trans_le
  unfold signedPrice signedCeiling
  norm_num only at hprice
  linarith only [hprice]

/-- The exact already-proved scalar degree price, without optimization. -/
def degreePrice (u H : ℝ) (d : ℕ) : ℝ :=
  (2*u)^(32*d)+(5/4)*(H+11)/(d : ℝ)

/-- Even the BEST degree choice cannot make this scalar method a
constant multiplicity cap. This is a PRICE lower bound, not an actual
zero-multiplicity lower bound or a carrier-divergence theorem. -/
theorem degreePrice_uniform_lower {u H : ℝ} (hu : 1/2 < u) (hH : 0 <= H)
    {d : ℕ} (hd : 0 < d) :
    sqrt (160*(2*u-1)*(H+11)) <= degreePrice u H d := by
  have hb : 0 < 2*u-1 := by linarith only [hu]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hpow := one_add_mul_le_pow (show (-2 : ℝ) <= 2*u-1 by linarith only [hu]) (32*d)
  rw [show 1+(2*u-1) = 2*u by ring] at hpow
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hpow
  have hA : 0 <= (2*u)^(32*d) := by positivity
  have hB : 0 <= (5/4)*(H+11)/(d : ℝ) := by positivity
  have hprod := mul_le_mul_of_nonneg_right
    (show (32*(d : ℝ))*(2*u-1) <= (2*u)^(32*d) by linarith only [hpow]) hB
  have he : (32*(d : ℝ))*(2*u-1)*((5/4)*(H+11)/(d : ℝ)) =
      40*(2*u-1)*(H+11) := by
    field_simp [hdpos.ne']
    ring
  rw [he] at hprod
  apply (sqrt_le_iff).mpr
  constructor
  · unfold degreePrice
    linarith only [hA,hB]
  · unfold degreePrice
    nlinarith only [hprod,sq_nonneg ((2*u)^(32*d)-(5/4)*(H+11)/(d : ℝ))]

/-- At any fixed source radius above 1/2, every possible positive
degree eventually has a price above any prescribed constant. -/
theorem eventually_all_degree_prices_gt {u : ℝ} (hu : 1/2 < u) (M : ℝ) :
    ∀ᶠ H : ℝ in atTop, ∀ d : ℕ, 0 < d -> M < degreePrice u H d := by
  have hp : 0 < 160*(2*u-1) := by nlinarith only [hu]
  have hH : Tendsto (fun H : ℝ => H+11) atTop atTop :=
    tendsto_atTop_add_const_right atTop 11 tendsto_id
  have ht := tendsto_sqrt_atTop.comp (hH.const_mul_atTop hp)
  filter_upwards [ht.eventually_gt_atTop M,eventually_ge_atTop (0 : ℝ)] with H hgt hnon d hd
  exact hgt.trans_le (degreePrice_uniform_lower hu hnon hd)

end RiemannGaussian.ZetaRieszCeilingSublinearHeight

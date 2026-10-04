/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFactorialCutoff

/-!
# Audit the proposed 1664/4096 to 1665/4096 transition

This is the same completed quadratic at a fixed order and height. The
cutoff change is not an independent arithmetic saving: the exact transition
and the original literal carrier's ledger remain explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCutoffTransitionAudit
open ZetaRieszFactorialCutoff ZetaRieszPairPrimePowerPayment
open ZetaRieszJoinedSourceError ZetaRieszPairFloorAllMultiplicity

/-- Original factorial prefix endpoint, with its literal integer rounding. -/
def cutoff0 (N : ℕ) : ℕ := 13*N/32

/-- Candidate one-unit-in-4096 wider factorial prefix. -/
def cutoff1 (N : ℕ) : ℕ := 1665*N/4096

/-- The research target is the exact narrow completed transition. -/
def transition (a : ℕ → ℂ) (u : ℝ) (N : ℕ) : ℂ :=
  evaluation a u N (cutoff0 N) - evaluation a u N (cutoff1 N)

/-- Its selected source is kept signed. -/
def transitionSource (u : ℝ) : ℝ := source u (13/32) - source u (1665/4096)

/-- The old endpoint is exactly 1664/4096, even off the native schedule. -/
theorem cutoff0_eq (N : ℕ) : cutoff0 N = 1664*N/4096 := by
  unfold cutoff0
  omega

theorem cutoff_bounds {N : ℕ} (hN : 8 ≤ N) :
    N ≤ 4*cutoff0 N ∧ N ≤ 4*cutoff1 N ∧
      cutoff0 N ≤ cutoff1 N ∧ 2*cutoff1 N ≤ N := by
  unfold cutoff0 cutoff1
  omega

private theorem floor_ratio (p q : ℕ) (hq : 0 < q) (hpq : p ≤ q) :
    Tendsto (fun N : ℕ => ((p*N/q : ℕ) : ℝ)/(N+1)) atTop (𝓝 ((p : ℝ)/q)) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hpqr : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have he : Tendsto (fun N : ℕ => ((p*N/q : ℕ) : ℝ)/(N+1)-(p : ℝ)/q)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => (2 : ℝ)/(N+1)) ?_
      (hn.const_div_atTop 2)
    intro N
    have hm := Nat.mod_lt (p*N) hq
    have hd := Nat.div_add_mod (p*N) q
    have hlo : p*N < q*(p*N/q)+q := by omega
    have hhi : q*(p*N/q) ≤ p*N := by omega
    have hlor : (p : ℝ)*N < (q : ℝ)*((p*N/q : ℕ) : ℝ)+q := by exact_mod_cast hlo
    have hhir : (q : ℝ)*((p*N/q : ℕ) : ℝ) ≤ (p : ℝ)*N := by exact_mod_cast hhi
    have hscale : (p : ℝ)/q*q=p := div_mul_cancel₀ _ hqr.ne'
    have hb : |((p*N/q : ℕ) : ℝ)-(p : ℝ)/q*(N+1)| ≤ 2 := by
      apply abs_le.mpr
      constructor <;> nlinarith only [hlor, hhir, hscale, hpqr, hqr, Nat.cast_nonneg (α := ℝ) p]
    rw [Real.norm_eq_abs]
    calc
      _ = |((p*N/q : ℕ) : ℝ)-(p : ℝ)/q*(N+1)|/(N+1) := by
        rw [show ((p*N/q : ℕ) : ℝ)/(N+1)-(p : ℝ)/q =
          (((p*N/q : ℕ) : ℝ)-(p : ℝ)/q*(N+1))/(N+1) by field_simp,
          abs_div, abs_of_pos (by positivity : (0 : ℝ) < N+1)]
      _ ≤ _ := div_le_div_of_nonneg_right hb (by positivity)
  convert he.add_const ((p : ℝ)/q) using 1
  · funext N; ring
  · simp

theorem cutoff0_ratio :
    Tendsto (fun N : ℕ => (cutoff0 N : ℝ)/(N+1)) atTop (𝓝 (13/32)) :=
  floor_ratio 13 32 (by norm_num) (by norm_num)

theorem cutoff1_ratio :
    Tendsto (fun N : ℕ => (cutoff1 N : ℝ)/(N+1)) atTop (𝓝 (1665/4096)) :=
  floor_ratio 1665 4096 (by norm_num) (by norm_num)

/-- The original native dyadic schedule has no 4096 floor ambiguity
from j=6 onward: its order includes 2^(j+6). -/
theorem native_divisible {j : ℕ} (hj : 6 ≤ j) :
    4096 ∣ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by
  unfold ZetaRieszPrimeCountFrequency.dyadicMomentOrder
    ZetaRieszPrimeCountFrequency.dyadicPrimeCount
  have hp : (2 : ℕ)^12 ∣ 2^(j+6) := pow_dvd_pow 2 (by omega)
  have he : 8*(j+4)*2^(j+3) = (j+4)*2^(j+6) := by
    rw [show j+6=j+3+3 by omega, pow_add]
    ring
  rw [he]
  have hp' : 4096 ∣ 2^(j+6) := by norm_num at hp; exact hp
  exact hp'.mul_left (j+4)

/-- On that schedule the thin transition has exactly N/4096 steps. -/
theorem native_width {j : ℕ} (hj : 6 ≤ j) :
    cutoff1 (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) -
      cutoff0 (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) =
        ZetaRieszPrimeCountFrequency.dyadicMomentOrder j / 4096 := by
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  have hd : 4096 ∣ N := native_divisible hj
  have he := Nat.div_mul_cancel hd
  change cutoff1 N-cutoff0 N=N/4096
  rw [cutoff0_eq]
  unfold cutoff1
  rw [← he, show 1665*(N/4096*4096)=1665*(N/4096)*4096 by ring,
    show 1664*(N/4096*4096)=1664*(N/4096)*4096 by ring]
  omega

/-- The exact thin target contains only the consecutive centered moments
identified by the user, with unchanged N, u, height and array. -/
theorem transition_eq_sum (a : ℕ → ℂ) (u : ℝ) {N : ℕ} (hN : 8 ≤ N) :
    transition a u N = ∑ k ∈ Finset.Ico (cutoff0 N) (cutoff1 N),
      ((N+1 : ℕ) : ℂ)/((k+1 : ℕ) : ℂ)*a k*
        (a (N-k-1)/((N-k : ℕ) : ℂ) -
          a (N-k)/((u : ℂ)*SquarefreeVaughanLogSource.length u N)) :=
  evaluation_sub_eq_sum a u (cutoff_bounds hN).2.2.1 (cutoff_bounds hN).2.2.2

/-- The real constant-array limit is checked independently for the
candidate endpoint; no numerical probe is used as an assumption. -/
theorem candidate_constant_tendsto (c : ℂ) {u : ℝ} (hu : 0 < u) (huq : u ≤ 3/5) :
    Tendsto (fun N : ℕ => evaluation (fun _ => c) u N (cutoff1 N))
      atTop (𝓝 (c^2*(source u (1665/4096) : ℂ))) :=
  evaluation_const_tendsto c cutoff1 hu huq (by norm_num) (by norm_num)
    ((eventually_ge_atTop 8).mono fun N hN => (cutoff_bounds hN).2.2.2) cutoff1_ratio

/-- BOTH sides of the constant transition have their exact source limit. -/
theorem constant_transition_tendsto (c : ℂ) {u : ℝ} (hu : 0 < u) (huq : u ≤ 3/5) :
    Tendsto (transition (fun _ => c) u) atTop (𝓝 (c^2*(transitionSource u : ℂ))) := by
  have h0 := evaluation_const_tendsto c cutoff0 hu huq (by norm_num) (by norm_num)
    ((eventually_ge_atTop 8).mono fun N hN => by have hh := cutoff_bounds hN; omega)
    cutoff0_ratio
  convert h0.sub (candidate_constant_tendsto c hu huq) using 1
  · rfl
  · unfold transitionSource
    push_cast
    ring

/-- Elementary rational bounds on the exact damping coefficient, uniform
on the entire requested radius interval. -/
theorem damping_bounds {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    (6931/10000 : ℝ) ≤ -2*u*log u ∧ -2*u*log u ≤ 693148/1000000 := by
  have hu0 : 0 < u := by linarith only [hu]
  have huU : u ≤ 10001/20000 := hU
  have hlog2lo : (69314718/100000000 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hlog2hi : log 2 < (693148/1000000 : ℝ) := by linarith [log_two_lt_d9]
  have hh := log_le_sub_one_of_pos (show 0 < 2*u by positivity)
  rw [log_mul (by norm_num) hu0.ne'] at hh
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*u by positivity)
  have hml := mul_le_mul_of_nonneg_left hlog2lo (show 0 ≤ 2*u by positivity)
  have hq := mul_nonneg (show 0 ≤ u-1/2 by linarith only [hu])
    (show 0 ≤ 10001/20000-u by linarith only [huU])
  have hi := one_sub_inv_le_log_of_pos (show 0 < 2*u by positivity)
  rw [log_mul (by norm_num) hu0.ne'] at hi
  have him := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2*u by positivity)
  have he : 2*u*(1-(2*u)⁻¹)=2*u-1 := by field_simp
  rw [he] at him
  have hp := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ 2*u-1 by linarith only [hu])
    (show log 2-1 ≤ 0 by linarith only [hlog2hi])
  constructor
  · nlinarith only [hm,hml,hq]
  · nlinarith only [him,hp,hlog2hi]

/-- The proposed new source is indeed below 399/5000 throughout the strip.
This is a scalar source statement, not a bound on the original carrier. -/
theorem candidate_source_lt_target {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    source u (1665/4096) < (399/5000 : ℝ) := by
  have hd := damping_bounds hu hU
  have hp : 0 < -2*u*log u := by linarith only [hd.1]
  have ha : log (2431/1665 : ℝ) < 378478/1000000 := by
    apply (log_lt_iff_lt_exp (by norm_num)).mpr
    have he := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 378478/1000000) 10
    norm_num [Finset.sum_range_succ] at he
    linarith only [he]
  have hb : (900185/1000000 : ℝ) < log (4096/1665) := by
    have hh := sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 2431/5761)
      (by norm_num : (2431/5761 : ℝ) < 1) 8
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  have hm := mul_le_mul_of_nonneg_left ha.le hp.le
  have hn := mul_le_mul_of_nonneg_right hd.2
    (show (0 : ℝ) ≤ 1+378478/1000000-399/5000 by norm_num)
  have hs : source u (1665/4096) =
      1 + log (2431/1665 : ℝ) - log (4096/1665)/(-2*u*log u) := by
    norm_num [source]
  rw [hs]
  have hh : 1+log (2431/1665 : ℝ)-399/5000 < log (4096/1665)/(-2*u*log u) := by
    apply (lt_div_iff₀ hp).mpr
    nlinarith only [hm,hn,hb]
  linarith only [hh]

/-- Exact signed change of the limiting source; its two logarithms are
the narrow endpoint ratios, not separately paid positive allowances. -/
theorem transitionSource_eq (u : ℝ) :
    transitionSource u = log (31635/31603 : ℝ) - log (1665/1664)/(-2*u*log u) := by
  have ha := log_div (by norm_num : (19/13 : ℝ) ≠ 0) (by norm_num : (2431/1665 : ℝ) ≠ 0)
  have hb := log_div (by norm_num : (32/13 : ℝ) ≠ 0) (by norm_num : (4096/1665 : ℝ) ≠ 0)
  norm_num at ha hb
  norm_num [transitionSource, source]
  rw [ha,hb]
  ring

/-- The supposedly saved transition has a positive, source-scale cost
uniformly greater than 1/7000 even at the upper radius endpoint. -/
theorem transitionSource_gt {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    (1/7000 : ℝ) < transitionSource u := by
  have hd := (damping_bounds hu hU).1
  have hp : 0 < -2*u*log u := by linarith only [hd]
  have ha : (1012/1000000 : ℝ) < log (31635/31603) := by
    have hh := sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 16/31619)
      (by norm_num : (16/31619 : ℝ) < 1) 1
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  have hb : log (1665/1664 : ℝ) ≤ 1/1664 := by
    have hh := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1665/1664)
    norm_num at hh
    exact hh
  have hquot : log (1665/1664 : ℝ)/(-2*u*log u) ≤ (1/1664)/(6931/10000) :=
    div_le_div₀ (by norm_num) hb (by norm_num) hd
  rw [transitionSource_eq]
  nlinarith only [ha,hquot]

private theorem endpoint0_bounds :
    ∀ᶠ N : ℕ in atTop, N ≤ 4*cutoff0 N ∧ 2*cutoff0 N ≤ N := by
  filter_upwards [eventually_ge_atTop 8] with N hN
  have hh := cutoff_bounds hN
  constructor
  · exact hh.1
  · omega

private theorem endpoint1_bounds :
    ∀ᶠ N : ℕ in atTop, N ≤ 4*cutoff1 N ∧ 2*cutoff1 N ≤ N := by
  filter_upwards [eventually_ge_atTop 8] with N hN
  exact ⟨(cutoff_bounds hN).2.1, (cutoff_bounds hN).2.2.2⟩

/-- The apparent smaller source survives in the actual completed array,
but the complementary transition must still be added to the original ledger. -/
theorem candidate_ordinary_source (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N : ℕ => evaluation (ordinaryArray (3/2-rho.1.re) rho.1.im)
      (3/2-rho.1.re) N (cutoff1 N)) atTop
        (𝓝 ((analyticZetaZeroMultiplicity rho : ℂ)^2*
          (source (3/2-rho.1.re) (1665/4096) : ℂ))) :=
  tendsto_ordinary_source rho hrho hexposed hU cutoff1 (by norm_num) (by norm_num)
    endpoint1_bounds cutoff1_ratio

/-- Every actual ordinary-prime transition retains exactly m^2 times the
positive selected transition. Exposure pays competitors, not this source. -/
theorem ordinary_transition_tendsto (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (transition (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re))
      atTop (𝓝 (((analyticZetaZeroMultiplicity rho : ℝ)^2*
        transitionSource (3/2-rho.1.re) : ℝ) : ℂ)) := by
  have h0 := tendsto_ordinary_source rho hrho hexposed hU cutoff0
    (by norm_num) (by norm_num) endpoint0_bounds cutoff0_ratio
  convert h0.sub (candidate_ordinary_source rho hrho hexposed hU) using 1
  · rfl
  · unfold transitionSource
    push_cast
    ring

/-- Proper prime powers do not alter the conclusion; the full von
Mangoldt transition carries the same quadratic multiplicity and sign. -/
theorem mangoldt_transition_tendsto (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (transition (mangoldtArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re))
      atTop (𝓝 (((analyticZetaZeroMultiplicity rho : ℝ)^2*
        transitionSource (3/2-rho.1.re) : ℝ) : ℂ)) := by
  have h0 := tendsto_mangoldt_source rho hrho hexposed hU cutoff0
    (by norm_num) (by norm_num) endpoint0_bounds cutoff0_ratio
  have h1 := tendsto_mangoldt_source rho hrho hexposed hU cutoff1
    (by norm_num) (by norm_num) endpoint1_bounds cutoff1_ratio
  convert h0.sub h1 using 1
  · rfl
  · unfold transitionSource
    push_cast
    ring

/-- The proposed centered moment has a nonzero signed selected limit.
The actual source-error summability justifies the moving array indices. -/
theorem ordinary_centered_tendsto (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N : ℕ => ((N+1 : ℕ) : ℂ)*
      centeredDefect (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re)
        N (N-cutoff1 N-1)) atTop
          (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*
            ((4096/2431 : ℝ) - 1/(-2*(3/2-rho.1.re)*log (3/2-rho.1.re)) : ℂ))) := by
  have hs := (summable_ordinary_source_error rho hrho hexposed hU).tendsto_atTop_zero
  have hz : Tendsto (fun n : ℕ => ordinaryArray (3/2-rho.1.re) rho.1.im n +
      (analyticZetaZeroMultiplicity rho : ℂ)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hs
  have ha : Tendsto (ordinaryArray (3/2-rho.1.re) rho.1.im) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
    simpa only [add_sub_cancel_right, zero_sub] using hz.sub_const (analyticZetaZeroMultiplicity rho : ℂ)
  have hu : 0 < 3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  have huq : 3/2-rho.1.re ≤ (3/5 : ℝ) :=
    hU.trans (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
  convert tendsto_centered_defect _ _ ha cutoff1 hu huq (by norm_num : (1665/4096 : ℝ) < 1/2)
    (endpoint1_bounds.mono fun _ h => by omega) cutoff1_ratio using 1
  norm_num

/-- Every selected recurrence coefficient is strictly negative, separated
from zero by 6/25 per unit multiplicity after multiplying by N+1. -/
theorem centered_source_negative {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    (1/(-2*u*log u) - 4096/2431 : ℝ) < -6/25 := by
  have hd := (damping_bounds hu hU).1
  have hp : 0 < -2*u*log u := by linarith only [hd]
  have hi : (1 : ℝ)/(-2*u*log u) ≤ 1/(6931/10000) :=
    one_div_le_one_div_of_le (by norm_num) hd
  linarith only [hi]

/-- Conditional signed LOWER bound for the thin transition itself. This
proves why it cannot be discarded as a zero-source correction. -/
theorem eventually_transition_source_lower (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop,
      (analyticZetaZeroMultiplicity rho : ℝ)^2/7000 <
        (transition (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N).re := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (ordinary_transition_tendsto rho hrho hexposed hU)
  simp only [Complex.ofReal_re] at ht
  have hu : 1/2 ≤ 3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  have hm : 0 < (analyticZetaZeroMultiplicity rho : ℝ)^2 := by
    have hh := analyticZetaZeroMultiplicity_positive rho
    have hp : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by exact_mod_cast hh
    positivity
  have hgap := mul_lt_mul_of_pos_left (transitionSource_gt hu hU) hm
  simpa only [div_eq_mul_inv, one_mul, Function.comp_def] using
    ht.eventually (lt_mem_nhds hgap)

/-- A strict improvement over the exact selected transition is a new
arithmetic hypothesis. It cannot follow by centering/exposure alone. -/
theorem false_of_transition_cofinal_upper (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (orders : ℕ → ℕ) (ho : Tendsto orders atTop atTop)
    {b : ℝ} (hb : b < (analyticZetaZeroMultiplicity rho : ℝ)^2*
      transitionSource (3/2-rho.1.re)) (err : ℕ → ℝ) (he : Tendsto err atTop (𝓝 0))
    (hf : ∃ᶠ j in atTop, (transition (ordinaryArray (3/2-rho.1.re) rho.1.im)
      (3/2-rho.1.re) (orders j)).re ≤ b+err j) : False := by
  have ht := (Complex.continuous_re.continuousAt.tendsto.comp
    (ordinary_transition_tendsto rho hrho hexposed hU)).comp ho
  simp only [Complex.ofReal_re] at ht
  have hh : (analyticZetaZeroMultiplicity rho : ℝ)^2*
      transitionSource (3/2-rho.1.re) ≤ b := by
    simpa only [sub_zero] using le_of_tendsto_of_frequently (ht.sub he)
      (hf.mono fun j hj => by dsimp only [Function.comp_def]; linarith only [hj])
  exact (not_le_of_gt hb) hh

/-- The original literal main contains candidate PLUS transition. This
ledger is exact and uses the previously reached completion only. -/
theorem prefix_candidate_ledger (u y : ℝ) (N : ℕ) :
    ZetaRieszPairPrefixPayment.prefixPairDefect u y N -
      (evaluation (ordinaryArray u y) u N (cutoff1 N) + transition (ordinaryArray u y) u N) =
    ZetaRieszPairPrefixPayment.prefixPairDefect u y N -
      ZetaRieszSelbergSourceAudit.harmonicEvaluation (ordinaryArray u y) u N := by
  unfold transition cutoff0
  rw [evaluation_original]
  ring

/-- No new physical completion is undertaken: both existing geometric
errors stay attached to the EXACT original candidate-plus-transition ledger. -/
theorem norm_prefix_candidate_ledger_le {u y : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ |y|)
    {N : ℕ} (hN : 65536 ≤ N) :
    ‖ZetaRieszPairPrefixPayment.prefixPairDefect u y N -
      (evaluation (ordinaryArray u y) u N (cutoff1 N) + transition (ordinaryArray u y) u N)‖ ≤
        ZetaRieszPairWholeCompletion.wholeCompletionBudget N +
          ZetaRieszPairJointQuadratic.squareBudget u N := by
  rw [prefix_candidate_ledger]
  exact ZetaRieszJoinedPhaseRadius.norm_prefix_sub_ordinary_le hu hU hy hN

/-- The smaller candidate and its transition add back to the original
selected source exactly. Raising K earns no free floor credit. -/
theorem candidate_plus_transition_source (u : ℝ) :
    source u (1665/4096) + transitionSource u =
      1-ZetaRieszMaskSupport.retainedCost u := by
  unfold transitionSource
  rw [add_sub_cancel]
  norm_num [source, ZetaRieszMaskSupport.retainedCost]
  ring

/-- An explicit quantitative comparison retains the narrow transition's
selected mass. Only the already-proved source-array error tends to zero. -/
theorem norm_transition_sub_selected_le (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {N : ℕ} (hN : 65536 ≤ N) :
    ‖transition (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N -
      transition (fun _ => -(analyticZetaZeroMultiplicity rho : ℂ)) (3/2-rho.1.re) N‖ ≤
        44*((analyticZetaZeroMultiplicity rho : ℝ)+sourceErrorMass rho)*
          sourceErrorMass rho/(N : ℝ) := by
  have h0 := norm_evaluation_sub_selected_le rho hrho hexposed hU hN
    (cutoff_bounds (by omega : 8 ≤ N)).1
    (show 2*cutoff0 N ≤ N by have hh := cutoff_bounds (by omega : 8 ≤ N); omega)
  have h1 := norm_evaluation_sub_selected_le rho hrho hexposed hU hN
    (cutoff_bounds (by omega : 8 ≤ N)).2.1
    (cutoff_bounds (by omega : 8 ≤ N)).2.2.2
  have he : transition (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N -
      transition (fun _ => -(analyticZetaZeroMultiplicity rho : ℂ)) (3/2-rho.1.re) N =
      (evaluation (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N (cutoff0 N) -
        evaluation (fun _ => -(analyticZetaZeroMultiplicity rho : ℂ)) (3/2-rho.1.re) N (cutoff0 N)) -
      (evaluation (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N (cutoff1 N) -
        evaluation (fun _ => -(analyticZetaZeroMultiplicity rho : ℂ)) (3/2-rho.1.re) N (cutoff1 N)) := by
    unfold transition
    ring
  rw [he]
  exact ((norm_sub_le _ _).trans (add_le_add h0 h1)).trans_eq (by ring)

/-- The exact original whole-support payment transfers the source-scale
cutoff discrepancy without introducing or changing any physical mask. -/
theorem tendsto_prefix_sub_candidate_transition {u y : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ |y|) :
    Tendsto (fun N : ℕ => ZetaRieszPairPrefixPayment.prefixPairDefect u y N -
      (evaluation (ordinaryArray u y) u N (cutoff1 N) + transition (ordinaryArray u y) u N))
        atTop (𝓝 0) := by
  have hb := ZetaRieszPairWholeCompletion.wholeCompletionBudget_tendsto.add
    (ZetaRieszPairJointQuadratic.squareBudget_tendsto (by linarith only [hu]) hU)
  simp only [add_zero] at hb
  exact squeeze_zero_norm' ((eventually_ge_atTop 65536).mono fun N hN =>
    norm_prefix_candidate_ledger_le hu hU hy hN) hb

end RiemannGaussian.ZetaRieszCutoffTransitionAudit

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWidePhasePayment
import RiemannGaussian.ZetaRieszJoinedPhysical

/-!
# Audit the sufficient floor and ceiling against the exact source

The source, carrier, radius and every arithmetic mask are unchanged.
The source-side scalar bounds allow floor -399/5000 and ceiling 42/25,
rather than -79/1000 and 3/2. The independent arithmetic estimates remain
OPEN. A budget 987/(100000*(N+1)) suffices for the current signed remainder;
this is 5.28 percent looser than 3/(320*(N+1)), not a bound proved here.

The parametric endpoints expose the exact admissible thresholds. Equality
with the source is insufficient when only vanishing two-sided errors are
available: the strict gap is an explicit hypothesis, not silently dropped.
-/

set_option autoImplicit false
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszEndgameSlack
open ZetaRieszMaskSupport ZetaRieszWideOwnerAudit
open ZetaRieszPrimeCountFrequency ZetaRieszGammaJoint

/-- A source-side upper bound with enough precision for the weaker floor.
This is NOT an independent arithmetic lower bound for joinedPhysical. -/
theorem retainedCost_upper {u : ℝ} (hu : 1/2 ≤ u) (hU : u ≤ radiusCeiling) :
    retainedCost u < 4601/5000 := by
  have hu0 : 0 < u := by linarith
  have huU : u ≤ 10001/20000 := hU
  have hh := log_le_sub_one_of_pos (show 0 < 2*u by positivity)
  rw [log_mul (by norm_num) hu0.ne'] at hh
  have hlog2 : (69314718/100000000 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*u by positivity)
  have hml := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ 2*u by positivity)
  have hq := mul_nonneg (show 0 ≤ u-1/2 by linarith)
    (show 0 ≤ 10001/20000-u by linarith)
  have hD : (6931/10000 : ℝ) ≤ -2*u*log u := by nlinarith
  have hDp : 0 < -2*u*log u := by linarith
  have hhi : log (32/13 : ℝ) < 90079/100000 := by
    apply (log_lt_iff_lt_exp (by norm_num)).mpr
    have he := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 90079/100000) 10
    norm_num [Finset.sum_range_succ] at he
    linarith
  have hlo : (9487/25000 : ℝ) < log (19/13) := by
    have hh := sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 3/16)
      (by norm_num : (3/16 : ℝ) < 1) 3
    norm_num [Finset.sum_range_succ] at hh
    linarith
  have hmul := mul_le_mul_of_nonneg_right hD
    (show 0 ≤ 4601/5000+log (19/13 : ℝ) by linarith)
  unfold retainedCost
  apply sub_lt_iff_lt_add.mpr
  apply (div_lt_iff₀ hDp).mpr
  nlinarith

/-- The same source-side scalar has a lower bound sufficient for ceiling
42/25. Actual analytic multiplicity is retained in the endpoints below. -/
theorem retainedCost_lower {u : ℝ} (hu : 1/2 ≤ u) (hU : u ≤ radiusCeiling) :
    23/25 < retainedCost u := by
  have hu0 : 0 < u := by linarith
  have hu1 : u < 1 := lt_of_le_of_lt hU (by norm_num [radiusCeiling])
  have hDp : 0 < -2*u*log u := by
    have hh := log_neg hu0 hu1
    nlinarith
  have hh := one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2*u by positivity)
  rw [log_mul (by norm_num) hu0.ne'] at hh
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*u by positivity)
  have hinv : 2*u*(1-(2*u)⁻¹)=2*u-1 := by field_simp
  rw [hinv] at hm
  have hl : log 2 < (13863/20000 : ℝ) := by linarith [log_two_lt_d9]
  have hsmall : log 2 < 1 := by linarith
  have hprod := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ 2*u-1 by linarith) (show log 2-1 ≤ 0 by linarith)
  have hD : -2*u*log u ≤ log 2 := by nlinarith only [hm,hprod]
  have hlo : (45039/50000 : ℝ) < log (32/13) := by
    have hh := sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 19/45)
      (by norm_num : (19/45 : ℝ) < 1) 6
    norm_num [Finset.sum_range_succ] at hh
    linarith
  have hhi : log (19/13 : ℝ) < 759/2000 := by
    apply (log_lt_iff_lt_exp (by norm_num)).mpr
    have he := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 759/2000) 8
    norm_num [Finset.sum_range_succ] at he
    linarith
  have hmul := mul_le_mul_of_nonneg_right hD
    (show 0 ≤ 23/25+759/2000 by norm_num)
  unfold retainedCost
  apply lt_sub_iff_add_lt.mpr
  have hquot : (23/25+759/2000 : ℝ) < log (32/13)/(-2*u*log u) := by
    apply (lt_div_iff₀ hDp).mpr
    nlinarith only [hmul,hl,hlo]
  linarith

/-- At every higher integer multiplicity the smallest source is the
double-zero source. This is exact algebra, not an arithmetic estimate. -/
theorem multiple_source_ge_double {c : ℝ} (hc : 1/2 ≤ c) {m : ℕ} (hm : 2 ≤ m) :
    -2+4*c ≤ -(m : ℝ)+(m : ℝ)^2*c := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hinner : 0 ≤ c*((m : ℝ)+2)-1 := by nlinarith
  have hp := mul_nonneg (show 0 ≤ (m : ℝ)-2 by linarith) hinner
  nlinarith only [hp]

/-- Exact admissible floor threshold: ANY allowance strictly below
1-retainedCost(u) suffices on a cofinal subsequence for a simple exposed
zero. The arithmetic premise is explicitly open and is not weakened to
equality at the source. -/
theorem false_of_cofinal_floor_allowance (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho = 1)
    (a : ℝ) (ha : a < 1-retainedCost (3/2-rho.1.re))
    (err : ℕ → ℝ) (he : Tendsto err atTop (𝓝 0))
    (hfloor : ∃ᶠ j in atTop, -a-err j ≤
      (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
        joinedPhysical (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)).re) : False := by
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (ZetaRieszJoinedPhysical.tendsto_joinedPhysical_exact_source rho hrho hexposed hU)
  simp only [hsimple,Nat.cast_one,one_pow,one_mul,Complex.add_re,
    Complex.neg_re,Complex.one_re,Complex.ofReal_re] at hs
  have hc : -a ≤ (-1+retainedCost (3/2-rho.1.re))+0 :=
    ge_of_tendsto_of_frequently (hs.add he)
      (hfloor.mono fun j hj => by dsimp only [Function.comp_def]; linarith)
  linarith

/-- Exact sufficient ceiling threshold: any number strictly below the
double-zero source excludes EVERY multiplicity>=2. The cofinal arithmetic
ceiling itself is not proved by the source theorem. -/
theorem false_of_cofinal_ceiling_allowance (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ radiusCeiling)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho)
    (b : ℝ) (hb : b < -2+4*retainedCost (3/2-rho.1.re))
    (err : ℕ → ℝ) (he : Tendsto err atTop (𝓝 0))
    (hceiling : ∃ᶠ j in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
        joinedPhysical (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)).re ≤ b+err j) : False := by
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (ZetaRieszJoinedPhysical.tendsto_joinedPhysical_exact_source rho hrho hexposed hU)
  have hreal : (-(analyticZetaZeroMultiplicity rho : ℂ)+
      (analyticZetaZeroMultiplicity rho : ℂ)^2*(retainedCost (3/2-rho.1.re) : ℂ)).re =
      -(analyticZetaZeroMultiplicity rho : ℝ)+
        (analyticZetaZeroMultiplicity rho : ℝ)^2*retainedCost (3/2-rho.1.re) := by norm_cast
  rw [hreal] at hs
  have hc : -(analyticZetaZeroMultiplicity rho : ℝ)+
      (analyticZetaZeroMultiplicity rho : ℝ)^2*retainedCost (3/2-rho.1.re)-0 ≤ b :=
    le_of_tendsto_of_frequently (hs.sub he)
      (hceiling.mono fun j hj => by dsimp only [Function.comp_def]; linarith)
  have hu : 1/2 ≤ 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hcost := ZetaRieszJointFloor.retainedCost_gt_nine_tenths hu hU
  have hmin := multiple_source_ge_double (show 1/2 ≤ retainedCost (3/2-rho.1.re) by linarith) hm
  linarith

/-- The weaker fixed floor -0.0798 suffices throughout the unchanged
restricted radius interval. This is a conditional endpoint only. -/
theorem false_of_relaxed_floor (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho = 1)
    (err : ℕ → ℝ) (he : Tendsto err atTop (𝓝 0))
    (hfloor : ∃ᶠ j in atTop, -(399/5000 : ℝ)-err j ≤
      (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
        joinedPhysical (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)).re) : False := by
  have hu : 1/2 ≤ 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  exact false_of_cofinal_floor_allowance rho hrho hexposed hU hsimple (399/5000)
    (by linarith only [retainedCost_upper hu hU]) err he hfloor

/-- The weaker ceiling1.68 suffices for ALL multiple exposed sources,
with no simplicity assumption and the exact original carrier retained. -/
theorem false_of_relaxed_ceiling (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ radiusCeiling)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho)
    (err : ℕ → ℝ) (he : Tendsto err atTop (𝓝 0))
    (hceiling : ∃ᶠ j in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
        joinedPhysical (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)).re ≤ 42/25+err j) : False := by
  have hu : 1/2 ≤ 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  exact false_of_cofinal_ceiling_allowance rho hrho hexposed hU hm (42/25)
    (by linarith only [retainedCost_lower hu hU]) err he hceiling

/-- A 5.28 percent larger SIGNED energy budget is enough for the relaxed
floor. This inequality does not prove that arithmetic budget. -/
theorem cost_le_of_relaxed_energy {N : ℕ} {E P : ℝ} (hP0 : 0 ≤ P)
    (hP : P ≤ (129/200 : ℝ)*N)
    (hE : E ≤ 987/(100000*((N : ℝ)+1))) :
    sqrt (max E 0*P) ≤ 399/5000 := by
  have hB : 0 ≤ 987/(100000*((N : ℝ)+1)) := by positivity
  have hM : max E 0 ≤ 987/(100000*((N : ℝ)+1)) := max_le hE hB
  have hp := mul_le_mul hM hP hP0 hB
  have hbudget : (987/(100000*((N : ℝ)+1)))*((129/200 : ℝ)*N) ≤ (399/5000 : ℝ)^2 := by
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0 < 100000*((N : ℝ)+1))]
    nlinarith only [Nat.cast_nonneg (α := ℝ) N]
  apply (sq_le_sq₀ (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 399/5000)).mp
  rw [sq_sqrt (mul_nonneg (le_max_right _ _) hP0)]
  exact hp.trans hbudget

/-- If the NEW remaining signed energy meets the relaxed numerical
budget, the already checked whole-floor comparison gives the weaker
sufficient floor. The only new arithmetic premise is stated literally. -/
theorem eventually_relaxed_floor_of_energy {u y : ℝ} (hu : 0 < u)
    (hU : u ≤ radiusCeiling) (hy : 54 ≤ y)
    (henergy : ∀ᶠ j : ℕ in atTop,
      let N := dyadicMomentOrder j
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := ZetaRieszParityPacket.coreBand u N (ZetaRieszNearCriticalCountPayment.countCeiling j)
      let X := max 1 (S.sup id)
      let f := ZetaRieszCutoffPeriodFloor.correctedProfile X L 1 0
      let w := fun n => u^(N+1)*ZetaRieszJointPrimeEnergy.primeWeight A L y N n 1;
      ZetaRieszWidePhasePayment.wideRemainingEnergy X N (S.filter Squarefree) w f y ≤
        987/(100000*((N : ℝ)+1))) :
    ∀ᶠ j : ℕ in atTop, -(399/5000 : ℝ)-ZetaRieszWidePhasePayment.joinedError u y j ≤
      (((u : ℂ)^(dyadicMomentOrder j+1))*
        joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [ZetaRieszWidePhasePayment.eventually_joined_floor hu hU hy,henergy]
    with j hj he
  dsimp only at hj he ⊢
  have hc := cost_le_of_relaxed_energy (by positivity : 0 ≤ (129/200 : ℝ)*dyadicMomentOrder j)
    (le_refl ((129/200 : ℝ)*dyadicMomentOrder j)) he
  linarith only [hj,hc]

end RiemannGaussian.ZetaRieszEndgameSlack

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCoupledArithmeticBound

/-!
# An arithmetic square-budget estimate for the joined energy minus credit

The common-radius ordinary-prime coefficients have one finite square budget,
independent of the factorial order. Apply it to the already joined symmetric
coefficient, whose maximum is at most `4/N`. The entire correlation credit
remains subtracted. This is an estimate for the original `D-Q`, not a new
carrier or a replacement of its native masks. The geometric rate may still
be at least one outside the independently proved analytic coverage.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real Filter Topology Metric Set
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCoupledSquareEnergy
open ZetaRieszCoupledSignedBound ZetaRieszCoupledArithmeticBound
open ZetaRieszPairPrimePowerPayment

private theorem native_divisor_bound {N : ℕ} (hN : 0 < N) :
    1/((13*N/32+1 : ℕ) : ℝ) ≤ (5/2 : ℝ)/(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_div_iff₀ (by positivity) hn).mpr
  have hi : 2*N ≤ 5*(13*N/32+1) := by omega
  have hr : 2*(N : ℝ) ≤ 5*((13*N/32+1 : ℕ) : ℝ) := by exact_mod_cast hi
  linarith only [hr]

private theorem positiveWeight_native_bounds {N i : ℕ} (hN : 0 < N) :
    0 ≤ positiveWeight N (13*N/32) i ∧
      positiveWeight N (13*N/32) i ≤ 4/(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold positiveWeight
  constructor
  · positivity
  · split_ifs with hi
    · have hd : 1/((N-i : ℕ) : ℝ) ≤ 1/((13*N/32+1 : ℕ) : ℝ) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast (show 13*N/32+1 ≤ N-i by omega)
      have he := hd.trans (native_divisor_bound hN)
      calc
        _ ≤ 1/(N : ℝ)+(5/2 : ℝ)/(N : ℝ) := add_le_add le_rfl he
        _ ≤ _ := by field_simp; norm_num
    · simp only [add_zero]
      exact div_le_div_of_nonneg_right (by norm_num) hn.le

private theorem successorWeight_native_bounds {N i : ℕ} (hN : 0 < N) :
    0 ≤ successorWeight N (13*N/32) i ∧
      successorWeight N (13*N/32) i ≤ (5/2 : ℝ)/(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold successorWeight
  split_ifs with hi
  · refine ⟨by positivity,?_⟩
    apply (one_div_le_one_div_of_le (by positivity) ?_).trans (native_divisor_bound hN)
    exact_mod_cast (show 13*N/32+1 ≤ N+1-i by omega)
  · exact ⟨le_rfl,by positivity⟩

private theorem joinedWeight_native_abs_le {N i : ℕ} (hN : 0 < N)
    {b : ℝ} (hb : 0 ≤ b) (hbu : b ≤ 3/2) :
    |joinedWeight N (13*N/32) b i| ≤ 4/(N : ℝ) := by
  have hp := positiveWeight_native_bounds (i:=i) hN
  have hv := successorWeight_native_bounds (i:=i) hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hmul : b*successorWeight N (13*N/32) i ≤ 4/(N : ℝ) := by
    apply (mul_le_mul hbu hv.2 hv.1 (by norm_num)).trans
    calc
      (3/2 : ℝ)*((5/2 : ℝ)/(N : ℝ)) = (15/4 : ℝ)/(N : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) hn.le
  unfold joinedWeight
  exact abs_le.mpr ⟨by nlinarith only [hp.1,hmul],
    by nlinarith only [hp.2,mul_nonneg hb hv.1]⟩

/-- A maximum-row bound for every positive order. It is applied AFTER
the native adjacent degrees and swapped incidences have been joined. -/
theorem symmetricWeight_native_abs_le {N i : ℕ} (hN : 0 < N)
    {b : ℝ} (hb : 0 ≤ b) (hbu : b ≤ 3/2) :
    |symmetricWeight N (13*N/32) b i| ≤ 4/(N : ℝ) := by
  unfold symmetricWeight
  rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h1 := joinedWeight_native_abs_le (i:=i) hN hb hbu
  have h2 := joinedWeight_native_abs_le (i:=N-1-i) hN hb hbu
  have h := abs_add_le (joinedWeight N (13*N/32) b i)
    (joinedWeight N (13*N/32) b (N-1-i))
  linarith only [h,h1,h2]

/-- The diagonal price uses one finite square budget, rather than an
orderwise supremum paid once for every factorial coordinate. -/
theorem diagonalEnergy_native_le_square_sum (a : ℕ → ℂ) {N : ℕ}
    (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b) (hbu : b ≤ 3/2) :
    diagonalEnergy a N (13*N/32) b ≤
      4/(N : ℝ)*∑ i∈Finset.range N, ‖a i‖^2 := by
  unfold diagonalEnergy
  calc
    _ ≤ ∑ i∈Finset.range N, (4/(N : ℝ))/2*
        (‖a i‖^2+‖a (N-1-i)‖^2) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_right (symmetricWeight_native_abs_le hN hb hbu)
        (by norm_num)
    _ = _ := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,
        Finset.sum_range_reflect (fun i => ‖a i‖^2) N]
      ring

/-- A signed common-radius estimate with its ENTIRE correlation credit
retained. No separate norm of `D` and `Q` occurs on the left. -/
theorem energy_sub_credit_le_square_budget (a : ℕ → ℂ) {q B : ℝ}
    (hq : 0 < q) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b)
    (hbu : b ≤ 3/2)
    (ha : (∑ i∈Finset.range N, ‖radiusArray a q i‖^2) ≤ B) :
    diagonalEnergy a N (13*N/32) b-correlationCredit a N (13*N/32) b ≤
      q^(N-1)*(4*B/(N : ℝ)-
        correlationCredit (radiusArray a q) N (13*N/32) b) := by
  rw [energy_sub_credit_rescale a hq]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq.le _)
  apply sub_le_sub_right
  calc
    _ ≤ 4/(N : ℝ)*∑ i∈Finset.range N, ‖radiusArray a q i‖^2 :=
      diagonalEnergy_native_le_square_sum _ hN hb hbu
    _ ≤ 4/(N : ℝ)*B := mul_le_mul_of_nonneg_left ha (by positivity)
    _ = _ := by ring

/-- A two-sided estimate for the same joined signed incidence, with
the common total order and one square budget. -/
theorem abs_energy_sub_credit_le_square_budget (a : ℕ → ℂ) {q B : ℝ}
    (hq : 0 < q) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b)
    (hbu : b ≤ 3/2)
    (ha : (∑ i∈Finset.range N, ‖radiusArray a q i‖^2) ≤ B) :
    |diagonalEnergy a N (13*N/32) b-correlationCredit a N (13*N/32) b| ≤
      4*B/(N : ℝ)*q^(N-1) := by
  rw [energy_sub_credit_rescale a hq,abs_mul,
    abs_of_nonneg (pow_nonneg hq.le _)]
  have hh : |diagonalEnergy (radiusArray a q) N (13*N/32) b-
      correlationCredit (radiusArray a q) N (13*N/32) b| ≤
        diagonalEnergy (radiusArray a q) N (13*N/32) b := by
    rw [←joined_real_eq_energy_sub_credit]
    apply (Complex.abs_re_le_norm _).trans
    apply (norm_sum_le _ _).trans
    unfold diagonalEnergy
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hs := sq_nonneg (‖radiusArray a q i‖-‖radiusArray a q (N-1-i)‖)
    nlinarith only [hs,abs_nonneg (symmetricWeight N (13*N/32) b i)]
  have hd := diagonalEnergy_native_le_square_sum (radiusArray a q) hN hb hbu
  have hm := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 4/(N : ℝ))
  apply (mul_le_mul_of_nonneg_left (hh.trans (hd.trans hm))
    (pow_nonneg hq.le _)).trans_eq
  ring

/-- The square budget of the actual complete ordinary-prime moments.
This is not a bound extrapolated from finitely many prime samples. -/
def ordinarySquareBudget (y R : ℝ) : ℝ :=
  ∑' i : ℕ, ‖zetaOrdinaryPrimeLogMoment i (3/2+Complex.I*y)‖^2*R^(2*i)

private theorem summable_squares_of_radius {R r C y : ℝ} (hR : 0 ≤ R)
    (hr : 0 < r) (hRr : R < r)
    (hm : ∀ i, ‖zetaOrdinaryPrimeLogMoment i (3/2+Complex.I*y)‖ ≤ C/r^i) :
    Summable (fun i : ℕ =>
      ‖zetaOrdinaryPrimeLogMoment i (3/2+Complex.I*y)‖^2*R^(2*i)) := by
  have hq : 0 ≤ (R/r)^2 := sq_nonneg _
  have hq1 : (R/r)^2 < 1 := by
    have hl := div_nonneg hR hr.le
    have hu := (div_lt_one hr).mpr hRr
    nlinarith only [hl,hu]
  apply Summable.of_nonneg_of_le (fun i => by positivity) _
    ((summable_geometric_of_lt_one hq hq1).mul_left (C^2))
  intro i
  have hci : 0 ≤ C/r^i := (norm_nonneg _).trans (hm i)
  have hi := pow_le_pow_left₀ (norm_nonneg _) (hm i) 2
  apply (mul_le_mul_of_nonneg_right hi (pow_nonneg hR (2*i))).trans_eq
  rw [div_pow,pow_mul,div_pow,←pow_mul]
  ring

private theorem larger_analytic_radius {R y : ℝ} (hR : 1/2 ≤ R) (hRu : R < 3/4)
    (ha : AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
      (closedBall (3/2+Complex.I*y) R)) :
    ∃ r : ℝ, R < r ∧ r < 3/4 ∧
      AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
        (closedBall (3/2+Complex.I*y) r) := by
  let f := fun s : ℂ => -logDeriv riemannZeta s
  let c : ℂ := 3/2+Complex.I*y
  obtain ⟨δ,hδ,hthick⟩ := (isCompact_closedBall c R).exists_cthickening_subset_open
    (isOpen_analyticAt ℂ f) ha
  let e := min (δ/2) ((3/4-R)/2)
  have he : 0 < e := lt_min (by positivity) (by linarith only [hRu])
  have hed : e ≤ δ/2 := min_le_left _ _
  have heu : e ≤ (3/4-R)/2 := min_le_right _ _
  refine ⟨R+e,by linarith only [he],by linarith only [heu,hRu],?_⟩
  intro s hs
  apply hthick
  rw [cthickening_closedBall hδ.le (by linarith only [hR] : 0 ≤ R)]
  exact (closedBall_subset_closedBall (by linarith only [hed,hδ])) hs

/-- Analyticity on a closed disk independently proves a finite square
budget at that SAME radius. No radius shrink or zero/source assumption
is hidden in the estimate. -/
theorem ordinarySquareBudget_summable_of_analytic_radius {R y : ℝ}
    (hR : 1/2 ≤ R) (hRu : R < 3/4)
    (ha : AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
      (closedBall (3/2+Complex.I*y) R)) :
    Summable (fun i : ℕ =>
      ‖zetaOrdinaryPrimeLogMoment i (3/2+Complex.I*y)‖^2*R^(2*i)) := by
  obtain ⟨r,hRr,hru,har⟩ := larger_analytic_radius hR hRu ha
  obtain ⟨C,_,hm⟩ := ZetaRieszJoinedPhaseRadius.ordinary_moment_bound_of_analytic_radius
    (by linarith only [hR,hRr]) hru har
  exact summable_squares_of_radius (by linarith only [hR])
    (by linarith only [hR,hRr]) hRr hm

theorem ordinarySquareBudget_nonneg (y R : ℝ) : 0 ≤ ordinarySquareBudget y R := by
  unfold ordinarySquareBudget
  apply tsum_nonneg
  intro i
  apply mul_nonneg (sq_nonneg _)
  rw [show 2*i=i*2 by omega,pow_mul]
  exact sq_nonneg _

/-- A quantitative certificate for the complete square budget using any
larger actual Cauchy disk. Its constant and strict radius margin remain
explicit inputs, rather than extrapolations of a finite prime control. -/
theorem ordinarySquareBudget_le_of_larger_radius {R r C y : ℝ}
    (hR : 0 ≤ R) (hr : 0 < r) (hRr : R < r)
    (hm : ∀ i, ‖zetaOrdinaryPrimeLogMoment i (3/2+Complex.I*y)‖ ≤ C/r^i) :
    ordinarySquareBudget y R ≤ C^2/(1-(R/r)^2) := by
  have hq : 0 ≤ (R/r)^2 := sq_nonneg _
  have hq1 : (R/r)^2 < 1 := by
    have hl := div_nonneg hR hr.le
    have hu := (div_lt_one hr).mpr hRr
    nlinarith only [hl,hu]
  have hs := summable_squares_of_radius hR hr hRr hm
  have hg := (summable_geometric_of_lt_one hq hq1).mul_left (C^2)
  unfold ordinarySquareBudget
  calc
    _ ≤ ∑' i : ℕ, C^2*((R/r)^2)^i := by
      apply hs.tsum_le_tsum _ hg
      intro i
      have hi := pow_le_pow_left₀ (norm_nonneg _) (hm i) 2
      apply (mul_le_mul_of_nonneg_right hi (pow_nonneg hR (2*i))).trans_eq
      rw [div_pow,pow_mul,div_pow,←pow_mul]
      ring
    _ = _ := by
      rw [tsum_mul_left,tsum_geometric_of_lt_one hq hq1]
      rfl

private theorem radiusArray_ordinary_norm_sq {u R y : ℝ} (hu : 0 < u) (hR : 0 < R)
    (i : ℕ) :
    ‖radiusArray (ordinaryArray u y) (u/R) i‖^2=
      u^2*(‖zetaOrdinaryPrimeLogMoment i (3/2+Complex.I*y)‖^2*R^(2*i)) := by
  have he : u^(i+1)/(u/R)^i=u*R^i := by
    rw [div_pow,pow_succ,div_div_eq_mul_div]
    have hne : u^i ≠ 0 := pow_ne_zero _ (ne_of_gt hu)
    field_simp
  unfold radiusArray ordinaryArray
  rw [norm_div,norm_mul,norm_pow,norm_pow,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg hu.le,Real.norm_of_nonneg (div_pos hu hR).le,
    mul_div_right_comm,he]
  rw [pow_mul]
  ring

/-- Every finite-order budget is bounded by the independently proved
complete arithmetic square sum. All low factorial orders are included. -/
theorem ordinary_radius_square_sum_le {u R y : ℝ} (hu : 0 < u) (hR : 0 < R)
    (hs : Summable (fun i : ℕ =>
      ‖zetaOrdinaryPrimeLogMoment i (3/2+Complex.I*y)‖^2*R^(2*i))) (N : ℕ) :
    (∑ i∈Finset.range N, ‖radiusArray (ordinaryArray u y) (u/R) i‖^2) ≤
      u^2*ordinarySquareBudget y R := by
  simp_rw [radiusArray_ordinary_norm_sq hu hR]
  rw [←Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg u)
  exact hs.sum_le_tsum _ (fun i _ => by positivity)

/-- The additional independent arithmetic estimate for `D-Q`: a single
`1/N` square-budget price and the ACTUAL negative correlation credit.
The geometric ratio is not assumed to be less than one. -/
theorem ordinary_energy_sub_credit_le_square_budget {u R y : ℝ}
    (hu : 1/2 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hR : 1/2 ≤ R) (hRu : R < 3/4)
    (ha : AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
      (closedBall (3/2+Complex.I*y) R)) {N : ℕ} (hN : 65536 ≤ N) :
    diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
      correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N) ≤
        (u/R)^(N-1)*(4*u^2*ordinarySquareBudget y R/(N : ℝ)-
          correlationCredit (radiusArray (ordinaryArray u y) (u/R)) N
            (13*N/32) (lengthFactor u N)) := by
  have hu0 : 0 < u := by linarith only [hu]
  have hr0 : 0 < R := by linarith only [hR]
  have hb := lengthFactor_bounds hu hU hN
  have hs := ordinarySquareBudget_summable_of_analytic_radius hR hRu ha
  convert energy_sub_credit_le_square_budget (ordinaryArray u y) (div_pos hu0 hr0)
    (by omega : 0 < N) (by linarith only [hb.1] : 0 ≤ lengthFactor u N) hb.2
    (ordinary_radius_square_sum_le hu0 hr0 hs N) using 1
  ring

/-- Two-sided control of the original signed quantity. This is stronger
than pricing `D` and `Q` separately, and uses no exposed-zero hypothesis. -/
theorem abs_ordinary_energy_sub_credit_le_square_budget {u R y : ℝ}
    (hu : 1/2 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hR : 1/2 ≤ R) (hRu : R < 3/4)
    (ha : AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
      (closedBall (3/2+Complex.I*y) R)) {N : ℕ} (hN : 65536 ≤ N) :
    |diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
      correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N)| ≤
        4*u^2*ordinarySquareBudget y R/(N : ℝ)*(u/R)^(N-1) := by
  have hu0 : 0 < u := by linarith only [hu]
  have hr0 : 0 < R := by linarith only [hR]
  have hb := lengthFactor_bounds hu hU hN
  have hs := ordinarySquareBudget_summable_of_analytic_radius hR hRu ha
  convert abs_energy_sub_credit_le_square_budget (ordinaryArray u y) (div_pos hu0 hr0)
    (by omega : 0 < N) (by linarith only [hb.1] : 0 ≤ lengthFactor u N) hb.2
    (ordinary_radius_square_sum_le hu0 hr0 hs N) using 1
  ring

/-- Keep whichever of the two proved DIAGONAL prices is smaller, after
the full signed incidence has already been joined. The negative credit
is common to both bounds and is spent exactly once. -/
theorem ordinary_energy_sub_credit_le_minimum_budget {u R C y : ℝ}
    (hu : 1/2 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hR : 1/2 ≤ R) (hRu : R < 3/4)
    (ha : AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
      (closedBall (3/2+Complex.I*y) R))
    (hm : ∀ i, ‖zetaOrdinaryPrimeLogMoment i (3/2+Complex.I*y)‖ ≤ C/R^i)
    {N : ℕ} (hN : 65536 ≤ N) :
    diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
      correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N) ≤
        (u/R)^(N-1)*
          (min ((C*u)^2*weightVariation N (13*N/32) (lengthFactor u N))
            (4*u^2*ordinarySquareBudget y R/(N : ℝ))-
            correlationCredit (radiusArray (ordinaryArray u y) (u/R)) N
              (13*N/32) (lengthFactor u N)) := by
  have hu0 : 0 < u := by linarith only [hu]
  have hr0 : 0 < R := by linarith only [hR]
  have hb := lengthFactor_bounds hu hU hN
  have hs := ordinarySquareBudget_summable_of_analytic_radius hR hRu ha
  have hc i : ‖radiusArray (ordinaryArray u y) (u/R) i‖ ≤ C*u := by
    unfold radiusArray ordinaryArray
    rw [norm_div,norm_mul,norm_pow,norm_pow,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg hu0.le,Real.norm_of_nonneg (div_pos hu0 hr0).le]
    apply (div_le_iff₀ (pow_pos (div_pos hu0 hr0) i)).mpr
    apply (mul_le_mul_of_nonneg_left (hm i) (pow_nonneg hu0.le (i+1))).trans_eq
    rw [div_pow,pow_succ]
    ring
  rw [energy_sub_credit_rescale _ (div_pos hu0 hr0)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (div_pos hu0 hr0).le _)
  apply sub_le_sub_right
  apply le_min
  · exact diagonalEnergy_le_variation _ _ (fun i _ => hc i)
  · have hd := diagonalEnergy_native_le_square_sum
      (radiusArray (ordinaryArray u y) (u/R)) (by omega : 0 < N)
      (by linarith only [hb.1] : 0 ≤ lengthFactor u N) hb.2
    have he := mul_le_mul_of_nonneg_left (ordinary_radius_square_sum_le hu0 hr0 hs N)
      (by positivity : 0 ≤ 4/(N : ℝ))
    exact (hd.trans he).trans_eq (by ring)

/-- Every fixed admissible height has an independently proved radius and
ONE square budget for all orders and all radii in the requested strip.
There is no claim that this full analytic radius exceeds `u`. -/
theorem exists_independent_square_budget {y : ℝ} (hy : 54 ≤ |y|) :
    ∃ R B : ℝ, 1/2 < R ∧ R < 3/4 ∧ 0 ≤ B ∧
      ∀ u : ℝ, 1/2 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
        ∀ N : ℕ, 65536 ≤ N →
          diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
            correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N) ≤
              (u/R)^(N-1)*(4*u^2*B/(N : ℝ)-
                correlationCredit (radiusArray (ordinaryArray u y) (u/R)) N
                  (13*N/32) (lengthFactor u N)) := by
  obtain ⟨R,hR,hRu,ha⟩ := ZetaRieszJoinedPhaseRadius.exists_analytic_radius hy
  exact ⟨R,ordinarySquareBudget y R,hR,hRu,ordinarySquareBudget_nonneg y R,
    fun _ hu hU _ hN => ordinary_energy_sub_credit_le_square_budget hu hU hR.le hRu ha hN⟩

/-- A concrete `1/N` arithmetic refinement at the SAME explicit radius
as the preceding geometric bound. This transfers EXISTING analytic
coverage; it does not assert a new zero-free region. -/
theorem exists_concrete_square_budget_bound {y : ℝ} (hy : 54 ≤ |y|)
    (hlog : log (|y|+3) ≤ 1800) :
    ∃ B : ℝ, 0 < B ∧ ∀ u : ℝ, 1/2 ≤ u →
      u ≤ ZetaRieszWideOwnerAudit.radiusCeiling → ∀ N : ℕ, 65536 ≤ N →
        |diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
          correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N)| ≤
            B/(N : ℝ)*(100010/100011 : ℝ)^(N-1) := by
  let B := 4*ZetaRieszWideOwnerAudit.radiusCeiling^2*
    ordinarySquareBudget y (100011/200000)
  have hB : 0 ≤ B := by dsimp [B]; positivity [ordinarySquareBudget_nonneg y (100011/200000)]
  refine ⟨B+1,by linarith only [hB],fun u hu hU N hN => ?_⟩
  have hu0 : 0 ≤ u := by linarith only [hu]
  have hs := ordinarySquareBudget_nonneg y (100011/200000)
  have hh := pow_le_pow_left₀ hu0 hU 2
  have hc : 4*u^2*ordinarySquareBudget y (100011/200000) ≤ B+1 := by
    have he := mul_le_mul_of_nonneg_right hh
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hs)
    dsimp only [B]
    nlinarith only [he]
  have hq : u/(100011/200000 : ℝ) ≤ (100010/100011 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 100011/200000)).mpr
    have huq : u ≤ (10001/20000 : ℝ) := hU
    linarith only [huq]
  have hr := pow_le_pow_left₀
    (div_nonneg hu0 (by norm_num : (0 : ℝ) ≤ 100011/200000)) hq (N-1)
  have hb := abs_ordinary_energy_sub_credit_le_square_budget hu hU
    (by norm_num : (1/2 : ℝ) ≤ 100011/200000)
    (by norm_num : (100011/200000 : ℝ) < 3/4)
    (ZetaRieszJoinedPhaseRadius.analytic_concrete_radius_of_log_height hy hlog) hN
  exact hb.trans (mul_le_mul (div_le_div_of_nonneg_right hc (by positivity)) hr
    (by positivity) (by positivity))

/-- At the concrete covered heights, even `N*abs(D-Q)` has geometric
decay. This is a quantitative refinement, not new uncovered floor credit. -/
theorem tendsto_order_mul_abs_energy_sub_credit_of_log_height {u y : ℝ}
    (hy : 54 ≤ |y|) (hlog : log (|y|+3) ≤ 1800)
    (hu : 1/2 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N : ℕ => (N : ℝ)*
      |diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
        correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N)|)
      atTop (𝓝 0) := by
  obtain ⟨B,_,hb⟩ := exists_concrete_square_budget_bound hy hlog
  have ht : Tendsto (fun N : ℕ => B*(100010/100011 : ℝ)^(N-1)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 100010/100011)
        (by norm_num : (100010/100011 : ℝ) < 1)).comp
          (tendsto_sub_atTop_nat 1)).const_mul B
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity)) _ ht
  filter_upwards [eventually_ge_atTop (65536 : ℕ)] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hh := mul_le_mul_of_nonneg_left (hb u hu hU N hN) (Nat.cast_nonneg N)
  have he : (N : ℝ)*(B/(N : ℝ)*(100010/100011 : ℝ)^(N-1))=
      B*(100010/100011 : ℝ)^(N-1) := by field_simp
  exact hh.trans_eq he

/-- A nonzero selected source cannot have a finite square budget at its
own radius. This blocks the false substitution of a competing-mode disk
for the complete ordinary-prime arithmetic radius. -/
theorem not_summable_squares_at_nonzero_source {u y : ℝ} (hu : 0 < u)
    {a : ℂ} (ha : a ≠ 0)
    (ht : Tendsto (ordinaryArray u y) atTop (𝓝 a)) :
    ¬Summable (fun i : ℕ =>
      ‖zetaOrdinaryPrimeLogMoment i (3/2+Complex.I*y)‖^2*u^(2*i)) := by
  intro hs
  have hz := hs.tendsto_atTop_zero.const_mul (u^2)
  have he (i : ℕ) : ‖ordinaryArray u y i‖^2=
      u^2*(‖zetaOrdinaryPrimeLogMoment i (3/2+Complex.I*y)‖^2*u^(2*i)) := by
    simpa only [div_self (ne_of_gt hu),radiusArray,Complex.ofReal_one,one_pow,
      div_one] using radiusArray_ordinary_norm_sq hu hu i
  have hzero : Tendsto (fun i => ‖ordinaryArray u y i‖^2) atTop (𝓝 0) := by
    simpa only [mul_zero] using hz.congr (fun i => (he i).symm)
  have hnorm := ht.norm.pow 2
  have h := tendsto_nhds_unique hnorm hzero
  have hp : 0 < ‖a‖ := norm_pos_iff.mpr ha
  nlinarith only [h,hp]

/-- The obstruction applies to every actual exposed zero with its true
analytic multiplicity. It is not restricted to simple zero models. -/
theorem not_summable_squares_at_exposed_zero (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau≠rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖) :
    ¬Summable (fun i : ℕ =>
      ‖zetaOrdinaryPrimeLogMoment i (3/2+Complex.I*(rho.1.im : ℂ))‖^2*
        (3/2-rho.1.re)^(2*i)) := by
  apply not_summable_squares_at_nonzero_source
    (by linarith only [NontrivialZetaZero.re_lt_one rho] : 0 < 3/2-rho.1.re)
    (a:=-(analyticZetaZeroMultiplicity rho : ℂ))
  · exact neg_ne_zero.mpr (by exact_mod_cast
      (Nat.ne_zero_of_lt (analyticZetaZeroMultiplicity_positive rho)))
  · exact ZetaRieszPrimeCompletionPhase.tendsto_ordinary_prime_source rho hrho hexposed

end RiemannGaussian.ZetaRieszCoupledSquareEnergy

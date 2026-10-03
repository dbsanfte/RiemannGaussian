/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGlobalBulkPayment

/-!
# Full unallocated owner phases

The raw high-owner boundary has no old owner allocation. Keep its full
factorial radial weight and actual product phase. This module proves the
signed complete-window lattice estimate up to owner log 7N/5. No prime
phase approximation or zero hypothesis is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology MeasureTheory
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszUnallocatedOwnerPhase
open ZetaRieszOwnerMaximal ZetaRieszSmoothOwnerDiscrepancy
open ZetaRieszOwnerLatticePhase ZetaRieszOwnerPhasePrimitive
open ZetaRieszCofactorDiscrepancy ZetaRieszCofactorPhaseEnergy

private theorem ownerWeight_one (N : ℕ) : ownerWeight N 1=1 := by
  unfold ownerWeight
  have hz : (∑ k∈ZetaRieszWingHighOrders.unpaidOrders N,
      ZetaRieszJointAllocation.mass (N+1) k 1)=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [unpaidOrders_eq] at hk
    have hkN : k<N+1 := by have := (Finset.mem_Icc.mp hk).2; omega
    simp [ZetaRieszJointAllocation.mass,show N+1-k≠0 by omega]
  rw [hz,sub_zero]

/-- Full factorial cofactor test, with no owner allocation. -/
def densityTest (N : ℕ) (c y x : ℝ) : ℝ :=
  ownerLogPhase N 0 y (c+log x)/x

private def densityTestDerivative (N : ℕ) (c y x : ℝ) : ℝ :=
  (ownerLogDerivative N 0 y (c+log x)-ownerLogPhase N 0 y (c+log x))/x^2

/-- The physical total-log weight, exactly. -/
theorem densityTest_eq {N : ℕ} {c x : ℝ} (ht : c+log x≠0) (y : ℝ) :
    densityTest N c y x=radial N (c+log x)*cos (y*(c+log x))/x := by
  simp only [densityTest,ownerLogPhase,sub_zero,div_self ht,ownerWeight_one,one_mul]

private theorem density_test_deriv {N : ℕ} (hN : 32≤N) {x : ℝ}
    (hx : 1<x) {c : ℝ} (hc : 0≤c) (y : ℝ) :
    HasDerivAt (densityTest N c y) (densityTestDerivative N c y x) x := by
  have hx0 : 0<x := by linarith
  have ht : c+log x≠0 := (by linarith [log_pos hx] : 0<c+log x).ne'
  have hg := (ownerLogPhase_deriv hN 0 y ht).comp x
    ((hasDerivAt_log hx0.ne').const_add c)
  apply (hg.div (hasDerivAt_id x) hx0.ne').congr_deriv
  dsimp [densityTestDerivative]
  field_simp

private theorem density_test_derivative_bound (N : ℕ) {x : ℝ}
    (hx : exp 1≤x) {c : ℝ} (hc : 0≤c) (y : ℝ) :
    |densityTestDerivative N c y x|≤
      (2*((N : ℝ)+1)+2+|y|)*radialCap N/x^2 := by
  have hx0 : 0<x := (exp_pos _).trans_le hx
  have hl : 1≤log x := by simpa only [log_exp] using log_le_log (exp_pos _) hx
  have hd := ownerLogDerivative_bound N (c:=0) (T:=c+log x) (by norm_num)
    (by linarith) (by linarith) y
  have hb := ownerLogPhase_bound N (c:=0) (T:=c+log x) (by norm_num)
    (by linarith) (by linarith) y
  unfold densityTestDerivative
  rw [abs_div,abs_of_nonneg (sq_nonneg x)]
  exact (div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add hd hb))
    (sq_nonneg x)).trans_eq (by ring)

private theorem density_lattice_error {N M X : ℕ} (hN : 32≤N)
    (hM : exp 1≤(M : ℝ)) (hMX : M≤X) {c : ℝ} (hc : 0≤c) (y : ℝ) :
    |(∑ n∈Finset.Ioc M X,densityTest N c y n)-
      (∫ x : ℝ in (M : ℝ)..X,densityTest N c y x)|≤
      (X-M : ℕ)*(2*((N : ℝ)+1)+2+|y|)*radialCap N/(M : ℝ)^2 := by
  have hm : 0<(M : ℝ) := (exp_pos _).trans_le hM
  have he : 1<exp (1 : ℝ) := one_lt_exp_iff.mpr (by norm_num)
  have hcap := radialCap_nonneg N
  let E := (2*((N : ℝ)+1)+2+|y|)*radialCap N/(M : ℝ)^2
  have hE : 0≤E := by dsimp [E]; positivity
  have hb x (hx : x∈Set.Icc (M : ℝ) X) : |densityTestDerivative N c y x|≤E := by
    apply (density_test_derivative_bound N (hM.trans hx.1) hc y).trans
    apply div_le_div_of_nonneg_left (by positivity) (by positivity : (0 : ℝ)<(M : ℝ)^2)
    nlinarith only [hx.1,hm]
  have h := integer_sampling_error hMX hE
    (fun x hx => density_test_deriv hN (he.trans_le (hM.trans hx.1)) hc y) hb
  exact h.trans_eq (by dsimp [E]; ring)

private theorem density_test_integral {N M X : ℕ} (hN : 32≤N)
    (hM : exp 1≤(M : ℝ)) (hMX : M≤X) {c : ℝ} (hc : 0≤c) (y : ℝ) :
    (∫ x : ℝ in (M : ℝ)..X,densityTest N c y x)=
      (∫ T : ℝ in (c+log M)..(c+log X),ownerPhase N 0 (phaseDamping y) T).re := by
  have hm : 1<(M : ℝ) := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ)<1)).trans_le hM
  have hab : (M : ℝ)≤X := by exact_mod_cast hMX
  have hcont : ContinuousOn (densityTest N c y) (Set.Icc (M : ℝ) X) := by
    intro x hx
    exact (density_test_deriv hN (hm.trans_le hx.1) hc y).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (densityTest N c y) volume (M : ℝ) X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hcont
  have hz : phaseDamping y≠0 := by
    intro he
    have := congrArg Complex.re he
    rw [phaseDamping_re] at this
    norm_num at this
  have hreal : (∫ T : ℝ in (c+log M)..(c+log X),ownerPhase N 0 (phaseDamping y) T).re=
      (ownerPrimitive N 0 (phaseDamping y) (c+log M)).re-
        (ownerPrimitive N 0 (phaseDamping y) (c+log X)).re := by
    rw [ownerPhase_integral N 0 hz,Complex.sub_re]
  have hf x (hx : x∈Set.uIcc (M : ℝ) X) :
      HasDerivAt (fun v : ℝ => (ownerPrimitive N 0 (phaseDamping y) (c+log v)).re)
        (-densityTest N c y x) x := by
    rw [Set.uIcc_of_le hab] at hx
    have hx1 := hm.trans_le hx.1
    have hx0 : 0<x := by linarith
    have ht : c+log x≠0 := (by linarith [log_pos hx1] : 0<c+log x).ne'
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
      ((ownerPrimitive_deriv N 0 hz (c+log x)).scomp x ((hasDerivAt_log hx0.ne').const_add c))
    apply h.congr_deriv
    simp only [Complex.reCLM_apply,Complex.real_smul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,zero_mul,sub_zero]
    rw [← ownerLogPhase_eq_re N 0 y ht]
    dsimp [densityTest]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hf hint.neg
  rw [intervalIntegral.integral_neg] at h
  rw [hreal]
  linarith only [h]

private theorem normalized_cap_fast {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    u^(N+1)*radialCap N*exp (-(2/5 : ℝ)*N)≤
      2*u*((N : ℝ)+1)*exp (-(N : ℝ)/4) := by
  have hb : 2*u≤exp (3/20 : ℝ) := by
    have he := add_one_le_exp (3/20 : ℝ)
    unfold ZetaRieszWideOwnerAudit.radiusCeiling at hU
    linarith only [hU,he]
  have hn := pow_le_pow_left₀ (mul_nonneg (by norm_num) hu) hb N
  rw [← exp_nat_mul] at hn
  have hg := mul_le_mul_of_nonneg_right hn (exp_pos (-(2/5 : ℝ)*N)).le
  rw [← exp_add] at hg
  have he : (N : ℝ)*(3/20)+-(2/5)*N=-(N : ℝ)/4 := by ring
  rw [he] at hg
  have h := mul_le_mul_of_nonneg_left hg
    (show 0≤2*u*((N : ℝ)+1) by positivity)
  calc
    _ = (2*u*((N : ℝ)+1))*((2*u)^N*exp (-(2/5 : ℝ)*N)) := by
      simp only [radialCap,pow_succ,mul_pow]
      ring
    _ ≤ _ := h

private theorem lattice_ratios {N M X : ℕ} (hM : 1≤M) (_hMX : M≤X)
    (hlarge : exp ((N : ℝ)/2)≤M) (hwide : (X : ℝ)≤M*exp ((N : ℝ)/10)) :
    1/(M : ℝ)≤exp (-(2/5 : ℝ)*N) ∧
      ((X-M : ℕ) : ℝ)/(M : ℝ)^2≤exp (-(2/5 : ℝ)*N) := by
  have hm : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hi : 1/(M : ℝ)≤exp (-(N : ℝ)/2) := by
    rw [show -(N : ℝ)/2=-((N : ℝ)/2) by ring,exp_neg,← one_div]
    exact one_div_le_one_div_of_le (exp_pos _) hlarge
  have hlow := exp_le_exp.mpr (show -(N : ℝ)/2≤-(2/5 : ℝ)*N by
    nlinarith only [Nat.cast_nonneg (α := ℝ) N])
  refine ⟨hi.trans hlow,?_⟩
  have hsub : ((X-M : ℕ) : ℝ)≤X := by exact_mod_cast Nat.sub_le X M
  calc
    _ ≤ (X : ℝ)/(M : ℝ)^2 := div_le_div_of_nonneg_right hsub (sq_nonneg _)
    _ ≤ (M*exp ((N : ℝ)/10))/(M : ℝ)^2 :=
      div_le_div_of_nonneg_right hwide (sq_nonneg _)
    _ = exp ((N : ℝ)/10)*(1/(M : ℝ)) := by field_simp
    _ ≤ exp ((N : ℝ)/10)*exp (-(N : ℝ)/2) :=
      mul_le_mul_of_nonneg_left hi (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

private theorem rounded_endpoint_separation {N : ℕ} (hN : 32≤N) {c T : ℝ}
    (hc : c≤(4/3 : ℝ)*N) (hT : (39/20 : ℝ)*N-1≤T)
    {y : ℝ} (hy : 54≤|y|) :
    c<T ∧ 2*((N : ℝ)+1)≤‖phaseDamping y‖*(T-c) := by
  have hn : (32 : ℝ)≤N := by exact_mod_cast hN
  have hv : (37/60 : ℝ)*N-1≤T-c := by linarith only [hc,hT]
  have hp : 0<T-c := by linarith only [hv,hn]
  have hz := mul_le_mul_of_nonneg_right (phaseDamping_norm hy) hp.le
  exact ⟨by linarith only [hp],by nlinarith only [hn,hv,hz]⟩

/-- Signed full-factorial lattice payment with literal endpoint rounding. -/
theorem normalized_densityTest_sum_bound {N M X : ℕ} (hN : 32≤N) (hM : 1≤M) (hMX : M≤X)
    {c u y : ℝ} (hc : 0≤c) (hxone : exp 1≤(M : ℝ)) (hy : 54≤|y|)
    (hu : 0≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hlarge : exp ((N : ℝ)/2)≤M) (hwide : (X : ℝ)≤M*exp ((N : ℝ)/10))
    (hlo : |c+log M-(39/20 : ℝ)*N|≤1/(M : ℝ))
    (hhi : |c+log X-(203/100 : ℝ)*N|≤1/(M : ℝ)) :
    |u^(N+1)*(∑ n∈Finset.Ioc M X, densityTest N c y n)|≤ownerSamplingBudget u y N := by
  have hcN : (0 : ℝ)≤(4/3 : ℝ)*N := by positivity
  have hm : (1 : ℝ)≤M := by exact_mod_cast hM
  have hx : (1 : ℝ)≤X := hm.trans (by exact_mod_cast hMX)
  have him : 1/(M : ℝ)≤1 := (div_le_one (by linarith : (0 : ℝ)<M)).mpr hm
  have hTa : (39/20 : ℝ)*N-1≤c+log M := by
    have h := (abs_le.mp hlo).1
    linarith only [h,him]
  have hTb : (39/20 : ℝ)*N-1≤c+log X := by
    have h := (abs_le.mp hhi).1
    nlinarith only [h,him,Nat.cast_nonneg (α := ℝ) N]
  have hc0 : (0 : ℝ)≤0 := by norm_num
  have hsepA := rounded_endpoint_separation hN hcN hTa hy
  have hsepB := rounded_endpoint_separation hN hcN hTb hy
  have hz54 := phaseDamping_norm hy
  have hz : phaseDamping y≠0 := norm_pos_iff.mp (by linarith only [hz54])
  have hd : 4/‖phaseDamping y‖≤(2/27 : ℝ) :=
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤4)
      (by norm_num : (0 : ℝ)<54) hz54).trans_eq (by norm_num)
  have hi := ownerPhase_interval_norm N hc0 hsepA.1 hsepB.1 hz
    (phaseDamping_re y) hsepA.2 hsepB.2
  have hcont : |∫ x : ℝ in (M : ℝ)..X, densityTest N c y x|≤
      (2/27 : ℝ)*(radial N (c+log M)+radial N (c+log X)) := by
    rw [density_test_integral hN hxone hMX hc y]
    simpa only [zero_add] using ((Complex.abs_re_le_norm _).trans hi).trans
      (mul_le_mul_of_nonneg_right hd (add_nonneg
        (radial_bounds N (by linarith [log_nonneg hm])).1
        (radial_bounds N (by linarith [log_nonneg hx])).1))
  have hloR : radial N (c+log M)≤radial N ((39/20 : ℝ)*N)+radialCap N/(M : ℝ) := by
    have h := radial_lipschitz N (T := c+log M) (U := (39/20 : ℝ)*N)
      (by linarith [log_nonneg hm])
      (by positivity : (0 : ℝ)≤(39/20 : ℝ)*N)
    have hb := h.trans (mul_le_mul_of_nonneg_left hlo (radialCap_nonneg N))
    have hb' := le_abs_self (radial N (c+log M)-radial N ((39/20 : ℝ)*N))
    have hh := hb'.trans hb
    ring_nf at hh ⊢
    linarith only [hh]
  have hhiR : radial N (c+log X)≤radial N ((203/100 : ℝ)*N)+radialCap N/(M : ℝ) := by
    have h := radial_lipschitz N (T := c+log X) (U := (203/100 : ℝ)*N)
      (by linarith [log_nonneg hx])
      (by positivity : (0 : ℝ)≤(203/100 : ℝ)*N)
    have hb := h.trans (mul_le_mul_of_nonneg_left hhi (radialCap_nonneg N))
    have hb' := le_abs_self (radial N (c+log X)-radial N ((203/100 : ℝ)*N))
    have hh := hb'.trans hb
    ring_nf at hh ⊢
    linarith only [hh]
  have hdisc := density_lattice_error hN hxone hMX hc y
  have hlohi := ZetaRieszTaggedOwnerComparison.normalized_core_endpoint_radial hu hU N
  have hrat := lattice_ratios hM hMX hlarge hwide
  have hcap := normalized_cap_fast hu hU N
  have hn : 0≤u^(N+1) := pow_nonneg hu _
  have hsmall1 : u^(N+1)*radialCap N/(M : ℝ)≤
      2*u*((N : ℝ)+1)*exp (-(N : ℝ)/4) := by
    have h := mul_le_mul_of_nonneg_left hrat.1 (mul_nonneg hn (radialCap_nonneg N))
    simpa only [mul_one,one_mul,div_eq_mul_inv,mul_assoc] using h.trans hcap
  have hsmall2 : u^(N+1)*radialCap N*((X-M : ℕ) : ℝ)/(M : ℝ)^2≤
      2*u*((N : ℝ)+1)*exp (-(N : ℝ)/4) := by
    have h := mul_le_mul_of_nonneg_left hrat.2 (mul_nonneg hn (radialCap_nonneg N))
    simpa only [mul_div_assoc,mul_assoc] using h.trans hcap
  have hsum : |u^(N+1)*(∑ n∈Finset.Ioc M X, densityTest N c y n)|≤
      u^(N+1)*((2/27 : ℝ)*(radial N ((39/20 : ℝ)*N)+radial N ((203/100 : ℝ)*N)+
        2*radialCap N/(M : ℝ))+
        (X-M : ℕ)*(2*((N : ℝ)+1)+2+|y|)*radialCap N/(M : ℝ)^2) := by
    rw [abs_mul,abs_of_nonneg hn]
    apply mul_le_mul_of_nonneg_left ?_ hn
    have h := (abs_add_le
      ((∑ n∈Finset.Ioc M X, densityTest N c y n)-∫ x : ℝ in (M : ℝ)..X, densityTest N c y x)
      (∫ x : ℝ in (M : ℝ)..X, densityTest N c y x)).trans (add_le_add hdisc hcont)
    have hh := mul_le_mul_of_nonneg_left (add_le_add hloR hhiR)
      (by norm_num : (0 : ℝ)≤2/27)
    simp only [sub_add_cancel] at h
    ring_nf at h hh ⊢
    linarith only [h,hh]
  apply hsum.trans
  unfold ownerSamplingBudget
  have hB : 0≤2*((N : ℝ)+1)+2+|y| := by positivity
  have hb := mul_le_mul_of_nonneg_left hsmall2 hB
  have he := mul_le_mul_of_nonneg_left (add_le_add hlohi.1 hlohi.2)
    (by norm_num : (0 : ℝ)≤2/27)
  have hr := mul_le_mul_of_nonneg_left hsmall1 (by norm_num : (0 : ℝ)≤4/27)
  have ht : 0≤2*u*((N : ℝ)+1)*exp (-(N : ℝ)/4) := by positivity
  ring_nf at hb he hr ht ⊢
  nlinarith only [hb,he,hr,ht]


private theorem floor_exp_log {v : ℝ} (hv : 1≤v) :
    1≤⌊exp v⌋₊ ∧ exp v≤2*(⌊exp v⌋₊ : ℝ) ∧
      |log (⌊exp v⌋₊ : ℝ)-v|≤1/(⌊exp v⌋₊ : ℝ) := by
  have he : 1≤exp v := by linarith only [add_one_le_exp v,hv]
  have hm : 1≤⌊exp v⌋₊ := (Nat.one_le_floor_iff (exp v)).mpr he
  have hm1 : (1 : ℝ)≤⌊exp v⌋₊ := by exact_mod_cast hm
  have hm0 : (0 : ℝ)<⌊exp v⌋₊ := by linarith only [hm1]
  have hf := Nat.floor_le (exp_pos v).le
  have htail := (Nat.lt_floor_add_one (exp v)).le
  have hl : log (⌊exp v⌋₊ : ℝ)≤v := by
    simpa only [log_exp] using log_le_log hm0 hf
  have hb := log_le_sub_one_of_pos (div_pos (exp_pos v) hm0)
  rw [log_div (exp_pos v).ne' hm0.ne',log_exp] at hb
  have hfrac : exp v/(⌊exp v⌋₊ : ℝ)-1≤1/(⌊exp v⌋₊ : ℝ) := by
    apply (le_div_iff₀ hm0).mpr
    field_simp at ⊢
    nlinarith only [htail]
  refine ⟨hm,by linarith only [htail,hm1],?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hl),neg_sub]
  exact hb.trans hfrac

/-- Literal floor geometry for the wider genuine unallocated-owner range. -/
theorem densityFloor_geometry {N : ℕ} (hN : 64≤N) {c : ℝ} (hc : c≤(7/5 : ℝ)*N) :
    let M := coreFloor N c (39/20)
    let X := coreFloor N c (203/100)
    1≤M ∧ M≤X ∧ exp ((N : ℝ)/2)≤M ∧ (X : ℝ)≤M*exp ((N : ℝ)/10) ∧
      |c+log M-(39/20 : ℝ)*N|≤1/(M : ℝ) ∧
      |c+log X-(203/100 : ℝ)*N|≤1/(M : ℝ) := by
  dsimp only
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hvA : 1≤(39/20 : ℝ)*N-c := by linarith only [hc,hn]
  have hvB : 1≤(203/100 : ℝ)*N-c := by linarith only [hc,hn]
  have hA := floor_exp_log hvA
  have hB := floor_exp_log hvB
  have hMX : coreFloor N c (39/20)≤coreFloor N c (203/100) := by
    apply Nat.floor_mono
    apply exp_le_exp.mpr
    nlinarith only [hn]
  have hlarge : exp ((N : ℝ)/2)≤coreFloor N c (39/20) := by
    have hmargin : 2≤exp ((1/20 : ℝ)*N) := by
      have he := add_one_le_exp ((1/20 : ℝ)*N)
      linarith only [he,hn]
    have hmul := mul_le_mul_of_nonneg_left hmargin (exp_pos ((N : ℝ)/2)).le
    rw [← exp_add] at hmul
    have he : (N : ℝ)/2+(1/20)*N=(11/20 : ℝ)*N := by ring
    rw [he] at hmul
    have hpow : exp ((11/20 : ℝ)*N)≤exp ((39/20 : ℝ)*N-c) :=
      exp_le_exp.mpr (by linarith only [hc])
    have hbound := hmul.trans (hpow.trans hA.2.1)
    change _≤(⌊exp ((39/20 : ℝ)*N-c)⌋₊ : ℝ)
    linarith only [hbound]
  have hwide : (coreFloor N c (203/100) : ℝ)≤
      coreFloor N c (39/20)*exp ((N : ℝ)/10) := by
    have hmargin : 2≤exp ((N : ℝ)/50) := by
      have he := add_one_le_exp ((N : ℝ)/50)
      linarith only [he,hn]
    calc
      _ ≤ exp ((203/100 : ℝ)*N-c) := Nat.floor_le (exp_pos _).le
      _ = exp ((39/20 : ℝ)*N-c)*exp ((2/25 : ℝ)*N) := by
        rw [← exp_add]; congr 1; ring
      _ ≤ (2*(coreFloor N c (39/20) : ℝ))*exp ((2/25 : ℝ)*N) :=
        mul_le_mul_of_nonneg_right hA.2.1 (exp_pos _).le
      _ ≤ (coreFloor N c (39/20) : ℝ)*(exp ((N : ℝ)/50)*exp ((2/25 : ℝ)*N)) := by
        have h := mul_le_mul_of_nonneg_left hmargin
          (show 0≤(coreFloor N c (39/20) : ℝ)*exp ((2/25 : ℝ)*N) by positivity)
        calc
          _ = ((coreFloor N c (39/20) : ℝ)*exp ((2/25 : ℝ)*N))*2 := by ring
          _ ≤ _ := h
          _ = _ := by ring
      _ = _ := by rw [← exp_add]; congr 1; ring
  have hlo : |c+log (coreFloor N c (39/20))-(39/20 : ℝ)*N|≤
      1/(coreFloor N c (39/20) : ℝ) := by
    change |c+log (⌊exp ((39/20 : ℝ)*N-c)⌋₊ : ℝ)-(39/20 : ℝ)*N|≤_
    change _≤1/(⌊exp ((39/20 : ℝ)*N-c)⌋₊ : ℝ)
    convert hA.2.2 using 1
    congr 1
    ring
  have hhi : |c+log (coreFloor N c (203/100))-(203/100 : ℝ)*N|≤
      1/(coreFloor N c (39/20) : ℝ) := by
    have hm0 : (0 : ℝ)<⌊exp ((39/20 : ℝ)*N-c)⌋₊ := by
      exact_mod_cast (show 0<⌊exp ((39/20 : ℝ)*N-c)⌋₊ by omega)
    have hmx : (⌊exp ((39/20 : ℝ)*N-c)⌋₊ : ℝ)≤⌊exp ((203/100 : ℝ)*N-c)⌋₊ := by
      exact_mod_cast hMX
    have h := hB.2.2.trans (one_div_le_one_div_of_le hm0 hmx)
    change |c+log (⌊exp ((203/100 : ℝ)*N-c)⌋₊ : ℝ)-(203/100 : ℝ)*N|≤_
    change _≤1/(⌊exp ((39/20 : ℝ)*N-c)⌋₊ : ℝ)
    convert h using 1
    congr 1
    ring
  exact ⟨hA.1,hMX,hlarge,hwide,hlo,hhi⟩

/-- Source-scale payment of the unallocated integer-density main,
with the original complete total-log window and full product phase. -/
theorem normalized_density_core_bound {N : ℕ} (hN : 64≤N) {c u y : ℝ}
    (hc : 0≤c) (hcN : c≤(7/5 : ℝ)*N) (hy : 54≤|y|)
    (hu : 0≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    |u^(N+1)*∑ n∈Finset.Ioc (coreFloor N c (39/20)) (coreFloor N c (203/100)),
      densityTest N c y n|≤ownerSamplingBudget u y N := by
  obtain ⟨hM,hMX,hlarge,hwide,hlo,hhi⟩ := densityFloor_geometry hN hcN
  have hNM : exp (1 : ℝ)≤(coreFloor N c (39/20) : ℝ) :=
    (exp_le_exp.mpr (by
      have hn : (64 : ℝ)≤N := by exact_mod_cast hN
      linarith)).trans hlarge
  exact normalized_densityTest_sum_bound (by omega) hM hMX hc hNM hy hu hU
    hlarge hwide hlo hhi

end RiemannGaussian.ZetaRieszUnallocatedOwnerPhase

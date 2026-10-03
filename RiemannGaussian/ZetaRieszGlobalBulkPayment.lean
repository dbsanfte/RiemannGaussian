/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGlobalCompletionBoundary
import RiemannGaussian.ZetaRieszLargeOrderCore

/-!
# Signed payment of the completed squarefree bulk

All squarefree counts are joined, including the restored ordinary primes
and semiprimes. The counting error has a fixed power saving. Its signed
density main is paid by the exact complete-window phase primitive, rather
than an absolute radial integral. This does not pay the prime, semiprime,
raw-owner or other literal-mask completion boundaries.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology MeasureTheory
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszGlobalBulkPayment
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

private theorem zero_amplitude (N : ℕ) {n : ℕ} (hn : 1<n) :
    ownerAmplitude N 0 n=radial N (log n) := by
  have hl : log (n : ℝ)≠0 := (log_pos (by exact_mod_cast hn)).ne'
  simp only [ownerAmplitude,zero_add,div_self hl,ownerWeight_one,one_mul]

private theorem zero_test_deriv {N : ℕ} (hN : 32≤N) {x : ℝ}
    (hx : 1<x) (y : ℝ) :
    HasDerivAt (ownerTest N 0 y) (ownerTestDerivative N 0 y x) x := by
  have hx0 : 0<x := by linarith
  have ht : 0+log x≠0 := by simpa only [zero_add] using (log_pos hx).ne'
  have hg := (ownerLogPhase_deriv hN 0 y ht).comp x
    ((hasDerivAt_log hx0.ne').const_add 0)
  apply (hg.div (hasDerivAt_id x) hx0.ne').congr_deriv
  dsimp [ownerTestDerivative]
  field_simp

private theorem zero_test_derivative_bound (N : ℕ) {x : ℝ}
    (hx : exp 1≤x) (y : ℝ) :
    |ownerTestDerivative N 0 y x|≤
      (2*((N : ℝ)+1)+2+|y|)*radialCap N/x^2 := by
  have hx0 : 0<x := (exp_pos _).trans_le hx
  have hl : 1≤log x := by simpa only [log_exp] using log_le_log (exp_pos _) hx
  have hd := ownerLogDerivative_bound N (c:=0) (T:=log x) (by norm_num)
    (by linarith) hl y
  have hb := ownerLogPhase_bound N (c:=0) (T:=log x) (by norm_num)
    (by linarith) (by linarith) y
  unfold ownerTestDerivative
  simp only [zero_add]
  rw [abs_div,abs_of_nonneg (sq_nonneg x)]
  exact (div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add hd hb))
    (sq_nonneg x)).trans_eq (by ring)

private theorem zero_lattice_error {N M X : ℕ} (hN : 32≤N)
    (hM : exp 1≤(M : ℝ)) (hMX : M≤X) (y : ℝ) :
    |(∑ n∈Finset.Ioc M X,ownerTest N 0 y n)-
      (∫ x : ℝ in (M : ℝ)..X,ownerTest N 0 y x)|≤
      (X-M : ℕ)*(2*((N : ℝ)+1)+2+|y|)*radialCap N/(M : ℝ)^2 := by
  have hm : 0<(M : ℝ) := (exp_pos _).trans_le hM
  have he : 1<exp (1 : ℝ) := one_lt_exp_iff.mpr (by norm_num)
  have hcap := radialCap_nonneg N
  let E := (2*((N : ℝ)+1)+2+|y|)*radialCap N/(M : ℝ)^2
  have hE : 0≤E := by dsimp [E]; positivity
  have hb x (hx : x∈Set.Icc (M : ℝ) X) : |ownerTestDerivative N 0 y x|≤E := by
    apply (zero_test_derivative_bound N (hM.trans hx.1) y).trans
    apply div_le_div_of_nonneg_left (by positivity) (by positivity : (0 : ℝ)<(M : ℝ)^2)
    nlinarith only [hx.1,hm]
  have h := integer_sampling_error hMX hE
    (fun x hx => zero_test_deriv hN (he.trans_le (hM.trans hx.1)) y) hb
  exact h.trans_eq (by dsimp [E]; ring)

private theorem zero_test_integral {N M X : ℕ} (hN : 32≤N)
    (hM : exp 1≤(M : ℝ)) (hMX : M≤X) (y : ℝ) :
    (∫ x : ℝ in (M : ℝ)..X,ownerTest N 0 y x)=
      (∫ T : ℝ in (log M)..(log X),ownerPhase N 0 (phaseDamping y) T).re := by
  have hm : 1<(M : ℝ) := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ)<1)).trans_le hM
  have hab : (M : ℝ)≤X := by exact_mod_cast hMX
  have hcont : ContinuousOn (ownerTest N 0 y) (Set.Icc (M : ℝ) X) := by
    intro x hx
    exact (zero_test_deriv hN (hm.trans_le hx.1) y).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (ownerTest N 0 y) volume (M : ℝ) X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hcont
  have hz : phaseDamping y≠0 := by
    intro he
    have := congrArg Complex.re he
    rw [phaseDamping_re] at this
    norm_num at this
  have hreal : (∫ T : ℝ in (log M)..(log X),ownerPhase N 0 (phaseDamping y) T).re=
      (ownerPrimitive N 0 (phaseDamping y) (log M)).re-
        (ownerPrimitive N 0 (phaseDamping y) (log X)).re := by
    rw [ownerPhase_integral N 0 hz,Complex.sub_re]
  have hf x (hx : x∈Set.uIcc (M : ℝ) X) :
      HasDerivAt (fun v : ℝ => (ownerPrimitive N 0 (phaseDamping y) (log v)).re)
        (-ownerTest N 0 y x) x := by
    rw [Set.uIcc_of_le hab] at hx
    have hx1 := hm.trans_le hx.1
    have hx0 : 0<x := by linarith
    have ht : log x≠0 := (log_pos hx1).ne'
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
      ((ownerPrimitive_deriv N 0 hz (log x)).scomp x (hasDerivAt_log hx0.ne'))
    apply h.congr_deriv
    simp only [Complex.reCLM_apply,Complex.real_smul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,zero_mul,sub_zero]
    rw [← ownerLogPhase_eq_re N 0 y ht]
    dsimp [ownerTest]
    simp only [zero_add]
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

private theorem zero_test_sum_bound {N M X : ℕ} (hN : 32≤N) (hM : 1≤M) (hMX : M≤X)
    {u y : ℝ} (hc : exp 1≤(M : ℝ)) (hy : 54≤|y|)
    (hu : 0≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hlarge : exp ((N : ℝ)/2)≤M) (hwide : (X : ℝ)≤M*exp ((N : ℝ)/10))
    (hlo : |0+log M-(39/20 : ℝ)*N|≤1/(M : ℝ))
    (hhi : |0+log X-(203/100 : ℝ)*N|≤1/(M : ℝ)) :
    |u^(N+1)*(∑ n∈Finset.Ioc M X, ownerTest N 0 y n)|≤ownerSamplingBudget u y N := by
  have hcN : (0 : ℝ)≤(4/3 : ℝ)*N := by positivity
  have hm : (1 : ℝ)≤M := by exact_mod_cast hM
  have hx : (1 : ℝ)≤X := hm.trans (by exact_mod_cast hMX)
  have him : 1/(M : ℝ)≤1 := (div_le_one (by linarith : (0 : ℝ)<M)).mpr hm
  have hTa : (39/20 : ℝ)*N-1≤0+log M := by
    have h := (abs_le.mp hlo).1
    linarith only [h,him]
  have hTb : (39/20 : ℝ)*N-1≤0+log X := by
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
  have hcont : |∫ x : ℝ in (M : ℝ)..X, ownerTest N 0 y x|≤
      (2/27 : ℝ)*(radial N (0+log M)+radial N (0+log X)) := by
    rw [zero_test_integral hN hc hMX y]
    simpa only [zero_add] using ((Complex.abs_re_le_norm _).trans hi).trans
      (mul_le_mul_of_nonneg_right hd (add_nonneg
        (radial_bounds N (by linarith [log_nonneg hm])).1
        (radial_bounds N (by linarith [log_nonneg hx])).1))
  have hloR : radial N (0+log M)≤radial N ((39/20 : ℝ)*N)+radialCap N/(M : ℝ) := by
    have h := radial_lipschitz N (T := 0+log M) (U := (39/20 : ℝ)*N)
      (by linarith [log_nonneg hm])
      (by positivity : (0 : ℝ)≤(39/20 : ℝ)*N)
    have hb := h.trans (mul_le_mul_of_nonneg_left hlo (radialCap_nonneg N))
    have hb' := le_abs_self (radial N (0+log M)-radial N ((39/20 : ℝ)*N))
    have hh := hb'.trans hb
    ring_nf at hh ⊢
    linarith only [hh]
  have hhiR : radial N (0+log X)≤radial N ((203/100 : ℝ)*N)+radialCap N/(M : ℝ) := by
    have h := radial_lipschitz N (T := 0+log X) (U := (203/100 : ℝ)*N)
      (by linarith [log_nonneg hx])
      (by positivity : (0 : ℝ)≤(203/100 : ℝ)*N)
    have hb := h.trans (mul_le_mul_of_nonneg_left hhi (radialCap_nonneg N))
    have hb' := le_abs_self (radial N (0+log X)-radial N ((203/100 : ℝ)*N))
    have hh := hb'.trans hb
    ring_nf at hh ⊢
    linarith only [hh]
  have hdisc := zero_lattice_error hN hc hMX y
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
  have hsum : |u^(N+1)*(∑ n∈Finset.Ioc M X, ownerTest N 0 y n)|≤
      u^(N+1)*((2/27 : ℝ)*(radial N ((39/20 : ℝ)*N)+radial N ((203/100 : ℝ)*N)+
        2*radialCap N/(M : ℝ))+
        (X-M : ℕ)*(2*((N : ℝ)+1)+2+|y|)*radialCap N/(M : ℝ)^2) := by
    rw [abs_mul,abs_of_nonneg hn]
    apply mul_le_mul_of_nonneg_left ?_ hn
    have h := (abs_add_le
      ((∑ n∈Finset.Ioc M X, ownerTest N 0 y n)-∫ x : ℝ in (M : ℝ)..X, ownerTest N 0 y x)
      (∫ x : ℝ in (M : ℝ)..X, ownerTest N 0 y x)).trans (add_le_add hdisc hcont)
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


/-- The full integer density phase, with every original factorial order.
Only the two exterior endpoints and ordinary integer sampling are priced. -/
theorem full_lattice_phase_bound {N : ℕ} (hN : 64≤N) {u y : ℝ}
    (hu : 0≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    |u^(N+1)*∑ n∈Finset.Ioc (coreFloor N 0 (39/20)) (coreFloor N 0 (203/100)),
      radial N (log n)*cos (y*log n)/(n : ℝ)|≤ownerSamplingBudget u y N := by
  obtain ⟨hM,hMX,hlarge,hwide,hlo,hhi⟩ := coreFloor_geometry hN (c:=0) (by positivity)
  have hNM : exp (1 : ℝ)≤(coreFloor N 0 (39/20) : ℝ) :=
    (exp_le_exp.mpr (by
      have hn : (64 : ℝ)≤N := by exact_mod_cast hN
      linarith)).trans hlarge
  have hb := zero_test_sum_bound (by omega : 32≤N) hM hMX hNM hy hu hU
    hlarge hwide (by simpa only [zero_add] using hlo) (by simpa only [zero_add] using hhi)
  have he n (hn : n∈Finset.Ioc (coreFloor N 0 (39/20)) (coreFloor N 0 (203/100))) :
      ownerTest N 0 y n=radial N (log n)*cos (y*log n)/(n : ℝ) := by
    rw [ownerTest_nat,zero_amplitude N (by have := (Finset.mem_Ioc.mp hn).1; omega)]
    simp only [zero_add]
  simpa only [Finset.sum_congr rfl he] using hb

private theorem hinge_profile_end (c : ℝ) :
    max 0 (c-log ((⌊exp c⌋₊+1 : ℕ) : ℝ))=0 := by
  have he : exp c < ((⌊exp c⌋₊+1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (exp c)
  have hl : c < log ((⌊exp c⌋₊+1 : ℕ) : ℝ) := by
    simpa only [log_exp] using log_lt_log (exp_pos _) he
  exact max_eq_left (by linarith)

private theorem riesz_eq_hinge_profile (c : ℝ) {n : ℕ} (hn : 0 < n) :
    VaughanLogAverage.riesz c n =
      ∑ d ∈ Finset.Icc 1 ⌊exp c⌋₊,
        max 0 (c-log d)*(if d ∣ n then (μ d : ℝ) else 0) := by
  have hr := Nat.floor_le (exp_pos c).le
  have he : exp c < (⌊exp c⌋₊ : ℝ)+1 := Nat.lt_floor_add_one _
  conv_lhs => rw [← log_exp c,ZetaRieszSieveMean.riesz_eq_log_prefix _ (exp_pos _) hr he hn]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (0 : ℝ)<d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hdx : (d : ℝ) ≤ exp c :=
    (show (d : ℝ) ≤ ⌊exp c⌋₊ by exact_mod_cast (Finset.mem_Icc.mp hd).2).trans hr
  have hdl : log d ≤ c := by simpa only [log_exp] using log_le_log hd0 hdx
  rw [max_eq_right (sub_nonneg.mpr hdl)]
  by_cases hdn : d ∣ n
  · simp only [hdn,if_true,log_div (exp_pos c).ne' hd0.ne',log_exp]
    ring
  · simp [hdn]


private theorem radial_amplitude_variation {M X : ℕ} (hM : 0<M)
    (hMX : M<X) (hXM : X≤2*M) (N : ℕ) :
    (∑ k∈Finset.Ico (M+1) X,
      |radial N (log k)-radial N (log (k+1 : ℕ))|)≤radialCap N := by
  let m := X-(M+1)
  let v := fun i : ℕ => log (M+1+i : ℕ)
  have hv i : 0≤v i := log_natCast_nonneg _
  have hvi i : v i≤v (i+1) := log_le_log (by positivity)
    (by exact_mod_cast (show M+1+i≤M+1+(i+1) by omega))
  have hlen : v m-v 0≤1 := by
    have hem : M+1+m=X := by dsimp [m]; omega
    have hMr : (0 : ℝ)<M+1 := by positivity
    have hXr : (0 : ℝ)<X := by exact_mod_cast (show 0<X by omega)
    have hr : (X : ℝ)/(M+1)≤2 := by
      apply (div_le_iff₀ hMr).mpr
      have h := (show (X : ℝ)≤2*M by exact_mod_cast hXM)
      linarith
    have hb := log_le_sub_one_of_pos (div_pos hXr hMr)
    rw [log_div hXr.ne' hMr.ne'] at hb
    dsimp [v]
    rw [hem,Nat.add_zero,Nat.cast_add,Nat.cast_one]
    linarith
  have hb : (∑ i∈Finset.range m,|radial N (v i)-radial N (v (i+1))|)≤radialCap N := by
    calc
      _ ≤ ∑ i∈Finset.range m,radialCap N*(v (i+1)-v i) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [abs_of_nonpos (sub_nonpos.mpr (hvi i)),neg_sub] using
          radial_lipschitz N (hv i) (hv (i+1))
      _ = radialCap N*(v m-v 0) := by rw [← Finset.mul_sum,Finset.sum_range_sub]
      _ ≤ radialCap N := mul_le_of_le_one_right (radialCap_nonneg N) hlen
  rw [Finset.sum_Ico_eq_sum_range]
  convert hb using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [v]
  congr 2

/-- The entire signed hinge is compared on a full integer shell.
Squarefreeness is in the counting measure; no prime/count deletion occurs. -/
private theorem full_shell_compare {N M X : ℕ} (hM : 0<M) (hMX : M<X)
    (hXM : X≤2*M) (hlarge : exp ((N : ℝ)/2)≤M) {L : ℝ} (hL : 0<L)
    (hcut : ⌊exp L⌋₊^4≤M^3) (y : ℝ) :
    |(∑ n∈Finset.Ioc M X,if Squarefree n then
        radial N (log n)*cos (y*log n)/(n : ℝ)*VaughanLogAverage.riesz L n else 0)-
      ZetaRieszSignedDensityMain.densityRiesz L*
        (∑ n∈Finset.Ioc M X,radial N (log n)*cos (y*log n)/(n : ℝ))|≤
      ZetaRieszLongCutoffError.countingConstant*exp (-(N : ℝ)/128)*
        ((4+|y|)*radialCap N)*L := by
  let R := ⌊exp L⌋₊
  let f := fun d : ℕ => max 0 (L-log d)
  let w := shellWeight M X (fun n => radial N (log n)) y 0
  have hR : 0<R := by
    have he : 1≤exp L := one_le_exp_iff.mpr hL.le
    have hf : 1≤R := (Nat.one_le_floor_iff _).mpr he
    omega
  have hend : w (X+1)=0 := by simp [w,shellWeight]
  have hactive k (_hk : k∈Finset.Icc 1 X) (hz : w k≠w (k+1)) : M≤k := by
    by_contra h
    have hkM : k<M := by omega
    simp [w,shellWeight,show ¬M<k by omega,show ¬M<k+1 by omega] at hz
  have hd D (hD : D∈Finset.Icc 1 R) :=
    ZetaRieszLongCutoffError.weighted_error_exponential X D N w (1/2) hend
      (Finset.mem_Icc.mp hD).1
      (fun k hk hz => (Nat.pow_le_pow_left (Finset.mem_Icc.mp hD).2 4).trans
        (hcut.trans (Nat.pow_le_pow_left (hactive k hk hz) 3)))
      (fun k hk hz => by
        have hm : (M : ℝ)≤k := by exact_mod_cast hactive k hk hz
        simpa only [div_eq_mul_inv,mul_comm,one_mul] using hlarge.trans hm)
  simp only [show -((1/2 : ℝ)*N)/64=-(N : ℝ)/128 by ring] at hd
  have he : (∑ n∈Finset.Icc 1 X,w n*(if Squarefree n then VaughanLogAverage.riesz L n else 0))=
      ∑ D∈Finset.Icc 1 R,(f D-f (D+1))*
        (∑ n∈Finset.Icc 1 X,w n*(if Squarefree n then sharp D n else 0)) := by
    have hn n (hn : n∈Finset.Icc 1 X) :
        (if Squarefree n then VaughanLogAverage.riesz L n else 0)=
          ∑ D∈Finset.Icc 1 R,(f D-f (D+1))*(if Squarefree n then sharp D n else 0) := by
      by_cases hs : Squarefree n
      · rw [if_pos hs,riesz_eq_hinge_profile L (Finset.mem_Icc.mp hn).1]
        rw [ZetaRieszSignedCutoffEnergy.abel_profile R f
          (fun d => if d∣n then (μ d : ℝ) else 0) (hinge_profile_end L)]
        simp only [if_pos hs,sharp]
      · simp [hs]
    rw [Finset.sum_congr rfl (fun n hn' => congrArg (w n*·) (hn n hn'))]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro D _
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hm : (∑ D∈Finset.Icc 1 R,(f D-f (D+1))*densityPrefix D)=
      ZetaRieszSignedDensityMain.densityRiesz L := by
    rw [ZetaRieszSignedDensityMain.densityRiesz_eq_hinge L (le_refl R)]
    symm
    have hp := ZetaRieszSignedCutoffEnergy.abel_profile R f
      (fun d => (μ d : ℝ)*SquarefreeCounting.density d.primeFactors) (hinge_profile_end L)
    simpa only [densityPrefix,f,mul_comm] using hp
  have hb : |(∑ n∈Finset.Icc 1 X,w n*(if Squarefree n then VaughanLogAverage.riesz L n else 0))-
      ZetaRieszSignedDensityMain.densityRiesz L*(∑ n∈Finset.Icc 1 X,w n)|≤
        ZetaRieszLongCutoffError.countingConstant*exp (-(N : ℝ)/128)*
          (∑ k∈Finset.Icc 1 X,(k : ℝ)*|w k-w (k+1)|)*L := by
    rw [he,← hm,Finset.sum_mul,← Finset.sum_sub_distrib]
    have ht := Finset.sum_le_sum (fun D hD =>
      mul_le_mul_of_nonneg_left (hd D hD) (abs_nonneg (f D-f (D+1))))
    rw [← Finset.sum_mul,ZetaRieszLongCutoffError.hinge_profile_variation L,
      max_eq_right hL.le] at ht
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have ha D : |(f D-f (D+1))*(∑ n∈Finset.Icc 1 X,w n*(if Squarefree n then sharp D n else 0))-
        (f D-f (D+1))*densityPrefix D*(∑ n∈Finset.Icc 1 X,w n)|=
        |f D-f (D+1)| * |(∑ n∈Finset.Icc 1 X,w n*(if Squarefree n then sharp D n else 0))-
          densityPrefix D*(∑ n∈Finset.Icc 1 X,w n)| := by rw [← abs_mul]; congr 1; ring
    simp_rw [ha]
    exact ht.trans_eq (by ring)
  have hv : (∑ k∈Finset.Icc 1 X,(k : ℝ)*|w k-w (k+1)|)≤(4+|y|)*radialCap N := by
    have hh := shellWeight_variation hM hMX hXM (fun n => radial N (log n)) y 0
      (radialCap N) (radialCap_nonneg N) (fun n _ => by
        rw [abs_of_nonneg (radial_bounds N (log_natCast_nonneg n)).1]
        exact (radial_bounds N (log_natCast_nonneg n)).2)
    exact hh.trans (by
      have h := radial_amplitude_variation hM hMX hXM N
      linarith only [h])
  have hs (g : ℕ→ℝ) : (∑ n∈Finset.Icc 1 X,w n*g n)=
      ∑ n∈Finset.Ioc M X,radial N (log n)*cos (y*log n)/(n : ℝ)*g n := by
    have hsub : Finset.Ioc M X⊆Finset.Icc 1 X := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ioc.mp hn).1; omega,
        (Finset.mem_Ioc.mp hn).2⟩
    rw [← Finset.sum_subset hsub (by
      intro n hn hnot
      have hi := (Finset.mem_Icc.mp hn).2
      have hm : ¬M<n := fun hn' => hnot (Finset.mem_Ioc.mpr ⟨hn',hi⟩)
      simp [w,shellWeight,hm])]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [w,shellWeight,Finset.mem_Ioc.mp hn,and_self,ite_true,zero_add]
  rw [hs (fun n => if Squarefree n then VaughanLogAverage.riesz L n else 0)] at hb
  have hs1 := hs (fun _ => 1)
  simp only [mul_one] at hs1
  rw [hs1] at hb
  simp only [mul_ite,mul_zero] at hb
  exact hb.trans (by
    have h := mul_le_mul_of_nonneg_left hv
      (by positivity [ZetaRieszLongCutoffError.countingConstant_pos] :
        0≤ZetaRieszLongCutoffError.countingConstant*exp (-(N : ℝ)/128))
    exact mul_le_mul_of_nonneg_right h hL.le)

private theorem partition_sum (f : ℕ→ℝ) (a : ℕ→ℕ) (ha : Monotone a) (b : ℕ) :
    (∑ i∈Finset.range b,∑ n∈Finset.Ioc (a i) (a (i+1)),f n)=
      ∑ n∈Finset.Ioc (a 0) (a b),f n := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ,ih]
    exact Finset.sum_Ioc_consecutive f (ha (Nat.zero_le b)) (ha (Nat.le_succ b))

private def front (M X i : ℕ) : ℕ := min X (2^i*M)

private theorem front_monotone (M X : ℕ) : Monotone (front M X) := by
  intro i j hij
  unfold front
  exact min_le_min_left X (Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by omega : 1≤2) hij))

private theorem front_bounds {M X : ℕ} (hMX : M≤X) (i : ℕ) :
    M≤front M X i ∧ front M X i≤X := by
  refine ⟨le_min hMX ?_,min_le_left _ _⟩
  have h : 1≤2^i := Nat.one_le_pow i 2 (by omega)
  simpa using Nat.mul_le_mul_right M h

private theorem front_dyadic {M X i : ℕ} (hi : front M X i<front M X (i+1)) :
    front M X (i+1)≤2*front M X i := by
  have hp : 2^i*M<X := by
    by_contra h
    have he : front M X i=X := min_eq_left (by omega)
    have hb : front M X (i+1)≤X := min_le_left _ _
    omega
  rw [show front M X i=2^i*M from min_eq_right hp.le]
  have hb : front M X (i+1)≤2^(i+1)*M := min_le_right _ _
  rw [pow_succ] at hb
  nlinarith only [hb]

private theorem core_cover {N : ℕ} (hN : 64≤N) {c : ℝ} (hc : c≤(4/3 : ℝ)*N) :
    coreFloor N c (203/100)≤2^N*coreFloor N c (39/20) := by
  have hwide := (coreFloor_geometry hN hc).2.2.2.1
  have he : exp (1/10 : ℝ)≤2 := by
    have hl := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<2)
    have hlog : (1/10 : ℝ)≤log 2 := by norm_num at hl; linarith
    simpa only [exp_log (by norm_num : (0 : ℝ)<2)] using exp_le_exp.mpr hlog
  have hn := pow_le_pow_left₀ (exp_pos (1/10 : ℝ)).le he N
  rw [← exp_nat_mul] at hn
  have hh := hwide.trans (mul_le_mul_of_nonneg_left
    (show exp ((N : ℝ)/10)≤(2 : ℝ)^N by simpa only [div_eq_mul_inv,mul_comm,one_mul] using hn)
      (Nat.cast_nonneg _))
  exact_mod_cast (show (coreFloor N c (203/100) : ℝ)≤
    (2 : ℝ)^N*coreFloor N c (39/20) by simpa only [mul_comm] using hh)

private theorem full_cutoff_geometry {u : ℝ} (hu : 1/2≤u) {N : ℕ} (hN : 64≤N) :
    ⌊exp (SquarefreeVaughanLogSource.length u N)⌋₊^4≤(coreFloor N 0 (39/20))^3 := by
  let M := coreFloor N 0 (39/20)
  let L := SquarefreeVaughanLogSource.length u N
  let R := ⌊exp L⌋₊
  obtain ⟨hM,_hMX,_hlarge,_hwide,hlo,_hhi⟩ :=
    coreFloor_geometry hN (c:=0) (by positivity)
  simp only [zero_add] at hlo
  have hm : (1 : ℝ)≤M := by exact_mod_cast hM
  have hm0 : (0 : ℝ)<M := by linarith
  have hL := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hi : 1/(M : ℝ)≤1 := (div_le_one hm0).mpr hm
  have hl : (39/20 : ℝ)*N-1≤log M := by
    have ht := (abs_le.mp hlo).1
    change _≤log M-((39/20 : ℝ)*N) at ht
    linarith only [ht,hi]
  have he : 4*L≤3*log M := by dsimp [L]; linarith only [hL,hl,hn]
  have hr : (R : ℝ)≤exp L := Nat.floor_le (exp_pos _).le
  have hp : (R : ℝ)^4≤(M : ℝ)^3 := by
    calc
      _ ≤ exp L^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hr _
      _ = exp (4*L) := by rw [← exp_nat_mul]; norm_num
      _ ≤ exp (3*log M) := exp_le_exp.mpr he
      _ = (M : ℝ)^3 := by
        change exp (((3 : ℕ) : ℝ)*log M)=(M : ℝ)^3
        rw [exp_nat_mul,exp_log hm0]
  exact_mod_cast hp

private theorem full_core_compare {u : ℝ} (hu : 1/2≤u) {N : ℕ} (hN : 64≤N) (y : ℝ) :
    let L := SquarefreeVaughanLogSource.length u N
    |(∑ n∈Finset.Ioc (coreFloor N 0 (39/20)) (coreFloor N 0 (203/100)),
        if Squarefree n then radial N (log n)*cos (y*log n)/(n : ℝ)*
          VaughanLogAverage.riesz L n else 0)-
      ZetaRieszSignedDensityMain.densityRiesz L*
        (∑ n∈Finset.Ioc (coreFloor N 0 (39/20)) (coreFloor N 0 (203/100)),
          radial N (log n)*cos (y*log n)/(n : ℝ))|≤
      (N : ℝ)*ZetaRieszLongCutoffError.countingConstant*exp (-(N : ℝ)/128)*
        ((4+|y|)*radialCap N)*L := by
  dsimp only
  let M := coreFloor N 0 (39/20)
  let X := coreFloor N 0 (203/100)
  let L := SquarefreeVaughanLogSource.length u N
  obtain ⟨hM,hMX,hlarge,_hwide,_hlo,_hhi⟩ := coreFloor_geometry hN (c:=0) (by positivity)
  change 1≤M at hM
  change M≤X at hMX
  have h0 : front M X 0=M := by simp [front,min_eq_right hMX]
  have hn : front M X N=X := min_eq_left (core_cover hN (c:=0) (by positivity))
  let B := ZetaRieszLongCutoffError.countingConstant*exp (-(N : ℝ)/128)*
    ((4+|y|)*radialCap N)*L
  have hB : 0≤B := by dsimp [B]; positivity [ZetaRieszLongCutoffError.countingConstant_pos,
    SquarefreeVaughanLogSource.length_pos u N,radialCap_nonneg N]
  let F := fun n : ℕ => (if Squarefree n then radial N (log n)*cos (y*log n)/(n : ℝ)*
    VaughanLogAverage.riesz L n else 0)-
      ZetaRieszSignedDensityMain.densityRiesz L*(radial N (log n)*cos (y*log n)/(n : ℝ))
  have hj (m x : ℕ) : (∑ n∈Finset.Ioc m x,if Squarefree n then
      radial N (log n)*cos (y*log n)/(n : ℝ)*VaughanLogAverage.riesz L n else 0)-
      ZetaRieszSignedDensityMain.densityRiesz L*
        (∑ n∈Finset.Ioc m x,radial N (log n)*cos (y*log n)/(n : ℝ))=
        ∑ n∈Finset.Ioc m x,F n := by simp only [F,Finset.sum_sub_distrib,Finset.mul_sum]
  have hloc i (_hi : i∈Finset.range N) :
      |∑ n∈Finset.Ioc (front M X i) (front M X (i+1)),F n|≤B := by
    have hmi := front_bounds hMX i
    rcases eq_or_lt_of_le (front_monotone M X (Nat.le_succ i)) with he | hi
    · rw [he]
      simp only [Finset.Ioc_self,Finset.sum_empty,abs_zero]
      exact hB
    · rw [← hj]
      exact full_shell_compare (by omega) hi (front_dyadic hi)
        (hlarge.trans (by exact_mod_cast hmi.1)) (SquarefreeVaughanLogSource.length_pos u N)
        ((full_cutoff_geometry hu hN).trans (Nat.pow_le_pow_left hmi.1 3)) y
  rw [hj]
  have he := partition_sum F (front M X) (front_monotone M X) N
  rw [h0,hn] at he
  rw [← he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum hloc
  rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  exact hh.trans_eq (by dsimp [B]; ring)

/-- The actual completed squarefree coefficient. Its ordinary-prime
boundary is restored explicitly; it is not the original composite carrier. -/
def completedCoefficient (L : ℝ) (n : ℕ) : ℂ :=
  if Squarefree n then ((-log n*VaughanLogAverage.riesz L n/L : ℝ) : ℂ) else 0

/-- The full physical total-log window, without a prime-count crop. -/
def fullLabels (N : ℕ) : Finset ℕ :=
  Finset.Ioc (coreFloor N 0 (39/20)) (coreFloor N 0 (203/100))

/-- One completed squarefree bulk, with all counts and the complete phase. -/
def completedCore (u y : ℝ) (N : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∑ n∈fullLabels N,
    completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The counting error and the signed phase endpoint cost. Both have
genuine geometric rates; no positive `(2*u)^N` main allowance remains. -/
def bulkBudget (u y : ℝ) (N : ℕ) : ℝ :=
  7*ownerSamplingBudget u y N+
    2*u*ZetaRieszLongCutoffError.countingConstant*(4+|y|)*
      (N : ℝ)*((N : ℝ)+1)*exp (-(N : ℝ)/200)

private theorem length_ge_one (u : ℝ) (N : ℕ) : 1≤SquarefreeVaughanLogSource.length u N := by
  have hD := Nat.cast_nonneg (α:=ℝ) (ZetaVaughanCutoffBudget.linearDampedCutoff u N)
  have hh : (2 : ℝ)^2≤(ZetaVaughanCutoffBudget.linearDampedCutoff u N+2 : ℝ)^2 := by nlinarith
  have hl := log_le_log (by norm_num : (0 : ℝ)<2^2) hh
  rw [log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have htwo := log_two_gt_d9
  norm_num at htwo
  unfold SquarefreeVaughanLogSource.length
  linarith only [hl,htwo]

private theorem completed_atom_re (u y L : ℝ) (N : ℕ) {n : ℕ} (hn : 0<n) :
    ((u : ℂ)^(N+1)*completedCoefficient L n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re=
      -(u^(N+1)/L)*(if Squarefree n then radial N (log n)*cos (y*log n)/(n : ℝ)*
        VaughanLogAverage.riesz L n else 0) := by
  by_cases hs : Squarefree n
  · have hk := ZetaRieszCosineCarrier.re_filterKernel_one N y n
    have hk' : (zetaPrimeLogKernel N (3/2+Complex.I*y) n).re=
        exp (-(3/2 : ℝ)*log n)*log n^N/N.factorial*cos (y*log n) := by
      simpa only [zetaPrimeFilterKernel,ZetaRieszCosineCarrier.factorialPolynomial_one,
        zetaPrimeLogKernel,zetaPrimeFeature,neg_mul] using hk
    have he : exp (-(3/2 : ℝ)*log n)=exp (-log n/2)/(n : ℝ) := by
      rw [show -(3/2 : ℝ)*log n=-log n/2+-log n by ring,exp_add,exp_neg,
        exp_log (by exact_mod_cast hn)]
      ring
    simp only [completedCoefficient,if_pos hs,← Complex.ofReal_pow,← Complex.ofReal_mul,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [hk',he]
    unfold radial
    rw [pow_succ]
    ring
  · simp [completedCoefficient,hs]

private theorem completedCore_re (N : ℕ) (u y : ℝ) :
    (completedCore u y N).re=
      -(u^(N+1)/SquarefreeVaughanLogSource.length u N)*
        ∑ n∈fullLabels N,if Squarefree n then
          radial N (log n)*cos (y*log n)/(n : ℝ)*
            VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) n else 0 := by
  unfold completedCore
  rw [Finset.mul_sum,Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hpos : 0<n := by
    have hh := (Finset.mem_Ioc.mp hn).1
    omega
  simpa only [mul_assoc] using completed_atom_re u y _ N hpos

/-- A genuine signed estimate for the WHOLE completed squarefree bulk.
It is independent of zeros and includes every ordinary-prime boundary.
It does not apply to a count/owner/physical-masked subpopulation. -/
theorem completedCore_real_bound {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    {N : ℕ} (hN : 64≤N) : |(completedCore u y N).re|≤bulkBudget u y N := by
  let L := SquarefreeVaughanLogSource.length u N
  let raw := ∑ n∈fullLabels N,if Squarefree n then radial N (log n)*cos (y*log n)/(n : ℝ)*
    VaughanLogAverage.riesz L n else 0
  let plain := ∑ n∈fullLabels N,radial N (log n)*cos (y*log n)/(n : ℝ)
  have hu0 : 0≤u := by linarith
  have hL : 0<L := SquarefreeVaughanLogSource.length_pos u N
  have hL1 : 1≤L := length_ge_one u N
  have herr := full_core_compare hu hN y
  have hp := full_lattice_phase_bound hN hu0 hU hy
  have hd := ZetaRieszSignedDensityMain.densityRiesz_bound L
  have hs : 0≤u^(N+1)/L := by positivity
  have hmain : u^(N+1)/L*|ZetaRieszSignedDensityMain.densityRiesz L*plain|≤
      7*ownerSamplingBudget u y N := by
    rw [abs_mul]
    have hdin : |ZetaRieszSignedDensityMain.densityRiesz L|/L≤7 := by
      apply (div_le_iff₀ hL).mpr
      linarith only [hd,hL1]
    calc
      _ = (|ZetaRieszSignedDensityMain.densityRiesz L|/L)*|u^(N+1)*plain| := by
        rw [abs_mul,abs_of_nonneg (pow_nonneg hu0 _)]
        ring
      _ ≤ 7*ownerSamplingBudget u y N :=
        (mul_le_mul_of_nonneg_right hdin (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hp (by norm_num))
  have he : u^(N+1)/L*|raw-ZetaRieszSignedDensityMain.densityRiesz L*plain|≤
      2*u*ZetaRieszLongCutoffError.countingConstant*(4+|y|)*
        (N : ℝ)*((N : ℝ)+1)*exp (-(N : ℝ)/200) := by
    have hh := mul_le_mul_of_nonneg_left herr hs
    have hb := mul_le_mul_of_nonneg_left (ZetaRieszLongCutoffError.source_rate_bound hu0 hU N)
      (show 0≤2*u*ZetaRieszLongCutoffError.countingConstant*(4+|y|)*
        (N : ℝ)*((N : ℝ)+1) by positivity [ZetaRieszLongCutoffError.countingConstant_pos])
    apply hh.trans
    convert hb using 1
    · simp only [radialCap,mul_pow,pow_succ]
      change u^N*u/L*((N : ℝ)*ZetaRieszLongCutoffError.countingConstant*
        exp (-(N : ℝ)/128)*((4+|y|)*(((N : ℝ)+1)*(2^N*2)))*L) = _
      field_simp [hL.ne']
    · congr 1
      ring
  rw [completedCore_re N,abs_mul,abs_neg,abs_of_nonneg hs]
  have hh : |raw|≤|raw-ZetaRieszSignedDensityMain.densityRiesz L*plain|+
      |ZetaRieszSignedDensityMain.densityRiesz L*plain| := by
    simpa only [sub_add_cancel] using abs_add_le (raw-ZetaRieszSignedDensityMain.densityRiesz L*plain)
      (ZetaRieszSignedDensityMain.densityRiesz L*plain)
  apply (mul_le_mul_of_nonneg_left hh hs).trans
  rw [mul_add]
  exact (add_le_add he hmain).trans_eq (by unfold bulkBudget; ring)

theorem bulkBudget_tendsto (u y : ℝ) : Tendsto (bulkBudget u y) atTop (𝓝 0) := by
  have h0 : 0<exp (-(1/200 : ℝ)) := exp_pos _
  have h1 : exp (-(1/200 : ℝ))<1 := exp_lt_one_iff.mpr (by norm_num)
  have hs := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 h0 h1
  have hq := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2 h0 h1
  have ht := ((ownerSamplingBudget_tendsto u y).const_mul 7).add
    ((hq.sub hs).const_mul (2*u*ZetaRieszLongCutoffError.countingConstant*(4+|y|)))
  simp only [mul_zero,sub_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [] with N
  simp only [pow_one,← exp_nat_mul]
  unfold bulkBudget
  ring

/-- Independent cofinal decay of the real signed completed bulk. The
restored prime and rejected-label completion boundaries are still unpaid. -/
theorem tendsto_completedCore_re {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    Tendsto (fun N => (completedCore u y N).re) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (bulkBudget_tendsto u y)
  filter_upwards [eventually_ge_atTop (64 : ℕ)] with N hN
  simpa only [Real.norm_eq_abs] using completedCore_real_bound hu hU hy hN

end RiemannGaussian.ZetaRieszGlobalBulkPayment

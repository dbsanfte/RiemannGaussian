/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszUnallocatedOwnerPhase
import RiemannGaussian.ZetaRieszGlobalPeriodEdgePayment

/-!
# All-count unallocated high-owner cancellation

Join the original unallocated composite owner row with its exact,
unallocated ordinary-prime cofactor correction. Squarefree counting and
the complete signed physical phase pay the joined sum at a geometric
rate. The correction is not the old allocated/sieved head and is never
dropped. No independent whole-carrier floor follows from this payment.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology MeasureTheory
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszUnallocatedOwnerPayment
open ZetaRieszOwnerMaximal ZetaRieszSmoothOwnerDiscrepancy
open ZetaRieszOwnerLatticePhase ZetaRieszOwnerPhasePrimitive
open ZetaRieszCofactorDiscrepancy ZetaRieszCofactorPhaseEnergy

open ZetaRieszUnallocatedOwnerPhase
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
    (hMX : M<X) (hXM : X≤2*M) (N : ℕ) {c : ℝ} (hc : 0≤c) :
    (∑ k∈Finset.Ico (M+1) X,
      |radial N (c+log k)-radial N (c+log (k+1 : ℕ))|)≤radialCap N := by
  let m := X-(M+1)
  let v := fun i : ℕ => c+log (M+1+i : ℕ)
  have hv i : 0≤v i := add_nonneg hc (log_natCast_nonneg _)
  have hvi i : v i≤v (i+1) := by
    have hlog : log (M+1+i : ℕ)≤log (M+1+(i+1) : ℕ) :=
      log_le_log (by positivity)
        (by exact_mod_cast (show M+1+i≤M+1+(i+1) by omega))
    simpa only [v,add_comm] using add_le_add_left hlog c
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
    (hXM : X≤2*M) (hlarge : exp ((N : ℝ)/2)≤M) {c L : ℝ} (hc : 0≤c) (hL : 0<L)
    (hcut : ⌊exp L⌋₊^4≤M^3) (y : ℝ) :
    |(∑ n∈Finset.Ioc M X,if Squarefree n then
        radial N (c+log n)*cos (y*(c+log n))/(n : ℝ)*VaughanLogAverage.riesz L n else 0)-
      ZetaRieszSignedDensityMain.densityRiesz L*
        (∑ n∈Finset.Ioc M X,radial N (c+log n)*cos (y*(c+log n))/(n : ℝ))|≤
      ZetaRieszLongCutoffError.countingConstant*exp (-(N : ℝ)/128)*
        ((4+|y|)*radialCap N)*L := by
  let R := ⌊exp L⌋₊
  let f := fun d : ℕ => max 0 (L-log d)
  let w := shellWeight M X (fun n => radial N (c+log n)) y c
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
    have hh := shellWeight_variation hM hMX hXM (fun n => radial N (c+log n)) y c
      (radialCap N) (radialCap_nonneg N) (fun n _ => by
        rw [abs_of_nonneg (radial_bounds N (add_nonneg hc (log_natCast_nonneg n))).1]
        exact (radial_bounds N (add_nonneg hc (log_natCast_nonneg n))).2)
    exact hh.trans (by
      have h := radial_amplitude_variation hM hMX hXM N hc
      linarith only [h])
  have hs (g : ℕ→ℝ) : (∑ n∈Finset.Icc 1 X,w n*g n)=
      ∑ n∈Finset.Ioc M X,radial N (c+log n)*cos (y*(c+log n))/(n : ℝ)*g n := by
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
    simp only [w,shellWeight,Finset.mem_Ioc.mp hn,and_self,ite_true]
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

private theorem core_cover {N : ℕ} (hN : 64≤N) {c : ℝ} (hc : c≤(7/5 : ℝ)*N) :
    coreFloor N c (203/100)≤2^N*coreFloor N c (39/20) := by
  have hwide := (densityFloor_geometry hN hc).2.2.2.1
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

private theorem full_core_compare {N : ℕ} (hN : 64≤N) {c L : ℝ}
    (hc : 0≤c) (hcN : c≤(7/5 : ℝ)*N) (hL : 0<L)
    (hcut : ⌊exp L⌋₊^4≤(coreFloor N c (39/20))^3) (y : ℝ) :
    |(∑ n∈Finset.Ioc (coreFloor N c (39/20)) (coreFloor N c (203/100)),
        if Squarefree n then radial N (c+log n)*cos (y*(c+log n))/(n : ℝ)*
          VaughanLogAverage.riesz L n else 0)-
      ZetaRieszSignedDensityMain.densityRiesz L*
        (∑ n∈Finset.Ioc (coreFloor N c (39/20)) (coreFloor N c (203/100)),
          radial N (c+log n)*cos (y*(c+log n))/(n : ℝ))|≤
      (N : ℝ)*ZetaRieszLongCutoffError.countingConstant*exp (-(N : ℝ)/128)*
        ((4+|y|)*radialCap N)*L := by
  let M := coreFloor N c (39/20)
  let X := coreFloor N c (203/100)
  obtain ⟨hM,hMX,hlarge,_hwide,_hlo,_hhi⟩ := densityFloor_geometry hN hcN
  change 1≤M at hM
  change M≤X at hMX
  have h0 : front M X 0=M := by simp [front,min_eq_right hMX]
  have hn : front M X N=X := min_eq_left (core_cover hN hcN)
  let B := ZetaRieszLongCutoffError.countingConstant*exp (-(N : ℝ)/128)*
    ((4+|y|)*radialCap N)*L
  have hB : 0≤B := by dsimp [B]; positivity [ZetaRieszLongCutoffError.countingConstant_pos,
    hL,radialCap_nonneg N]
  let F := fun n : ℕ => (if Squarefree n then radial N (c+log n)*cos (y*(c+log n))/(n : ℝ)*
    VaughanLogAverage.riesz L n else 0)-
      ZetaRieszSignedDensityMain.densityRiesz L*(radial N (c+log n)*cos (y*(c+log n))/(n : ℝ))
  have hj (m x : ℕ) : (∑ n∈Finset.Ioc m x,if Squarefree n then
      radial N (c+log n)*cos (y*(c+log n))/(n : ℝ)*VaughanLogAverage.riesz L n else 0)-
      ZetaRieszSignedDensityMain.densityRiesz L*
        (∑ n∈Finset.Ioc m x,radial N (c+log n)*cos (y*(c+log n))/(n : ℝ))=
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
        (hlarge.trans (by exact_mod_cast hmi.1)) hc hL
        (hcut.trans (Nat.pow_le_pow_left hmi.1 3)) y
  rw [hj]
  have he := partition_sum F (front M X) (front_monotone M X) N
  rw [h0,hn] at he
  rw [← he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum hloc
  rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  exact hh.trans_eq (by dsimp [B]; ring)

private theorem length_ge_one (u : ℝ) (N : ℕ) :
    1≤SquarefreeVaughanLogSource.length u N := by
  have hD := Nat.cast_nonneg (α:=ℝ) (ZetaVaughanCutoffBudget.linearDampedCutoff u N)
  have hh : (2 : ℝ)^2≤(ZetaVaughanCutoffBudget.linearDampedCutoff u N+2 : ℝ)^2 := by nlinarith
  have hl := log_le_log (by norm_num : (0 : ℝ)<2^2) hh
  rw [log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have htwo := log_two_gt_d9
  norm_num at htwo
  unfold SquarefreeVaughanLogSource.length
  linarith only [hl,htwo]

/-- The actual translated divisor cutoff is inside the squarefree
counting range for EVERY unallocated high owner, including owners beyond
old allocated support. -/
theorem translated_cutoff_geometry {u : ℝ} (hu : 1/2≤u) {N : ℕ}
    (hN : 64≤N) {c : ℝ} (hc : (51/50 : ℝ)*N≤c)
    (hcL : c≤SquarefreeVaughanLogSource.length u N) :
    ⌊exp (SquarefreeVaughanLogSource.length u N-c)⌋₊^4≤
      (coreFloor N c (39/20))^3 := by
  let L := SquarefreeVaughanLogSource.length u N
  have hLhi := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
  have hcN : c≤(7/5 : ℝ)*N := by
    nlinarith only [hcL,hLhi,Nat.cast_nonneg (α:=ℝ) N]
  obtain ⟨hM,_hMX,_hlarge,_hwide,hlo,_hhi⟩ := densityFloor_geometry hN hcN
  let M := coreFloor N c (39/20)
  have hm : (1 : ℝ)≤M := by exact_mod_cast hM
  have hm0 : (0 : ℝ)<M := by linarith only [hm]
  have hi : 1/(M : ℝ)≤1 := (div_le_one hm0).mpr hm
  have hl : (39/20 : ℝ)*N-c-1≤log M := by
    have h := (abs_le.mp hlo).1
    linarith only [h,hi]
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hg : 4*(L-c)≤3*log M := by
    dsimp [L]
    linarith only [hLhi,hc,hl,hn]
  have hr : (⌊exp (L-c)⌋₊ : ℝ)≤exp (L-c) := Nat.floor_le (exp_pos _).le
  have hp : (⌊exp (L-c)⌋₊ : ℝ)^4≤(M : ℝ)^3 := by
    calc
      _ ≤ exp (L-c)^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hr _
      _ = exp (4*(L-c)) := by rw [← exp_nat_mul]; norm_num
      _ ≤ exp (3*log M) := exp_le_exp.mpr hg
      _ = (M : ℝ)^3 := by
        change exp (((3 : ℕ) : ℝ)*log M)=(M : ℝ)^3
        rw [exp_nat_mul,exp_log hm0]
  exact_mod_cast hp

/-- Source-normalized full physical owner row. ALL squarefree cofactor
counts are retained; its prime part is an exact completion correction. -/
def joinedOwner (u y : ℝ) (N p : ℕ) : ℝ :=
  let L := SquarefreeVaughanLogSource.length u N
  u^(N+1)/(L*p)*∑ a∈Finset.Ioc (coreFloor N (log p) (39/20))
    (coreFloor N (log p) (203/100)),
    if Squarefree a then densityTest N (log p) y a*VaughanLogAverage.riesz (L-log p) a else 0

/-- The old coefficient/phase is kept, WITHOUT the allocated owner weight
or the small-prime sieve. The correction is never identified with the
original allocated head. -/
def compositeRow (u y : ℝ) (N p : ℕ) : ℝ :=
  let L := SquarefreeVaughanLogSource.length u N
  u^(N+1)/(L*p)*∑ a∈Finset.Ioc (coreFloor N (log p) (39/20))
    (coreFloor N (log p) (203/100)),
    if Squarefree a ∧ ¬a.Prime then
      densityTest N (log p) y a*VaughanLogAverage.riesz (L-log p) a else 0

/-- Literal UNALLOCATED prime-cofactor correction, including the extended
owner interval and the full original total-log window. -/
def primeCorrection (u y : ℝ) (N p : ℕ) : ℝ :=
  let L := SquarefreeVaughanLogSource.length u N
  u^(N+1)/(L*p)*(L-log p)*∑ q∈Finset.Ioc (coreFloor N (log p) (39/20))
    (coreFloor N (log p) (203/100)), if q.Prime then densityTest N (log p) y q else 0

/-- One common geometric budget for the joined raw row. -/
def ownerBudget (u y : ℝ) (N : ℕ) : ℝ :=
  7*ownerSamplingBudget u y N+
    2*u*ZetaRieszLongCutoffError.countingConstant*(4+|y|)*
      (N : ℝ)*((N : ℝ)+1)*exp (-(N : ℝ)/200)

/-- INDEPENDENT signed payment, including all cofactor counts and the
exact prime correction. No bound on either part separately is asserted. -/
theorem joinedOwner_bound {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    {N p : ℕ} (hN : 64≤N) (hp : p.Prime)
    (hc : (51/50 : ℝ)*N≤log p)
    (hpL : log p≤SquarefreeVaughanLogSource.length u N) :
    |joinedOwner u y N p|≤ownerBudget u y N/(p : ℝ) := by
  let L := SquarefreeVaughanLogSource.length u N
  let b := L-log p
  let raw := ∑ a∈Finset.Ioc (coreFloor N (log p) (39/20))
    (coreFloor N (log p) (203/100)),
    if Squarefree a then densityTest N (log p) y a*VaughanLogAverage.riesz b a else 0
  let plain := ∑ a∈Finset.Ioc (coreFloor N (log p) (39/20))
    (coreFloor N (log p) (203/100)),densityTest N (log p) y a
  have hu0 : 0≤u := by linarith only [hu]
  have hL : 0<L := SquarefreeVaughanLogSource.length_pos u N
  have hL1 : 1≤L := length_ge_one u N
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hc0 := log_natCast_nonneg p
  have hcN : log p≤(7/5 : ℝ)*N := by
    have hhi := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
    nlinarith only [hpL,hhi,Nat.cast_nonneg (α:=ℝ) N]
  have hp' := normalized_density_core_bound hN hc0 hcN hy hu0 hU
  have hplain : |u^(N+1)*plain|≤ownerSamplingBudget u y N := hp'
  have hsw a (ha : a∈Finset.Ioc (coreFloor N (log p) (39/20))
      (coreFloor N (log p) (203/100))) :
      densityTest N (log p) y a=
        radial N (log p+log a)*cos (y*(log p+log a))/(a : ℝ) := by
    apply densityTest_eq
    have ham : 1≤a := by have := (Finset.mem_Ioc.mp ha).1; omega
    have hn : (64 : ℝ)≤N := by exact_mod_cast hN
    have hap := log_natCast_nonneg a
    linarith only [hc,hn,hap]
  have hraw : raw=∑ a∈Finset.Ioc (coreFloor N (log p) (39/20))
      (coreFloor N (log p) (203/100)),
      if Squarefree a then radial N (log p+log a)*cos (y*(log p+log a))/(a : ℝ)*
        VaughanLogAverage.riesz b a else 0 := by
    dsimp [raw]
    exact Finset.sum_congr rfl (fun a ha => by rw [hsw a ha])
  by_cases hb : 0<b
  · have herr := full_core_compare hN hc0 hcN hb (translated_cutoff_geometry hu hN hc hpL) y
    have hplain' : plain=∑ a∈Finset.Ioc (coreFloor N (log p) (39/20))
        (coreFloor N (log p) (203/100)),
        radial N (log p+log a)*cos (y*(log p+log a))/(a : ℝ) :=
      Finset.sum_congr rfl hsw
    rw [← hraw,← hplain'] at herr
    have hd := ZetaRieszSignedDensityMain.densityRiesz_bound b
    have hs : 0≤u^(N+1)/(L*p) := by positivity
    have hmain : u^(N+1)/(L*p)*|ZetaRieszSignedDensityMain.densityRiesz b*plain|≤
        (7/(p : ℝ))*ownerSamplingBudget u y N := by
      rw [abs_mul]
      have hdin : |ZetaRieszSignedDensityMain.densityRiesz b|/L≤7 := by
        apply (div_le_iff₀ hL).mpr
        linarith only [hd,hL1]
      calc
        _ = (|ZetaRieszSignedDensityMain.densityRiesz b|/L)/(p : ℝ)*|u^(N+1)*plain| := by
          rw [abs_mul,abs_of_nonneg (pow_nonneg hu0 _)]
          ring
        _ ≤ _ := (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hdin hp0.le) (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hplain (by positivity))
    have he : u^(N+1)/(L*p)*|raw-ZetaRieszSignedDensityMain.densityRiesz b*plain|≤
        (2*u*ZetaRieszLongCutoffError.countingConstant*(4+|y|)*
          (N : ℝ)*((N : ℝ)+1)*exp (-(N : ℝ)/200))/(p : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left herr hs
      have hbL : b≤L := by dsimp [b]; linarith only [hc0]
      have herrL : u^(N+1)/(L*p)*(N*ZetaRieszLongCutoffError.countingConstant*
          exp (-(N : ℝ)/128)*((4+|y|)*radialCap N)*b)≤
        u^(N+1)/(L*p)*(N*ZetaRieszLongCutoffError.countingConstant*
          exp (-(N : ℝ)/128)*((4+|y|)*radialCap N)*L) := by
        gcongr
        positivity [ZetaRieszLongCutoffError.countingConstant_pos,radialCap_nonneg N]
      have hn := mul_le_mul_of_nonneg_left (ZetaRieszLongCutoffError.source_rate_bound hu0 hU N)
        (show 0≤(2*u*ZetaRieszLongCutoffError.countingConstant*(4+|y|)*
          (N : ℝ)*((N : ℝ)+1))/(p : ℝ) by
            positivity [ZetaRieszLongCutoffError.countingConstant_pos])
      apply (hh.trans herrL).trans
      convert hn using 1
      · simp only [radialCap,mul_pow,pow_succ]
        field_simp [hL.ne']
      · ring
    have ht : |raw|≤|raw-ZetaRieszSignedDensityMain.densityRiesz b*plain|+
        |ZetaRieszSignedDensityMain.densityRiesz b*plain| := by
      simpa only [sub_add_cancel] using abs_add_le
        (raw-ZetaRieszSignedDensityMain.densityRiesz b*plain)
        (ZetaRieszSignedDensityMain.densityRiesz b*plain)
    change |u^(N+1)/(L*p)*raw|≤_
    rw [abs_mul,abs_of_nonneg hs]
    apply (mul_le_mul_of_nonneg_left ht hs).trans
    rw [mul_add]
    exact (add_le_add he hmain).trans_eq (by unfold ownerBudget; ring)
  · have hb0 : b≤0 := le_of_not_gt hb
    have hz a : VaughanLogAverage.riesz b a=0 := by
      unfold VaughanLogAverage.riesz
      apply Finset.sum_eq_zero
      intro d _
      rw [max_eq_left (by linarith [log_natCast_nonneg d]),mul_zero]
    have hraw0 : raw=0 := by
      simp only [raw,hz,mul_zero,ite_self,Finset.sum_const_zero]
    change |u^(N+1)/(L*p)*raw|≤_
    rw [hraw0,mul_zero,abs_zero]
    unfold ownerBudget ownerSamplingBudget
    positivity [ZetaRieszLongCutoffError.countingConstant_pos]

private theorem prime_riesz_translated {u : ℝ} (hu : 1/2≤u) {N p q : ℕ}
    (hN : 64≤N) (hpL : log p≤SquarefreeVaughanLogSource.length u N)
    (hq : q∈Finset.Ioc (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)))
    (hqp : q.Prime) :
    VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N-log p) q=
      SquarefreeVaughanLogSource.length u N-log p := by
  have hw := (coreFloor_membership N (log p) hqp.pos).mp hq
  have hhi := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hcut : SquarefreeVaughanLogSource.length u N-log p-log q≤0 := by
    linarith only [hw.1,hhi,hN0]
  rw [VaughanLogAverage.riesz,hqp.sum_divisors]
  simp only [ArithmeticFunction.moebius_apply_one,Int.cast_one,Nat.cast_one,
    log_one,sub_zero,max_eq_right (sub_nonneg.mpr hpL),one_mul,
    ArithmeticFunction.moebius_apply_prime hqp,Int.cast_neg,
    max_eq_left hcut,mul_zero,zero_add]

/-- Exact all-count join BEFORE taking norms. The unallocated prime
correction has precisely the plus sign; it is not the original head. -/
theorem joinedOwner_eq_row_add_correction {u : ℝ} (hu : 1/2≤u)
    {N p : ℕ} (hN : 64≤N) (hpL : log p≤SquarefreeVaughanLogSource.length u N)
    (y : ℝ) :
    joinedOwner u y N p=compositeRow u y N p+primeCorrection u y N p := by
  let L := SquarefreeVaughanLogSource.length u N
  let b := L-log p
  let S := Finset.Ioc (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100))
  have he a (ha : a∈S) :
      (if Squarefree a then densityTest N (log p) y a*VaughanLogAverage.riesz b a else 0)=
      (if Squarefree a ∧ ¬a.Prime then densityTest N (log p) y a*VaughanLogAverage.riesz b a else 0)+
        b*(if a.Prime then densityTest N (log p) y a else 0) := by
    by_cases hap : a.Prime
    · have hr := prime_riesz_translated hu hN hpL ha hap
      rw [if_pos hap.squarefree,if_neg (by simp [hap]),if_pos hap,
        show VaughanLogAverage.riesz b a=b from hr]
      ring
    · simp [hap]
  have hs := Finset.sum_congr rfl he
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  unfold joinedOwner compositeRow primeCorrection
  dsimp only
  change u^(N+1)/(L*p)*(∑ a∈S,if Squarefree a then
    densityTest N (log p) y a*VaughanLogAverage.riesz b a else 0)=_
  rw [hs]
  ring

/-- The joined estimate pays the full raw composite row plus its SAME
unallocated correction, retaining every cofactor count and phase. -/
theorem compositeRow_add_correction_bound {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    {N p : ℕ} (hN : 64≤N) (hp : p.Prime)
    (hc : (51/50 : ℝ)*N≤log p)
    (hpL : log p≤SquarefreeVaughanLogSource.length u N) :
    |compositeRow u y N p+primeCorrection u y N p|≤ownerBudget u y N/(p : ℝ) := by
  rw [← joinedOwner_eq_row_add_correction hu hN hpL y]
  exact joinedOwner_bound hu hU hy hN hp hc hpL

/-- Harmonic owner aggregation after ALL cofactor counts/radial shells
have been joined. This bound has no zero or prime-density hypothesis. -/
theorem global_row_add_correction_bound (P : Finset ℕ) {u y : ℝ}
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    {N Q : ℕ} (hN : 64≤N)
    (hP : ∀ p∈P,p.Prime ∧ p≤Q ∧ (51/50 : ℝ)*N≤log p ∧
      log p≤SquarefreeVaughanLogSource.length u N)
    (hQ : log Q≤(7/5 : ℝ)*N) :
    |∑ p∈P,(compositeRow u y N p+primeCorrection u y N p)|≤
      (1+(7/5 : ℝ)*N)*ownerBudget u y N := by
  have hB : 0≤ownerBudget u y N := by
    unfold ownerBudget ownerSamplingBudget
    positivity [ZetaRieszLongCutoffError.countingConstant_pos]
  have hh : (∑ p∈P,(p : ℝ)⁻¹)≤1+(7/5 : ℝ)*N :=
    (marked_harmonic_bound P
      (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1⟩)).trans (by linarith only [hQ])
  calc
    _ ≤ ∑ p∈P,|compositeRow u y N p+primeCorrection u y N p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p∈P,ownerBudget u y N/(p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpp,_hpQ,hc,hpL⟩ := hP p hp
      exact compositeRow_add_correction_bound hu hU hy hN hpp hc hpL
    _ = ownerBudget u y N*(∑ p∈P,(p : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => div_eq_mul_inv _ _)
    _ ≤ _ := (mul_le_mul_of_nonneg_left hh hB).trans_eq (by ring)

/-- Even after summing EVERY owner, both rates remain geometric times a
fixed polynomial. This is a concrete all-count joined estimate, not a
numerical bound for the leftover prime-pair expression. -/
theorem globalBudget_tendsto (u y : ℝ) :
    Tendsto (fun N : ℕ => (1+(7/5 : ℝ)*N)*ownerBudget u y N) atTop (𝓝 0) := by
  have h0 : 0<exp (-(1/200 : ℝ)) := exp_pos _
  have h1 : exp (-(1/200 : ℝ))<1 := exp_lt_one_iff.mpr (by norm_num)
  have hs := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 h0 h1
  have hq := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2 h0 h1
  have hc := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3 h0 h1
  have hpoly := ((hc.const_mul (7/5 : ℝ)).sub (hq.const_mul (9/5 : ℝ))).add
    (hs.const_mul (2/5 : ℝ))
  have hm := (ownerSamplingBudget_polynomial_tendsto 1 u y).const_mul (49/5 : ℝ)
  have hz := ((ownerSamplingBudget_tendsto u y).const_mul (-14/5 : ℝ)).add hm
  have ht := hz.add (hpoly.const_mul (2*u*ZetaRieszLongCutoffError.countingConstant*(4+|y|)))
  simp only [mul_zero,sub_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [] with N
  simp only [pow_one,← exp_nat_mul]
  unfold ownerBudget
  ring

/-- Every genuine high owner through the ACTUAL moving length. No old
5N/4 owner cap or rough-prime sieve is inserted. -/
def highOwners (u : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊exp (SquarefreeVaughanLogSource.length u N)⌋₊).filter
    (fun p => p.Prime ∧ (51/50 : ℝ)*N≤log p)

theorem highOwner_data {u : ℝ} {N p : ℕ} (hp : p∈highOwners u N) :
    p.Prime ∧ p≤⌊exp (SquarefreeVaughanLogSource.length u N)⌋₊ ∧
      (51/50 : ℝ)*N≤log p ∧ log p≤SquarefreeVaughanLogSource.length u N := by
  obtain ⟨hi,hpp,hlo⟩ := Finset.mem_filter.mp hp
  have hpr : (0 : ℝ)<p := by exact_mod_cast hpp.pos
  have he := (show (p : ℝ)≤⌊exp (SquarefreeVaughanLogSource.length u N)⌋₊ by
    exact_mod_cast (Finset.mem_Icc.mp hi).2).trans (Nat.floor_le (exp_pos _).le)
  exact ⟨hpp,(Finset.mem_Icc.mp hi).2,hlo,by
    simpa only [log_exp] using log_le_log hpr he⟩

/-- The full unallocated ordinary-prime correction generated by the raw
high-owner completion. Keep it with the SAME original head afterwards. -/
def highPrimeCorrection (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ p∈highOwners u N,primeCorrection u y N p

/-- The literal raw composite population in its UNIQUE owner rows. -/
def highCompositeRows (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ p∈highOwners u N,compositeRow u y N p

/-- Independent geometric payment of ALL raw high-owner counts PLUS the
exact correction, on the literal wide window and moving length. -/
theorem highRows_add_correction_bound {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    {N : ℕ} (hN : 64≤N) :
    |highCompositeRows u y N+highPrimeCorrection u y N|≤
      (1+(7/5 : ℝ)*N)*ownerBudget u y N := by
  let Q := ⌊exp (SquarefreeVaughanLogSource.length u N)⌋₊
  have hQ0 : 0<Q := by
    have hL1 := length_ge_one u N
    have he : 1≤exp (SquarefreeVaughanLogSource.length u N) :=
      one_le_exp_iff.mpr (by linarith only [hL1])
    have hq : 1≤Q := (Nat.one_le_floor_iff _).mpr he
    omega
  have hQ : log Q≤(7/5 : ℝ)*N := by
    have hr : (0 : ℝ)<Q := by exact_mod_cast hQ0
    have hl := log_le_log hr (Nat.floor_le (exp_pos (SquarefreeVaughanLogSource.length u N)).le)
    rw [log_exp] at hl
    have hi := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
    nlinarith only [hl,hi,Nat.cast_nonneg (α:=ℝ) N]
  simpa only [highCompositeRows,highPrimeCorrection,Finset.sum_add_distrib] using
    global_row_add_correction_bound (highOwners u N) hu hU hy hN
      (fun _ hp => highOwner_data hp) hQ

/-- The all-count joined error really tends to zero on increasing orders;
no exposed-zero hypothesis is involved. -/
theorem tendsto_highRows_add_correction {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    Tendsto (fun N => highCompositeRows u y N+highPrimeCorrection u y N) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (globalBudget_tendsto u y)
  filter_upwards [eventually_ge_atTop (64 : ℕ)] with N hN
  simpa only [Real.norm_eq_abs] using highRows_add_correction_bound hu hU hy hN

theorem cofactor_window_data {u : ℝ} (hu : 1/2≤u) {N p a : ℕ}
    (hN : 64≤N) (hp : p∈highOwners u N)
    (hLlo : (51/50 : ℝ)*N≤SquarefreeVaughanLogSource.length u N)
    (ha : a∈Finset.Ioc (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100))) :
    1<a ∧ a<p ∧ log a≤SquarefreeVaughanLogSource.length u N := by
  obtain ⟨hpp,_hpQ,hc,hpL⟩ := highOwner_data hp
  have hcN : log p≤(7/5 : ℝ)*N := by
    have hh := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2≤N)
    nlinarith only [hh,hpL,Nat.cast_nonneg (α:=ℝ) N]
  have hM := (densityFloor_geometry hN hcN).1
  have ha1 : 1<a := by have := (Finset.mem_Ioc.mp ha).1; omega
  have ht := (coreFloor_membership N (log p) (by omega : 0<a)).mp ha
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hap : log a<log p := by linarith only [ht.2,hc,hn]
  have haL : log a≤SquarefreeVaughanLogSource.length u N := by
    linarith only [ht.2,hc,hLlo,hn]
  exact ⟨ha1,by exact_mod_cast (log_lt_log_iff
    (by exact_mod_cast (by omega : 0<a)) (by exact_mod_cast hpp.pos)).mp hap,haL⟩

/-- Exact squarefree-composite cofactor support; no count ceiling,
physical deletion or old owner allocation is imposed. -/
def rowCofactors (N p : ℕ) : Finset ℕ :=
  (Finset.Ioc (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100))).filter
    (fun a => Squarefree a ∧ ¬a.Prime)

/-- The full unallocated translated row is the ORIGINAL coefficient
atom, with its full physical product phase. This is not a density model. -/
theorem literal_composite_atom_re {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p a : ℕ} (hN : 65536≤N)
    (hp : p∈highOwners u N) (ha : a∈rowCofactors N p) (y : ℝ) :
    ((u : ℂ)^(N+1)*ZetaRieszGlobalBulkPayment.completedCoefficient
      (SquarefreeVaughanLogSource.length u N) (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re=
      u^(N+1)/(SquarefreeVaughanLogSource.length u N*p)*
        (densityTest N (log p) y a*
          VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N-log p) a) := by
  obtain ⟨haw,has,hap⟩ := Finset.mem_filter.mp ha
  obtain ⟨hpp,_hpQ,_hc,_hpL⟩ := highOwner_data hp
  have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0<u) hU
  have hLlo : (51/50 : ℝ)*N≤SquarefreeVaughanLogSource.length u N := by
    nlinarith only [hlo,Nat.cast_nonneg (α:=ℝ) N]
  obtain ⟨ha1,haplt,haL⟩ := cofactor_window_data hu (by omega) hp hLlo haw
  have hnot : ¬p∣a := fun hd => (Nat.le_of_dvd (by omega : 0<a) hd).not_gt haplt
  have hs : Squarefree (p*a) := Nat.squarefree_mul_iff.mpr
    ⟨hpp.coprime_iff_not_dvd.mpr hnot,hpp.squarefree,has⟩
  have hz := ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated has (by omega) hap haL
  have hr := ZetaSquarefreeRieszWindows.riesz_prime_mul
    (SquarefreeVaughanLogSource.length u N) hpp hnot
  rw [hz,zero_sub] at hr
  have hlog : log (p*a : ℕ)=log p+log a := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast has.ne_zero)]
  have hk := ZetaRieszCosineCarrier.re_filterKernel_one N y (p*a)
  have hk' : (zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re=
      exp (-(3/2 : ℝ)*log (p*a : ℕ))*log (p*a : ℕ)^N/N.factorial*
        cos (y*log (p*a : ℕ)) := by
    simpa only [zetaPrimeFilterKernel,ZetaRieszCosineCarrier.factorialPolynomial_one,
      zetaPrimeLogKernel,zetaPrimeFeature,neg_mul,Nat.cast_mul] using hk
  have he : exp (-(3/2 : ℝ)*log (p*a : ℕ))=
      exp (-log (p*a : ℕ)/2)/((p*a : ℕ) : ℝ) := by
    rw [show -(3/2 : ℝ)*log (p*a : ℕ)=-log (p*a : ℕ)/2+-log (p*a : ℕ) by ring,
      exp_add,exp_neg,exp_log (by exact_mod_cast Nat.mul_pos hpp.pos (by omega : 0<a))]
    ring
  have htest := densityTest_eq
    (N:=N) (c:=log p) (x:=(a : ℝ)) (by
      have hpl := log_natCast_nonneg p
      have hal : 0<log (a : ℝ) := log_pos (by exact_mod_cast ha1)
      linarith) y
  simp only [ZetaRieszGlobalBulkPayment.completedCoefficient,if_pos hs,
    ← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  rw [hr,hk',he,hlog,htest]
  simp only [Nat.cast_mul,radial,pow_succ]
  ring

/-- Exact connection of the ALL-count row to the actual unallocated
coefficient atoms. Every original factorial order and product phase stays. -/
theorem literal_row_eq {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p : ℕ} (hN : 65536≤N)
    (hp : p∈highOwners u N) (y : ℝ) :
    (∑ a∈rowCofactors N p,
      ((u : ℂ)^(N+1)*ZetaRieszGlobalBulkPayment.completedCoefficient
        (SquarefreeVaughanLogSource.length u N) (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re)=compositeRow u y N p := by
  rw [Finset.sum_congr rfl (fun a ha => literal_composite_atom_re hu hU hN hp ha y)]
  unfold compositeRow rowCofactors
  dsimp only
  rw [Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp only [mul_zero]

end RiemannGaussian.ZetaRieszUnallocatedOwnerPayment

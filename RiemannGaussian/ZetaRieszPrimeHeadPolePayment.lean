/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeHeadTransport
import RiemannGaussian.ZetaRieszShiftedCenter
import RiemannGaussian.ZetaRieszSkewFactorial
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Exponential arithmetic payment for pole removal on the actual prime head

Both original head primes are exponentially large. Hence the exact
per-leg shifted-center multiplier can be paid on EVERY factorial order,
including zero and one, at a geometric source-scale cost. This is a
difference payment, not a norm bound for the signed head or the joint main.
No complete-leg phase transfer through the hard masks is inferred.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPrimeHeadPolePayment
open ZetaRieszPrimeCountFrequency ZetaRieszPrimeHeadTransport
open ZetaRieszSmallTagNativeFloor (owners owners_data smallPrimes)
open ZetaRieszSmoothOwnerDiscrepancy (radial radial_bounds radialCap radialCap_nonneg ownerAmplitude)
open ZetaRieszOwnerMaximal (ownerWeight ownerWeight_bounds)
open ZetaRieszJointAllocation (mass mass_total mass_nonneg)
open ZetaRieszShiftedCenter (ratio)

/-- Original complementary head orders, retaining both boundary orders. -/
def keptOrders (N : ℕ) : Finset ℕ :=
  Finset.range (N+2)\ZetaRieszWingHighOrders.unpaidOrders N

theorem keptOrders_support {N k : ℕ} (hk : k∈keptOrders N) : k≤N+1 := by
  have h := Finset.mem_range.mp (Finset.mem_sdiff.mp hk).1
  omega

/-- No continuum or limiting allocation replaces this exact finite mass. -/
theorem sum_kept_mass (N : ℕ) (x : ℝ) :
    (∑ k∈keptOrders N,mass (N+1) k x)=ownerWeight N x := by
  have hs : ZetaRieszWingHighOrders.unpaidOrders N⊆Finset.range (N+2) := by
    intro k hk
    have h := (ZetaRieszWingHighOrders.unpaidOrders_support hk).1
    have hh := ZetaRieszReflectedCompletion.lowerWing_bounds h
    simp only [Finset.mem_range]
    omega
  have h := Finset.sum_sdiff hs (f:=fun k => mass (N+1) k x)
  rw [mass_total] at h
  unfold keptOrders ownerWeight
  linarith only [h]

/-- The physical lower cofactor endpoint gives an EXACT exponential
prime lower bound, not the much weaker separate polynomial sieve cutoff. -/
theorem head_prime_logs {u : ℝ} {N p q : ℕ} (hp : p∈owners u N)
    (hq : q∈pairInterval N p) :
    (51/50 : ℝ)*N≤log p ∧ (7/10 : ℝ)*N<log q := by
  have hd := owners_data hp
  have hlo := (Finset.mem_Ioc.mp hq).1
  have hf := Nat.lt_floor_add_one (exp ((39/20 : ℝ)*N-log p))
  have hqR : (ZetaRieszOwnerLatticePhase.coreFloor N (log p) (39/20) : ℝ)+1≤q := by
    exact_mod_cast (show ZetaRieszOwnerLatticePhase.coreFloor N (log p) (39/20)+1≤q by omega)
  have hq0 : (0 : ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have he : exp ((39/20 : ℝ)*N-log p)<q := hf.trans_le hqR
  have hl := log_lt_log (exp_pos _) he
  rw [log_exp] at hl
  exact ⟨hd.2.2.1,by linarith only [hl,hd.2.2.2]⟩

theorem owner_log_le_length {u : ℝ} {N p : ℕ} (hp : p∈owners u N) :
    log p≤SquarefreeVaughanLogSource.length u N := by
  have hd := owners_data hp
  have hx := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hd.2.1).2.2
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hd.1.pos
  have hr : (p : ℝ)<(ZetaVaughanCutoffBudget.linearDampedCutoff u N+2 : ℝ)^2 := by
    exact_mod_cast hx
  exact log_le_log hp0 hr.le

/-- The unweighted leg kernel is kept at order zero too. Multiplication
by k*u^k gives precisely the previously proved pole-killed leg. -/
def legKernel (y : ℝ) (k p : ℕ) : ℂ :=
  zetaPrimeLogKernel k (ZetaRieszShiftedCenter.center y) p-
    ratio y^k*zetaPrimeLogKernel k (ZetaRieszShiftedCenter.center y+1) p

theorem legKernel_eq_multiplier (y : ℝ) (k p : ℕ) (hp : 0<p) :
    legKernel y k p=(1-ratio y^k/(p : ℂ))*
      zetaPrimeLogKernel k (ZetaRieszShiftedCenter.center y) p := by
  rw [legKernel,ZetaRieszShiftedCenter.kernel_shift k p _ hp]
  ring

theorem logged_leg_eq (u y : ℝ) (k p : ℕ) :
    (k : ℂ)*(u : ℂ)^k*legKernel y k p=ZetaRieszShiftedCenter.leg u y k p := rfl

/-- Exact two-leg multiplier on the original correlated factorial slot. -/
def slotMultiplier (y : ℝ) (N k p q : ℕ) : ℂ :=
  (1-ratio y^(N+1-k)/(p : ℂ))*(1-ratio y^k/(q : ℂ))

/-- Every order, not only a good-order range, pays a fixed exponential
multiplier difference on the original literal head support. -/
theorem slotMultiplier_error {u y : ℝ} (hy : 54 < |y|) {N p q k : ℕ}
    (hN : 64≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p)
    (hk : k≤N+1) :
    ‖slotMultiplier y N k p q-1‖≤3*exp (-(2/3 : ℝ)*N) := by
  obtain ⟨hpl,hql⟩ := head_prime_logs hp hq
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hkp : ((N+1-k : ℕ) : ℝ)≤4*log p := by
    have hh : ((N+1-k : ℕ) : ℝ)≤(N : ℝ)+1 := by
      exact_mod_cast (show N+1-k≤N+1 by omega)
    linarith only [hh,hpl,hn]
  have hkq : (k : ℝ)≤4*log q := by
    have hh : (k : ℝ)≤(N : ℝ)+1 := by exact_mod_cast hk
    linarith only [hh,hql,hn]
  have hq0 : 0<q := by have := (Finset.mem_Ioc.mp hq).1; omega
  have hp0 := (owners_data hp).1.pos
  have he0 : 0≤exp (-(2/3 : ℝ)*N) := (exp_pos _).le
  have he1 : exp (-(2/3 : ℝ)*N)≤1 :=
    exp_le_one_iff.mpr (by nlinarith only [Nat.cast_nonneg (α:=ℝ) N])
  have ha : ‖ratio y^(N+1-k)/(p : ℂ)‖≤exp (-(2/3 : ℝ)*N) := by
    apply (ZetaRieszShiftedCenter.multiplier_error_le hy _ _ (by omega) hkp).trans
    apply exp_le_exp.mpr
    linarith only [hpl,hn]
  have hb : ‖ratio y^k/(q : ℂ)‖≤exp (-(2/3 : ℝ)*N) := by
    apply (ZetaRieszShiftedCenter.multiplier_error_le hy _ _ (by omega) hkq).trans
    apply exp_le_exp.mpr
    linarith only [hql,hn]
  have hid : slotMultiplier y N k p q-1=
    -(ratio y^(N+1-k)/(p : ℂ))-ratio y^k/(q : ℂ)+
      ratio y^(N+1-k)/(p : ℂ)*(ratio y^k/(q : ℂ)) := by
    unfold slotMultiplier
    ring
  rw [hid]
  have h := (norm_add_le
    (-(ratio y^(N+1-k)/(p : ℂ))-ratio y^k/(q : ℂ))
    (ratio y^(N+1-k)/(p : ℂ)*(ratio y^k/(q : ℂ)))).trans
    (add_le_add (norm_sub_le (-(ratio y^(N+1-k)/(p : ℂ))) (ratio y^k/(q : ℂ)))
      (le_refl ‖ratio y^(N+1-k)/(p : ℂ)*(ratio y^k/(q : ℂ))‖))
  rw [norm_neg,norm_mul] at h
  have hab := mul_le_mul ha hb (norm_nonneg _) he0
  have hh := mul_le_mul_of_nonneg_left he1 he0
  nlinarith only [h,ha,hb,hab,hh]

/-- The original complementary allocation, with the operator on each
actual prime leg before any mask or prime sum is projected. -/
def filteredMass (y : ℝ) (N p q : ℕ) : ℂ :=
  ∑ k∈keptOrders N,
    (mass (N+1) k (log q/(log p+log q)) : ℂ)*slotMultiplier y N k p q

/-- This is literally the product of the two shifted-center kernels.
The composite cofactor is never completed. -/
theorem filteredMass_kernel {p q : ℕ} (hp : 0<p) (hq : 0<q) (hpq : 1<p*q)
    (N : ℕ) (y : ℝ) :
    filteredMass y N p q*zetaPrimeLogKernel (N+1) (ZetaRieszShiftedCenter.center y) (p*q)=
      ∑ k∈keptOrders N,legKernel y k q*legKernel y (N+1-k) p := by
  have hl : log p+log q=log (p*q : ℕ) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hq.ne')]
  rw [filteredMass,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have h := ZetaRieszSkewAllocation.split_mass_kernel (N+1) k q p
    (keptOrders_support hk) hq hp (by simpa only [Nat.mul_comm] using hpq)
    (ZetaRieszShiftedCenter.center y)
  rw [Nat.mul_comm q p,← hl] at h
  rw [legKernel_eq_multiplier y k q hq,legKernel_eq_multiplier y (N+1-k) p hp]
  calc
    _ = slotMultiplier y N k p q*
      ((mass (N+1) k (log q/(log p+log q)) : ℂ)*
        zetaPrimeLogKernel (N+1) (ZetaRieszShiftedCenter.center y) (p*q)) := by ring
    _ = _ := by rw [h]; unfold slotMultiplier; ring

/-- The exact owner allocation remains on the error. No small-order
mass or positive factorial slot is removed. -/
theorem filteredMass_error {u y : ℝ} (hy : 54 < |y|) {N p q : ℕ}
    (hN : 64≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p) :
    ‖filteredMass y N p q-(ownerWeight N (log q/(log p+log q)) : ℂ)‖≤
      3*exp (-(2/3 : ℝ)*N)*ownerWeight N (log q/(log p+log q)) := by
  obtain ⟨hpl,hql⟩ := head_prime_logs hp hq
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hx : 0≤log q/(log p+log q) := div_nonneg (by linarith) (by linarith)
  have hx1 : log q/(log p+log q)≤1 :=
    (div_le_one (by linarith : 0<log p+log q)).mpr (by linarith)
  rw [← sum_kept_mass,Complex.ofReal_sum,filteredMass,← Finset.sum_sub_distrib]
  have h := norm_sum_le (keptOrders N)
    (fun k => (mass (N+1) k (log q/(log p+log q)) : ℂ)*slotMultiplier y N k p q-
      (mass (N+1) k (log q/(log p+log q)) : ℂ))
  apply h.trans
  calc
    _ ≤ ∑ k∈keptOrders N,
      mass (N+1) k (log q/(log p+log q))*(3*exp (-(2/3 : ℝ)*N)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [show (mass (N+1) k (log q/(log p+log q)) : ℂ)*slotMultiplier y N k p q-
        (mass (N+1) k (log q/(log p+log q)) : ℂ)=
          (mass (N+1) k (log q/(log p+log q)) : ℂ)*(slotMultiplier y N k p q-1) by ring,
        norm_mul,Complex.norm_real,Real.norm_of_nonneg (mass_nonneg _ _ hx hx1)]
      exact mul_le_mul_of_nonneg_left
        (slotMultiplier_error hy hN hp hq (keptOrders_support hk)) (mass_nonneg _ _ hx hx1)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The literal real head amplitude BEFORE its factorial allocation.
The ordinary-prime and polynomial sieve masks remain exact. -/
def rawAmount (u : ℝ) (N p q : ℕ) : ℝ :=
  let L := SquarefreeVaughanLogSource.length u N
  u^(N+1)*(L-log p)/(L*p)*
    (if q.Prime then radial N (log p+log q)/(q : ℝ)*
      ZetaRieszUnsignedDivisorError.sieve (smallPrimes N) q else 0)

/-- Full original product phase, not a frozen or separate prime phase. -/
def character (y : ℝ) (p q : ℕ) : ℂ :=
  Complex.exp (Complex.I*((-(y*(log (p : ℝ)+log (q : ℝ))) : ℝ) : ℂ))

theorem character_re (y : ℝ) (p q : ℕ) :
    (character y p q).re=cos (y*(log p+log q)) := by
  have hr : (Complex.I*((-(y*(log (p : ℝ)+log (q : ℝ))) : ℝ) : ℂ)).re=0 := by
    simp only [Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,mul_zero,sub_self]
  have hi : (Complex.I*((-(y*(log (p : ℝ)+log (q : ℝ))) : ℝ) : ℂ)).im=
      -(y*(log p+log q)) := by
    simp only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,one_mul,mul_zero,zero_add]
  rw [character,Complex.exp_re,hr,hi,exp_zero,one_mul,cos_neg]

theorem norm_character (y : ℝ) (p q : ℕ) : ‖character y p q‖=1 := by
  have hr : (Complex.I*((-(y*(log (p : ℝ)+log (q : ℝ))) : ℝ) : ℂ)).re=0 := by
    simp only [Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,mul_zero,sub_self]
  rw [character,Complex.norm_exp,hr,exp_zero]

/-- The SAME original head atom in complex form. -/
def originalPair (u y : ℝ) (N p q : ℕ) : ℂ :=
  (rawAmount u N p q : ℂ)*character y p q*
    (ownerWeight N (log q/(log p+log q)) : ℂ)

/-- Apply the pole killer to each actual prime leg, before the original
correlated factorial orders and hard support are summed. -/
def filteredPair (u y : ℝ) (N p q : ℕ) : ℂ :=
  (rawAmount u N p q : ℂ)*character y p q*filteredMass y N p q

theorem originalPair_re (u y : ℝ) (N p q : ℕ) :
    (originalPair u y N p q).re=pairAmount u y N p q := by
  simp only [originalPair,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,zero_mul,sub_zero,character_re,rawAmount,pairAmount]
  rw [ZetaRieszOwnerLatticePhase.ownerTest_nat]
  unfold ownerAmplitude
  split_ifs <;> ring

private theorem sieve_bounds (S : Finset ℕ) (q : ℕ) :
    0≤ZetaRieszUnsignedDivisorError.sieve S q ∧
      ZetaRieszUnsignedDivisorError.sieve S q≤1 := by
  unfold ZetaRieszUnsignedDivisorError.sieve
  split_ifs <;> norm_num

/-- The positive envelope is used ONLY on the exponentially small
arithmetic operator difference, never as a bound for the signed head. -/
theorem rawAmount_bounds {u : ℝ} (hu : 0≤u) {N p q : ℕ}
    (hN : 64≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p)
    (hpL : log p≤SquarefreeVaughanLogSource.length u N) :
    0≤rawAmount u N p q ∧
      rawAmount u N p q≤u^(N+1)*radialCap N/(p : ℝ)/(q : ℝ) := by
  obtain ⟨hpl,hql⟩ := head_prime_logs hp hq
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hp0 : (0 : ℝ)<p := by exact_mod_cast (owners_data hp).1.pos
  have hq0 : (0 : ℝ)<q := by
    have hh := (Finset.mem_Ioc.mp hq).1
    exact_mod_cast (show 0<q by omega)
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have ht : 0≤log p+log q := by linarith only [hpl,hql,hn]
  obtain ⟨hr0,hr1⟩ := radial_bounds N ht
  obtain ⟨hs0,hs1⟩ := sieve_bounds (smallPrimes N) q
  have hf0 : 0≤(SquarefreeVaughanLogSource.length u N-log p)/
      SquarefreeVaughanLogSource.length u N := div_nonneg (sub_nonneg.mpr hpL) hL.le
  have hf1 : (SquarefreeVaughanLogSource.length u N-log p)/
      SquarefreeVaughanLogSource.length u N≤1 :=
    (div_le_one hL).mpr (by linarith only [hpl,hn])
  have hf := mul_le_of_le_one_left hr0 hf1
  have hr := mul_le_of_le_one_right hr0 hs1
  have hmain : ((SquarefreeVaughanLogSource.length u N-log p)/
      SquarefreeVaughanLogSource.length u N)*
      (radial N (log p+log q)*ZetaRieszUnsignedDivisorError.sieve (smallPrimes N) q)≤
      radialCap N := by
    exact (mul_le_mul_of_nonneg_left hr hf0).trans
      ((mul_le_of_le_one_left hr0 hf1).trans hr1)
  unfold rawAmount
  dsimp only
  split_ifs
  · constructor
    · positivity
    · have hh := mul_le_mul_of_nonneg_left hmain
        (show 0≤u^(N+1)/(p : ℝ)/(q : ℝ) by positivity)
      convert hh using 1 <;> first | rfl |
        (simp only [div_eq_mul_inv,mul_inv_rev]; ring)
  · simp only [mul_zero]
    exact ⟨le_refl 0,div_nonneg (div_nonneg
      (mul_nonneg (pow_nonneg hu _) (radialCap_nonneg N)) hp0.le) hq0.le⟩

theorem originalPair_norm {u : ℝ} {N p q : ℕ} (hN : 64≤N)
    (hp : p∈owners u N) (hq : q∈pairInterval N p) (y : ℝ) :
    ‖originalPair u y N p q‖=
      |rawAmount u N p q| * ownerWeight N (log q/(log p+log q)) := by
  obtain ⟨hpl,hql⟩ := head_prime_logs hp hq
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have hx0 : 0≤log q/(log p+log q) := div_nonneg (by linarith) (by linarith)
  have hx1 : log q/(log p+log q)≤1 :=
    (div_le_one (by linarith : 0<log p+log q)).mpr (by linarith)
  rw [originalPair,norm_mul,norm_mul,norm_character,mul_one,
    Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,
    Real.norm_of_nonneg (ownerWeight_bounds N hx0 hx1).1]

/-- Source-scale per-pair error with EVERY original allocation slot. -/
theorem filteredPair_error {u y : ℝ} (hy : 54 < |y|) {N p q : ℕ}
    (hN : 64≤N) (hp : p∈owners u N) (hq : q∈pairInterval N p) :
    ‖filteredPair u y N p q-originalPair u y N p q‖≤
      3*exp (-(2/3 : ℝ)*N)*‖originalPair u y N p q‖ := by
  rw [show filteredPair u y N p q-originalPair u y N p q=
    ((rawAmount u N p q : ℂ)*character y p q)*
      (filteredMass y N p q-(ownerWeight N (log q/(log p+log q)) : ℂ)) by
        unfold filteredPair originalPair; ring,
    norm_mul,norm_mul,norm_character,mul_one,Complex.norm_real,Real.norm_eq_abs,
    originalPair_norm hN hp hq y]
  exact (mul_le_mul_of_nonneg_left (filteredMass_error hy hN hp hq)
    (abs_nonneg _)).trans_eq (by ring)

/-- The exact original signed head; its real part is nativeHead. -/
def originalHead (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ p∈owners u N,∑ q∈pairInterval N p,originalPair u y N p q

/-- The per-leg operator on the SAME pairs and orders. No completion. -/
def filteredHead (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ p∈owners u N,∑ q∈pairInterval N p,filteredPair u y N p q

theorem originalHead_re (u y : ℝ) (N : ℕ) :
    (originalHead u y N).re=ZetaRieszRoughPrimePairCancellation.nativeHead u y N := by
  simp only [originalHead,Complex.re_sum,originalPair_re,
    nativeHead_eq_sum_pairAmount]

private theorem inverse_sum_bound (A : Finset ℕ) {X : ℕ}
    (hA : ∀ a∈A,0<a ∧ a≤X) :
    (∑ a∈A,(a : ℝ)⁻¹)≤1+log X := by
  have hs : A⊆Finset.Icc 1 X := by
    intro a ha
    exact Finset.mem_Icc.mpr ⟨(hA a ha).1,(hA a ha).2⟩
  have h := harmonic_le_one_add_log X
  rw [harmonic_eq_sum_Icc] at h
  simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at h
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)).trans h

theorem owner_inverse_sum (u : ℝ) (N : ℕ) :
    (∑ p∈owners u N,(p : ℝ)⁻¹)≤1+(5/4 : ℝ)*N := by
  by_cases h : (owners u N).Nonempty
  · let X := (owners u N).max' h
    have hX : X∈owners u N := Finset.max'_mem _ h
    have hg := (owners_data hX).2.2.2
    have hh := inverse_sum_bound (owners u N) (X:=X) (by
      intro p hp
      exact ⟨(owners_data hp).1.pos,Finset.le_max' _ p hp⟩)
    linarith only [hh,hg]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp h,Finset.sum_empty]
    positivity

/-- Harmonic aggregation preserves the full native head, while providing
only a polynomial factor for its exponentially small operator change. -/
theorem head_envelope {u : ℝ} (hu : 0≤u) {N : ℕ} (hN : 64≤N) (y : ℝ)
    (hPL : ∀ p∈owners u N,log p≤SquarefreeVaughanLogSource.length u N) :
    (∑ p∈owners u N,∑ q∈pairInterval N p,‖originalPair u y N p q‖)≤
      u^(N+1)*radialCap N*(1+(5/4 : ℝ)*N)^2 := by
  have hD : 0≤1+(5/4 : ℝ)*N := by positivity
  have hcap : 0≤u^(N+1)*radialCap N :=
    mul_nonneg (pow_nonneg hu _) (radialCap_nonneg N)
  calc
    _ ≤ ∑ p∈owners u N,∑ q∈pairInterval N p,
      u^(N+1)*radialCap N/(p : ℝ)/(q : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hpl,hql⟩ := head_prime_logs hp hq
      have hn : (64 : ℝ)≤N := by exact_mod_cast hN
      have hx0 : 0≤log q/(log p+log q) := div_nonneg (by linarith) (by linarith)
      have hx1 : log q/(log p+log q)≤1 :=
        (div_le_one (by linarith : 0<log p+log q)).mpr (by linarith)
      rw [originalPair_norm hN hp hq y,
        abs_of_nonneg (rawAmount_bounds hu hN hp hq (hPL p hp)).1]
      exact (mul_le_of_le_one_right (rawAmount_bounds hu hN hp hq (hPL p hp)).1
        (ownerWeight_bounds N hx0 hx1).2).trans
          (rawAmount_bounds hu hN hp hq (hPL p hp)).2
    _ = ∑ p∈owners u N,(u^(N+1)*radialCap N/(p : ℝ))*
        ∑ q∈pairInterval N p,(q : ℝ)⁻¹ := by
      simp only [div_eq_mul_inv,Finset.mul_sum]
    _ ≤ ∑ p∈owners u N,(u^(N+1)*radialCap N/(p : ℝ))*(1+(5/4 : ℝ)*N) := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := inverse_sum_bound (pairInterval N p) (X:=p) (by
        intro q hq
        have hlo := (Finset.mem_Ioc.mp hq).1
        exact ⟨by omega,(pair_cofactor_lt_owner hN hp hq).le⟩)
      have hg := (owners_data hp).2.2.2
      apply mul_le_mul_of_nonneg_left (hh.trans (by linarith only [hg]))
      positivity
    _ = u^(N+1)*radialCap N*(1+(5/4 : ℝ)*N)*
        ∑ p∈owners u N,(p : ℝ)⁻¹ := by
      simp only [div_eq_mul_inv,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ u^(N+1)*radialCap N*(1+(5/4 : ℝ)*N)^2 := by
      exact (mul_le_mul_of_nonneg_left (owner_inverse_sum u N)
        (mul_nonneg hcap hD)).trans_eq (by ring)

/-- Explicit global source-scale difference budget. It is independent
of the phase height and vanishes exponentially on the native schedule. -/
def budget (N : ℕ) : ℝ := 10*((N : ℝ)+1)^3*exp (-(N : ℝ)/2)

theorem budget_nonneg (N : ℕ) : 0≤budget N := by
  unfold budget
  positivity

private theorem source_power_bound {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    (2*u)^(N+1)≤2*exp ((N : ℝ)/1000) := by
  have hx : 2*u≤exp (1/1000 : ℝ) := by
    have he := add_one_le_exp (1/1000 : ℝ)
    unfold ZetaRieszWideOwnerAudit.radiusCeiling at hU
    linarith only [hU,he]
  have h := pow_le_pow_left₀ (by positivity : 0≤2*u) hx (N+1)
  rw [← exp_nat_mul] at h
  have hid : ((N+1 : ℕ) : ℝ)*(1/1000)=(N : ℝ)/1000+1/1000 := by
    push_cast
    ring
  rw [hid,exp_add] at h
  have he : exp (1/1000 : ℝ)≤2 := by
    calc
      _ ≤ exp (log 2) := exp_le_exp.mpr (by linarith [log_two_gt_d9])
      _ = 2 := exp_log (by norm_num : (0 : ℝ)<2)
  exact h.trans ((mul_le_mul_of_nonneg_left he (exp_pos _).le).trans_eq (by ring))

private theorem budget_majorizes {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    3*exp (-(2/3 : ℝ)*N)*(u^(N+1)*radialCap N*(1+(5/4 : ℝ)*N)^2)≤budget N := by
  have hn : 0≤(N : ℝ) := Nat.cast_nonneg _
  have hD : (1+(5/4 : ℝ)*N)^2≤(25/16 : ℝ)*((N : ℝ)+1)^2 := by
    have h := pow_le_pow_left₀ (by positivity : 0≤1+(5/4 : ℝ)*N)
      (show 1+(5/4 : ℝ)*N≤(5/4)*((N : ℝ)+1) by linarith) 2
    exact h.trans_eq (by ring)
  have hp := source_power_bound hu hU N
  have he : exp ((N : ℝ)/1000)*exp (-(2/3 : ℝ)*N)=
      exp (((1/1000 : ℝ)-2/3)*N) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    _ = 3*((N : ℝ)+1)*(2*u)^(N+1)*exp (-(2/3 : ℝ)*N)*(1+(5/4 : ℝ)*N)^2 := by
      rw [radialCap,mul_pow]
      ring
    _ ≤ 3*((N : ℝ)+1)*(2*exp ((N : ℝ)/1000))*exp (-(2/3 : ℝ)*N)*
        ((25/16 : ℝ)*((N : ℝ)+1)^2) := by gcongr
    _ = (75/8 : ℝ)*((N : ℝ)+1)^3*exp (((1/1000 : ℝ)-2/3)*N) := by
      rw [show 3*((N : ℝ)+1)*(2*exp ((N : ℝ)/1000))*exp (-(2/3 : ℝ)*N)*
        ((25/16 : ℝ)*((N : ℝ)+1)^2)=
          (75/8 : ℝ)*((N : ℝ)+1)^3*
            (exp ((N : ℝ)/1000)*exp (-(2/3 : ℝ)*N)) by ring,he]
    _ ≤ 10*((N : ℝ)+1)^3*exp (-(N : ℝ)/2) := by
      gcongr
      · norm_num
      · nlinarith only [hn]
    _ = _ := rfl

/-- The COMPLETE hard-masked signed correction changes by at most
10*(N+1)^3*exp(-N/2). No original head source is discarded. -/
theorem filteredHead_error {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 < |y|)
    {N : ℕ} (hN : 64≤N) :
    ‖filteredHead u y N-originalHead u y N‖≤budget N := by
  rw [filteredHead,originalHead,← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p∈owners u N,∑ q∈pairInterval N p,
      ‖filteredPair u y N p q-originalPair u y N p q‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => norm_sum_le _ _))
    _ ≤ ∑ p∈owners u N,∑ q∈pairInterval N p,
      3*exp (-(2/3 : ℝ)*N)*‖originalPair u y N p q‖ := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.sum_le_sum (fun q hq => filteredPair_error hy hN hp hq)
    _ = 3*exp (-(2/3 : ℝ)*N)*
        (∑ p∈owners u N,∑ q∈pairInterval N p,‖originalPair u y N p q‖) := by
      simp only [Finset.mul_sum]
    _ ≤ 3*exp (-(2/3 : ℝ)*N)*
        (u^(N+1)*radialCap N*(1+(5/4 : ℝ)*N)^2) :=
      mul_le_mul_of_nonneg_left
        (head_envelope hu hN y (fun _ hp => owner_log_le_length hp)) (by positivity)
    _ ≤ _ := budget_majorizes hu hU N

/-- A rational certificate for the operator-change budget at the FIRST
native order N=256, not an empirical small-order extrapolation. -/
theorem budget_first_native_lt : budget 256<1/(10 : ℝ)^40 := by
  have he4 : (50 : ℝ)≤exp 4 := by
    have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤4) 9
    norm_num [Finset.sum_range_succ,Nat.factorial] at h
    linarith only [h]
  have he128 : (50 : ℝ)^32≤exp 128 := by
    calc
      _ ≤ (exp 4)^32 := pow_le_pow_left₀ (by norm_num) he4 32
      _ = _ := by rw [← exp_nat_mul]; norm_num
  rw [budget]
  norm_num only [Nat.cast_ofNat]
  rw [exp_neg,← div_eq_mul_inv,div_lt_iff₀ (exp_pos _)]
  convert (by norm_num : 10*(257 : ℝ)^3<(1/(10 : ℝ)^40)*(50 : ℝ)^32).trans_le
    (mul_le_mul_of_nonneg_left he128 (by positivity)) using 1 <;> norm_num

theorem budget_succ_le {N : ℕ} (hN : 64≤N) : budget (N+1)≤budget N := by
  have hn : (64 : ℝ)≤N := by exact_mod_cast hN
  have he : exp (-(1/2 : ℝ))≤2/3 := by
    rw [exp_neg,← one_div,div_le_iff₀ (exp_pos _)]
    have h := add_one_le_exp (1/2 : ℝ)
    nlinarith only [h]
  have hp : ((N : ℝ)+2)^3≤(729/512 : ℝ)*((N : ℝ)+1)^3 := by
    have h := pow_le_pow_left₀ (by positivity : 0≤(N : ℝ)+2)
      (show (N : ℝ)+2≤(9/8)*((N : ℝ)+1) by linarith only [hn]) 3
    exact h.trans_eq (by ring)
  have hE : -((N+1 : ℕ) : ℝ)/2=-(N : ℝ)/2-1/2 := by push_cast; ring
  rw [budget,budget,hE,exp_sub]
  have he' : (exp (1/2 : ℝ))⁻¹≤2/3 := by rwa [exp_neg] at he
  calc
    _ = 10*((N : ℝ)+2)^3*exp (-(N : ℝ)/2)*(exp (1/2 : ℝ))⁻¹ := by
      push_cast
      ring
    _ ≤ 10*((729/512 : ℝ)*((N : ℝ)+1)^3)*exp (-(N : ℝ)/2)*(2/3) := by
      gcongr
    _ ≤ 10*((N : ℝ)+1)^3*exp (-(N : ℝ)/2) := by
      nlinarith only [mul_nonneg
        (pow_nonneg (by positivity : 0≤(N : ℝ)+1) 3) (exp_pos (-(N : ℝ)/2)).le]

/-- The certified small price holds at EVERY native order from256 on. -/
theorem budget_lt_native {N : ℕ} (hN : 256≤N) : budget N<1/(10 : ℝ)^40 := by
  have h : budget N≤budget 256 := by
    induction N, hN using Nat.le_induction with
    | base => exact le_refl _
    | succ N hN ih => exact (budget_succ_le (by omega : 64≤N)).trans ih
  exact h.trans_lt budget_first_native_lt

theorem budget_tendsto : Tendsto budget atTop (𝓝 0) := by
  have h := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    (exp_pos (-(1/2 : ℝ))) (exp_lt_one_iff.mpr (by norm_num : -(1/2 : ℝ)<0))).const_mul 10
  simp only [mul_zero] at h
  apply h.congr' (Eventually.of_forall fun N => ?_)
  unfold budget
  rw [← exp_nat_mul]
  rw [show (N : ℝ)*(-(1/2 : ℝ))=-(N : ℝ)/2 by ring]
  ring

/-- All hypotheses of the global arithmetic payment are available
eventually from the ACTUAL moving length and original physical set. -/
theorem eventually_filteredHead_error {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 < |y|) :
    ∀ᶠ N : ℕ in atTop,‖filteredHead u y N-originalHead u y N‖≤budget N := by
  filter_upwards [eventually_ge_atTop (64 : ℕ)] with N hN
  exact filteredHead_error (by linarith only [hu] : 0≤u) hU hy hN

theorem tendsto_filteredHead_sub_original {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 < |y|) :
    Tendsto (fun N => filteredHead u y N-originalHead u y N) atTop (𝓝 0) :=
  squeeze_zero_norm' (eventually_filteredHead_error hu hU hy) budget_tendsto

/-- Substituting the paid per-leg pole killer retains the exact whole
source ledger. This is NOT an independent signed floor. -/
theorem tendsto_central_sub_filteredHead_sub_native {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 < |y|) :
    Tendsto (fun j => (ZetaRieszBalancedRadialPayment.centralRest u y j).re-
      (filteredHead u y (dyadicMomentOrder j)).re-
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re)
      atTop (𝓝 0) := by
  have hpaid : Tendsto (fun j => (filteredHead u y (dyadicMomentOrder j)).re-
      ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.sub_re,originalHead_re,Complex.zero_re] using
      (Complex.continuous_re.tendsto 0).comp
        ((tendsto_filteredHead_sub_original hu hU hy).comp tendsto_dyadicMomentOrder)
  have h := (ZetaRieszBalancedRadialPayment.tendsto_central_sub_head_sub_native
    hu hU hy.le).sub hpaid
  simp only [sub_zero] at h
  exact h.congr' (Eventually.of_forall fun _ => by ring)

/-- Any actual one-sided estimate for the JOINT balanced sum minus
filtered head transfers to joinedPhysical. All original paid errors and
the new operator-change budget appear exactly once. Its signed premise
is the remaining arithmetic problem, not an assumption hidden in a price. -/
theorem eventually_joined_floor_of_joint {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 < |y|)
    (B : ℕ→ℝ)
    (hf : ∀ᶠ j in atTop,-B j≤(ZetaRieszBalancedRadialPayment.centralRest u y j).re-
      (filteredHead u y (dyadicMomentOrder j)).re) :
    ∀ᶠ j in atTop,
      -B j-budget (dyadicMomentOrder j)-ZetaRieszBalancedOwnerFloor.budget u y j-
        ZetaRieszBalancedAllocationPayment.allocationBudget j-
          ZetaRieszBalancedRadialPayment.radialBudget j-
            ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [hf,
    tendsto_dyadicMomentOrder.eventually (eventually_filteredHead_error hu hU hy),
    ZetaRieszBalancedOwnerFloor.eventually_high_packet_joint_bound hu hU hy.le]
    with j hf he hb
  have hhead := Complex.re_le_norm
    (originalHead u y (dyadicMomentOrder j)-filteredHead u y (dyadicMomentOrder j))
  rw [Complex.sub_re,originalHead_re,norm_sub_rev] at hhead
  have ha := ZetaRieszBalancedAllocationPayment.unallocated_sub_rest_bound
    (by linarith : 0≤u) hU j y
  have hrad := ZetaRieszBalancedRadialPayment.central_sub_unallocated_real_bound
    (by linarith : 0≤u) hU j y
  let P := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
    (dyadicMomentOrder j) (dyadicPrimeCount j)
  let Q := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
    (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hr : Q.re-P.re≤‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  have hnative := ZetaRieszBalancedOwnerFloor.native_real_eq_rest_high u y j
  change Q.re=ZetaRieszBalancedOwnerFloor.restPacket u y j+
    ZetaRieszBalancedOwnerFloor.highPacket u y j at hnative
  change -B j-budget (dyadicMomentOrder j)-ZetaRieszBalancedOwnerFloor.budget u y j-
    ZetaRieszBalancedAllocationPayment.allocationBudget j-
      ZetaRieszBalancedRadialPayment.radialBudget j-(4*|P.im|+5*‖Q-P‖)≤P.re
  linarith only [hf,he,hhead,hnative,hr,(abs_le.mp hb).1,(abs_le.mp ha).2,
    (abs_le.mp hrad).2,abs_nonneg P.im,norm_nonneg (Q-P)]

end RiemannGaussian.ZetaRieszPrimeHeadPolePayment

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLowCountSignedBoundary
import RiemannGaussian.ZetaRieszSignedDensityMain
import RiemannGaussian.ZetaRieszSignedSelbergPayment

/-!
# Geometric payment of the prime-pair owner masks

Join the actual head and unallocated correction before comparing them with
one exact binomial prefix. The prefix keeps every factorial order, including
zero. Only the difference of the joined coefficients is normed; its explicit
exponential saving is stronger than the source growth. The signed prefix
main is not paid or assumed bounded here.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPairPrefixPayment
open ZetaRieszJointAllocation ZetaRieszOwnerMaximal

/-- A lower-tail tilt for the exact prefix, including order zero. -/
theorem prefix_tilt (M K : ℕ) (hK : K ≤ M) {x q : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hq : 1 < q) :
    lowerMass M K x ≤ exp ((K : ℝ)*log q)*(q⁻¹*x+(1-x))^M := by
  have ht : 0 ≤ log q := log_nonneg hq.le
  let B := exp ((K : ℝ)*log q)
  have hb (k : ℕ) (hk : k ∈ Finset.range (K+1)) : 1 ≤ B*(q⁻¹)^k := by
    have hkK : (k : ℝ) ≤ K := by exact_mod_cast (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk) : k ≤ K)
    rw [show q⁻¹=exp (-log q) by rw [exp_neg,exp_log (by linarith : 0<q)],
      ← exp_nat_mul,←exp_add]
    apply one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hkK ht]
  calc
    lowerMass M K x ≤ ∑ k ∈ Finset.range (K+1), B*(q⁻¹)^k*mass M k x := by
      apply Finset.sum_le_sum
      intro k hk
      exact le_mul_of_one_le_left (mass_nonneg M k hx hx1) (hb k hk)
    _ ≤ ∑ k ∈ Finset.range (M+1), B*(q⁻¹)^k*mass M k x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun k _ _ => mul_nonneg (mul_nonneg (by dsimp [B]; positivity)
          (pow_nonneg (inv_nonneg.mpr (by linarith : 0≤q)) k)) (mass_nonneg M k hx hx1))
    _ = _ := by simp only [mul_assoc,←Finset.mul_sum]; rw [mass_tilt]

/-- The complementary prefix has an upper-tail tilt with its literal floor. -/
theorem complement_tilt (N : ℕ) {x q : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hq : 1 < q) :
    1-lowerMass (N+1) (13*N/32) x ≤
      exp (-(13/32 : ℝ)*N*log q)*(q*x+(1-x))^(N+1) := by
  let S := Finset.range (N+2)
  let U := Finset.range (13*N/32+1)
  have hUS : U ⊆ S := Finset.range_mono (by omega)
  have he : 1-lowerMass (N+1) (13*N/32) x=∑ k∈S\U,mass (N+1) k x := by
    have h := Finset.sum_sdiff (f:=fun k => mass (N+1) k x) hUS
    rw [mass_total] at h
    change _+lowerMass (N+1) (13*N/32) x=1 at h
    linarith
  let B := exp (-(13/32 : ℝ)*N*log q)
  have ht : 0 ≤ log q := log_nonneg hq.le
  have hb (k : ℕ) (hk : k∈S\U) : 1 ≤ B*q^k := by
    have hcut : 13*N/32<k := by
      have h := (Finset.mem_sdiff.mp hk).2
      simp only [U,Finset.mem_range] at h
      omega
    have hkN : (13/32 : ℝ)*N ≤ k := by
      have h : 13*N<32*k := by omega
      have hr : 13*(N : ℝ)<32*k := by exact_mod_cast h
      linarith
    rw [←exp_log (by linarith : 0<q),←exp_nat_mul,←exp_add]
    apply one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hkN ht]
  rw [he]
  calc
    _ ≤ ∑ k∈S\U,B*q^k*mass (N+1) k x := by
      apply Finset.sum_le_sum
      intro k hk
      exact le_mul_of_one_le_left (mass_nonneg _ _ hx hx1) (hb k hk)
    _ ≤ ∑ k∈S,B*q^k*mass (N+1) k x :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun k _ _ =>
        mul_nonneg (mul_nonneg (by dsimp [B]; positivity)
          (pow_nonneg (by linarith : 0≤q) k)) (mass_nonneg _ _ hx hx1))
    _ = _ := by simp only [mul_assoc,←Finset.mul_sum]; rw [mass_tilt]; simp only [B,mul_assoc]

private theorem log_upper_tilt : log (10/9 : ℝ) ≤ 106/1000 := by
  apply (log_le_iff_le_exp (by norm_num : (0 : ℝ)<10/9)).mpr
  have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤106/1000) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem upper_tail_log_rate :
    log (2077/2000 : ℝ)-(13/32 : ℝ)*log (11/10) ≤ -(1/1250) := by
  have hlo : (9531/100000 : ℝ)≤log (11/10) := by
    have h := sum_range_le_log_div (by norm_num : (0 : ℝ)≤1/21)
      (by norm_num : (1/21 : ℝ)<1) 2
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hhi : log (2077/2000 : ℝ)≤37778/1000000 := by
    apply (log_le_iff_le_exp (by norm_num : (0 : ℝ)<2077/2000)).mpr
    have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤37778/1000000) 5
    norm_num [Finset.sum_range_succ] at h
    linarith
  linarith

/-- Every cofactor below the high-owner transition has a geometric
complement tail. The integer `13*N/32` is not replaced by a limit. -/
theorem high_owner_tail (N : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 77/200) :
    1-lowerMass (N+1) (13*N/32) x ≤ 2*exp (-(N : ℝ)/1250) := by
  have h := complement_tilt N hx (by linarith : x≤1) (by norm_num : (1 : ℝ)<11/10)
  have hbase : (11/10 : ℝ)*x+(1-x) ≤ 2077/2000 := by linarith
  have hnonneg : 0 ≤ (11/10 : ℝ)*x+(1-x) := by linarith
  have hb := pow_le_pow_left₀ hnonneg hbase (N+1)
  have hp := mul_le_mul_of_nonneg_left hb (exp_pos (-(13/32 : ℝ)*N*log (11/10))).le
  apply (h.trans hp).trans
  rw [←exp_log (by norm_num : (0 : ℝ)<2077/2000),←exp_nat_mul,←exp_add]
  have hN : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hr : -(13/32 : ℝ)*N*log (11/10)+((N+1 : ℕ) : ℝ)*log (2077/2000) ≤
      log (2077/2000)-(N : ℝ)/1250 := by
    have hm := mul_le_mul_of_nonneg_right upper_tail_log_rate hN
    push_cast
    nlinarith only [hm]
  calc
    _ ≤ exp (log (2077/2000)-(N : ℝ)/1250) := exp_le_exp.mpr hr
    _ = (2077/2000 : ℝ)*exp (-(N : ℝ)/1250) := by
      rw [sub_eq_add_neg,exp_add,exp_log (by norm_num)]
      congr 1
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (exp_pos _).le

/-- On the low-owner and nonowner sides the same prefix is tiny. -/
theorem low_owner_tail (N : ℕ) {x : ℝ} (hx : 12/25 ≤ x) (hx1 : x ≤ 1) :
    lowerMass (N+1) (13*N/32) x ≤ exp (-(N : ℝ)/250) := by
  have hx0 : 0≤x := by linarith
  have h := prefix_tilt (N+1) (13*N/32) (by omega) hx0 hx1
    (by norm_num : (1 : ℝ)<10/9)
  have hbase : (10/9 : ℝ)⁻¹*x+(1-x) ≤ 119/125 := by norm_num; linarith
  have hnonneg : 0 ≤ (10/9 : ℝ)⁻¹*x+(1-x) := by norm_num; linarith
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hbase (N+1))
    (exp_pos ((13*N/32 : ℕ)*log (10/9))).le
  apply (h.trans hp).trans
  rw [←exp_log (by norm_num : (0 : ℝ)<119/125),←exp_nat_mul,←exp_add]
  apply exp_le_exp.mpr
  have hcut : ((13*N/32 : ℕ) : ℝ)≤(13/32 : ℝ)*N := by
    have hN : 32*(13*N/32) ≤ 13*N := Nat.mul_div_le _ _
    have hr : 32*((13*N/32 : ℕ) : ℝ)≤13*N := by exact_mod_cast hN
    linarith
  have hlo : 0 ≤ log (10/9 : ℝ) := log_nonneg (by norm_num)
  have hb : log (119/125 : ℝ)≤-(6/125) := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<119/125)
    linarith
  have h1 := mul_le_mul_of_nonneg_right log_upper_tilt (Nat.cast_nonneg (α:=ℝ) (13*N/32))
  have h2 := mul_le_mul_of_nonneg_right hcut (by norm_num : (0 : ℝ)≤106/1000)
  have h3 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α:=ℝ) (N+1))
  push_cast at h3
  push_cast
  nlinarith only [h1,h2,h3,Nat.cast_nonneg (α:=ℝ) N]

/-- Removing the lower endpoint only on the actual head costs a
geometric tail, rather than an independent positive cofactor price. -/
theorem head_lower_tail (N : ℕ) {x : ℝ} (hx : 9/25 ≤ x) (hx1 : x ≤ 1) :
    lowerMass (N+1) (N/5+1) x ≤ 2*exp (-(N : ℝ)/40) := by
  have hx0 : 0≤x := by linarith
  have h := prefix_tilt (N+1) (N/5+1) (by omega) hx0 hx1
    (by norm_num : (1 : ℝ)<5/4)
  have hbase : (5/4 : ℝ)⁻¹*x+(1-x) ≤ 116/125 := by norm_num; linarith
  have hnonneg : 0 ≤ (5/4 : ℝ)⁻¹*x+(1-x) := by norm_num; linarith
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hbase (N+1))
    (exp_pos (((N/5+1 : ℕ) : ℝ)*log (5/4))).le
  apply (h.trans hp).trans
  rw [←exp_log (by norm_num : (0 : ℝ)<116/125),←exp_nat_mul,←exp_add]
  have hcut : ((N/5+1 : ℕ) : ℝ)≤(N : ℝ)/5+1 := by
    have h : 5*(N/5)≤N := Nat.mul_div_le _ _
    have hr : 5*((N/5 : ℕ) : ℝ)≤N := by exact_mod_cast h
    push_cast
    linarith
  have hb : log (116/125 : ℝ)≤-(9/125) := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<116/125)
    linarith
  have h1 := mul_le_mul_of_nonneg_right log_tilt_bounds.2 (Nat.cast_nonneg (α:=ℝ) (N/5+1))
  have h2 := mul_le_mul_of_nonneg_right hcut (by norm_num : (0 : ℝ)≤224/1000)
  have h3 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α:=ℝ) (N+1))
  have hr : ((N/5+1 : ℕ) : ℝ)*log (5/4)+((N+1 : ℕ) : ℝ)*log (116/125) ≤
      (224/1000 : ℝ)-(N : ℝ)/40 := by
    push_cast at h1 h2 h3 ⊢
    nlinarith only [h1,h2,h3,Nat.cast_nonneg (α:=ℝ) N]
  calc
    _ ≤ exp ((224/1000 : ℝ)-(N : ℝ)/40) := exp_le_exp.mpr hr
    _ ≤ 2*exp (-(N : ℝ)/40) := by
      rw [sub_eq_add_neg,exp_add]
      rw [show -((N : ℝ)/40)=-(N : ℝ)/40 by ring]
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      calc
        _ ≤ exp (log 2) := exp_le_exp.mpr (by linarith [log_two_gt_d9])
        _ = _ := exp_log (by norm_num)

/-- The joined two-hinge coefficient in the original canonical prime
coordinates. The head and correction retain their distinct owner masks. -/
def joinedLogCoefficient (N : ℕ) (L x z : ℝ) : ℝ :=
  -(x+z)/L*(L-max 0 (L-x)-max 0 (L-z)+max 0 (L-x-z))+
    (if (51/50 : ℝ)*N≤x ∧ x≤(5/4 : ℝ)*N then
      (x+z)/L*(L-x)*ownerWeight N (z/(x+z)) else 0)-
    (if (51/50 : ℝ)*N≤x ∧ x≤L then (x+z)/L*(L-x) else 0)

/-- A symmetric exact factorial prefix, with no largest-prime/share mask.
Its signed contribution remains unpaid. -/
def prefixLogCoefficient (N : ℕ) (L x z : ℝ) : ℝ :=
  (x+z)*(1-(x+z)/L)-(x+z)/L*
    ((L-x)*lowerMass (N+1) (13*N/32) (z/(x+z))+
     (L-z)*lowerMass (N+1) (13*N/32) (x/(x+z)))

private theorem alpha_bound {L T x : ℝ} (hL : 0<L) (hT : 0≤T)
    (hx : 0≤x) (hxT : x≤T) (hTL : T≤2*L) : |T/L*(L-x)|≤T := by
  have ha : |L-x|≤L := abs_le.mpr ⟨by linarith,by linarith⟩
  rw [abs_mul,abs_of_nonneg (div_nonneg hT hL.le)]
  exact (mul_le_mul_of_nonneg_left ha (div_nonneg hT hL.le)).trans_eq
    (div_mul_cancel₀ _ hL.ne')

/-- ALL owner geometries are paid together by a single coefficient error.
Only this difference is normed, with a fixed saving `exp(-N/1250)`.
The comparison keeps the exact prefix and every factorial order. -/
theorem joined_sub_prefix_log_bound {N : ℕ} (hN : 32≤N) {L x z : ℝ}
    (hx0 : 0≤x) (hz0 : 0≤z) (hzx : z≤x)
    (hlo : (1971/1000 : ℝ)*N≤x+z) (hhi : x+z≤(2029/1000 : ℝ)*N)
    (hLl : (277/200 : ℝ)*N≤L) (hLu : L≤(7/5 : ℝ)*N) :
    |joinedLogCoefficient N L x z-prefixLogCoefficient N L x z|≤
      3*(x+z)*exp (-(N : ℝ)/1250) := by
  let T := x+z
  let F := lowerMass (N+1) (13*N/32) (z/T)
  let G := lowerMass (N+1) (N/5+1) (z/T)
  let alpha := T/L*(L-x)
  let Q := T*(1-T/L)-alpha*F
  have hNr : (32 : ℝ)≤N := by exact_mod_cast hN
  have hTp : 0<T := by dsimp [T]; nlinarith only [hlo,hNr]
  have hLp : 0<L := by nlinarith only [hLl,hNr]
  have hTL : T≤2*L := by dsimp [T]; nlinarith only [hhi,hLl,hNr]
  have hzL : z≤L := by nlinarith only [hhi,hLl,hzx,hNr]
  have hAL : (5/4 : ℝ)*N≤L := by nlinarith only [hLl,hNr]
  have hLT : L≤x+z := by nlinarith only [hlo,hLu,hNr]
  have hzT : z≤T := by dsimp [T]; linarith
  have hxT : x≤T := by dsimp [T]; linarith
  have hs0 : 0≤z/T := div_nonneg hz0 hTp.le
  have hs1 : z/T≤1 := (div_le_one hTp).mpr hzT
  have hF := lowerMass_bounds (N+1) (13*N/32) hs0 hs1
  have hA : |alpha|≤T := alpha_bound hLp hTp.le hx0 hxT hTL
  have hw : ownerWeight N (z/T)=1-F+G := by
    rw [ownerWeight,ownerMass_eq_difference hN]
    dsimp [F,G]
    ring
  have hE250 : exp (-(N : ℝ)/250)≤exp (-(N : ℝ)/1250) := exp_le_exp.mpr (by nlinarith)
  have hE40 : exp (-(N : ℝ)/40)≤exp (-(N : ℝ)/1250) := exp_le_exp.mpr (by nlinarith)
  have hcan : |joinedLogCoefficient N L x z-Q|≤2*T*exp (-(N : ℝ)/1250) := by
    by_cases hxlo : x<(51/50 : ℝ)*N
    · have hxL : x≤L := by nlinarith only [hxlo,hAL,hNr]
      have hs : (12/25 : ℝ)≤z/T := by
        apply (le_div_iff₀ hTp).mpr
        dsimp [T]
        nlinarith only [hxlo,hlo,hNr]
      have hf := low_owner_tail N hs hs1
      have he : joinedLogCoefficient N L x z-Q=alpha*F := by
        have hnh : ¬((51/50 : ℝ)*N≤x ∧ x≤(5/4 : ℝ)*N) := fun h => (not_le_of_gt hxlo) h.1
        have hnc : ¬((51/50 : ℝ)*N≤x ∧ x≤L) := fun h => (not_le_of_gt hxlo) h.1
        simp only [joinedLogCoefficient,if_neg hnh,if_neg hnc,
          max_eq_right (sub_nonneg.mpr hxL),max_eq_right (sub_nonneg.mpr hzL),
          max_eq_left (by linarith only [hLT] : L-x-z≤0)]
        dsimp [Q,alpha,T]
        field_simp [hLp.ne']
        ring
      rw [he,abs_mul,abs_of_nonneg hF.1]
      exact (mul_le_mul hA (hf.trans hE250) hF.1 hTp.le).trans (by
        have h := mul_nonneg hTp.le (exp_pos (-(N : ℝ)/1250)).le
        nlinarith only [h])
    · have hlo' : (51/50 : ℝ)*N≤x := le_of_not_gt hxlo
      by_cases hxhi : x≤(5/4 : ℝ)*N
      · have hxL : x≤L := hxhi.trans hAL
        have hs : (9/25 : ℝ)≤z/T := by
          apply (le_div_iff₀ hTp).mpr
          dsimp [T]
          nlinarith only [hxhi,hlo,hNr]
        have hg := head_lower_tail N hs hs1
        have hG0 := (lowerMass_bounds (N+1) (N/5+1) hs0 hs1).1
        have he : joinedLogCoefficient N L x z-Q=alpha*G := by
          simp only [joinedLogCoefficient,if_pos (And.intro hlo' hxhi),if_pos (And.intro hlo' hxL),
            max_eq_right (sub_nonneg.mpr hxL),max_eq_right (sub_nonneg.mpr hzL),
            max_eq_left (by linarith only [hLT] : L-x-z≤0)]
          rw [show ownerWeight N (z/(x+z))=1-F+G from hw]
          dsimp [Q,alpha,T]
          field_simp [hLp.ne']
          ring
        rw [he,abs_mul,abs_of_nonneg hG0]
        have hg' := hg.trans (mul_le_mul_of_nonneg_left hE40 (by norm_num : (0 : ℝ)≤2))
        exact (mul_le_mul hA hg' hG0 hTp.le).trans_eq (by ring)
      · have hxhi' : (5/4 : ℝ)*N<x := lt_of_not_ge hxhi
        have hs : z/T≤77/200 := by
          apply (div_le_iff₀ hTp).mpr
          dsimp [T]
          nlinarith only [hxhi',hhi,hNr]
        have hf := high_owner_tail N hs0 hs
        have he : joinedLogCoefficient N L x z-Q=alpha*(F-1) := by
          have hnh : ¬((51/50 : ℝ)*N≤x ∧ x≤(5/4 : ℝ)*N) := fun h => hxhi h.2
          by_cases hxL : x≤L
          · simp only [joinedLogCoefficient,if_neg hnh,if_pos (And.intro hlo' hxL),
              max_eq_right (sub_nonneg.mpr hxL),max_eq_right (sub_nonneg.mpr hzL),
              max_eq_left (by linarith only [hLT] : L-x-z≤0)]
            dsimp [Q,alpha,T]
            field_simp [hLp.ne']
            ring
          · simp only [joinedLogCoefficient,if_neg hnh,if_neg (fun h :
                (51/50 : ℝ)*N≤x ∧ x≤L => hxL h.2),
              max_eq_left (by linarith : L-x≤0),max_eq_right (sub_nonneg.mpr hzL),
              max_eq_left (by linarith only [hLT] : L-x-z≤0)]
            dsimp [Q,alpha,T]
            field_simp [hLp.ne']
            ring
        rw [he,abs_mul,abs_of_nonpos (by linarith only [hF.2] : F-1≤0)]
        have hn : 0≤-(F-1) := by linarith only [hF.2]
        have hf' : -(F-1)≤2*exp (-(N : ℝ)/1250) := by linarith only [hf]
        exact (mul_le_mul hA hf' hn hTp.le).trans_eq (by ring)
  have hs : (12/25 : ℝ)≤x/T := by
    apply (le_div_iff₀ hTp).mpr
    dsimp [T]
    nlinarith only [hzx,hTp]
  have hs' : x/T≤1 := (div_le_one hTp).mpr hxT
  have hF' := low_owner_tail N hs hs'
  have hF0 := (lowerMass_bounds (N+1) (13*N/32) (div_nonneg hx0 hTp.le) hs').1
  have hB := alpha_bound hLp hTp.le hz0 hzT hTL
  have herr : |T/L*(L-z)*lowerMass (N+1) (13*N/32) (x/T)|≤
      T*exp (-(N : ℝ)/1250) := by
    rw [abs_mul,abs_of_nonneg hF0]
    exact mul_le_mul hB (hF'.trans hE250) hF0 hTp.le
  have he : joinedLogCoefficient N L x z-prefixLogCoefficient N L x z=
      (joinedLogCoefficient N L x z-Q)+T/L*(L-z)*lowerMass (N+1) (13*N/32) (x/T) := by
    dsimp [prefixLogCoefficient,Q,alpha,F,T]
    ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hcan herr).trans_eq (by dsimp [T]; ring))

open ZetaRieszLowCountSignedBoundary ZetaRieszGlobalHeadCentralPayment
open ZetaRieszGlobalCentralPayment ZetaRieszGlobalBulkPayment
open ZetaRieszOwnerLatticePhase ZetaRieszSmallTagNativeFloor
open ZetaRieszUnallocatedOwnerPayment ZetaRieszPrimeEndpoint

private theorem canonical_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : q<p) :
    largestPrime (p*q)=p ∧ ZetaRieszOwnedCells.ownerCofactor (p*q)=q ∧ Squarefree (p*q) := by
  have hm : ∀ r∈q.primeFactors,r<p := by
    intro r hr
    rw [hq.primeFactors,Finset.mem_singleton] at hr
    subst r
    exact hpq
  have hs : Squarefree (p*q) := Nat.squarefree_mul_iff.mpr
    ⟨hp.coprime_iff_not_dvd.mpr (fun h => hpq.ne'
      ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)),hp.squarefree,hq.squarefree⟩
  exact ⟨ZetaRieszPrimeIntervals.largestPrime_mul p q hp hq.ne_zero hm,
    ZetaRieszPrimeIntervals.ownerCofactor_mul p q hp hq.ne_zero hm,hs⟩

/-- Exact bridge from the literal joined coefficient. The original radial
support flag is retained, not silently filled at an endpoint. -/
theorem joinedCoefficient_eq_log {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ} (hN : 65536≤N)
    (hp : p.Prime) (hq : q.Prime) (hpq : q<p)
    (hwide : (39/20 : ℝ)*N<log p+log q ∧ log p+log q≤(203/100 : ℝ)*N)
    (hCube : ∀ c : ℝ,c≤(4/3 : ℝ)*N → N^3≤coreFloor N c (39/20)) :
    joinedCoefficient u N (p*q)=
      ((joinedLogCoefficient N (SquarefreeVaughanLogSource.length u N) (log p) (log q) : ℝ) : ℂ)-
      (if p*q∈primeLabels N∪semiprimeLabels N then 0 else
        completedCoefficient (SquarefreeVaughanLogSource.length u N) (p*q)) := by
  let L := SquarefreeVaughanLogSource.length u N
  have hL : 0<L := SquarefreeVaughanLogSource.length_pos u N
  have hLl : (277/200 : ℝ)*N≤L :=
    ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0<u) hU
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ)<q := by exact_mod_cast hq.pos
  obtain ⟨hlarge,hco,hs⟩ := canonical_pair hp hq hpq
  have hlog : log (p*q : ℕ)=log p+log q := by
    rw [Nat.cast_mul,log_mul hp0.ne' hq0.ne']
  have hqI : q∈ZetaRieszPrimeHeadTransport.pairInterval N p := by
    exact (coreFloor_membership N (log p) hq.pos).mpr hwide
  have hqIC : q∈Finset.Ioc (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) := hqI
  have hrough (hh : (51/50 : ℝ)*N≤log p ∧ log p≤(5/4 : ℝ)*N) : N^3<q :=
    lt_of_le_of_lt (hCube (log p) (by nlinarith only [hh.2,hNr])) (Finset.mem_Ioc.mp hqIC).1
  have hhead : p*q∈headLabels u N ↔ (51/50 : ℝ)*N≤log p ∧ log p≤(5/4 : ℝ)*N := by
    constructor
    · intro hn
      obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hn
      have he' : e∈pairs u N := he
      have heP : e.1=p := by
        rw [←largestPrime_label (by omega : 64≤N) he',heq,hlarge]
      have hd := owners_data (Finset.mem_sigma.mp he').1
      rw [heP] at hd
      exact hd.2.2
    · intro hh
      have hrq := hrough hh
      have hsq : N^2≤N^3 := by
        calc
          _ = N^2*1 := by simp
          _ ≤ N^2*N := Nat.mul_le_mul_left _ (by omega : 1≤N)
          _ = _ := by ring
      have hNp : N^2<p := hsq.trans_lt (hrq.trans hpq)
      have hpx : p<(ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 := by
        have hpl : log p<L := by nlinarith only [hh.2,hLl,hNr]
        have h : (p : ℝ)<(ZetaVaughanCutoffBudget.linearDampedCutoff u N+2 : ℝ)^2 :=
          (log_lt_log_iff hp0 (by positivity)).mp hpl
        exact_mod_cast h
      have howners : p∈owners u N := Finset.mem_filter.mpr
        ⟨(ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mpr ⟨hp,hNp,hpx⟩,hh⟩
      exact Finset.mem_image.mpr ⟨⟨p,q⟩,Finset.mem_sigma.mpr
        ⟨howners,Finset.mem_filter.mpr ⟨hqI,hq⟩⟩,rfl⟩
  have hcorr : p*q∈correctionLabels u N ↔ (51/50 : ℝ)*N≤log p ∧ log p≤L := by
    constructor
    · intro hn
      obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hn
      have heP : e.1=p := by rw [←correction_largest hu hU hN he,heq,hlarge]
      have hd := highOwner_data (Finset.mem_sigma.mp he).1
      rw [heP] at hd
      exact hd.2.2
    · intro hh
      have hpF : p≤⌊exp L⌋₊ := by
        apply Nat.le_floor
        rw [←exp_log hp0]
        exact exp_le_exp.mpr hh.2
      have ho : p∈highOwners u N := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hp.pos,hpF⟩,hp,hh.1⟩
      exact Finset.mem_image.mpr ⟨⟨p,q⟩,Finset.mem_sigma.mpr
        ⟨ho,Finset.mem_filter.mpr ⟨hqIC,hq⟩⟩,rfl⟩
  have hheadval : (if p*q∈headLabels u N then headCoefficient u N (p*q) else 0)=
      (((if (51/50 : ℝ)*N≤log p ∧ log p≤(5/4 : ℝ)*N then
        (log p+log q)/L*(L-log p)*ownerWeight N (log q/(log p+log q)) else 0) : ℝ) : ℂ) := by
    by_cases hh : (51/50 : ℝ)*N≤log p ∧ log p≤(5/4 : ℝ)*N
    · have hrq := hrough hh
      have hnone : ¬∃ r∈smallPrimes N,r∣q := by
        rintro ⟨r,hr,hrq⟩
        have hd := Nat.mem_primesLE.mp hr
        have he : r=q := (Nat.prime_dvd_prime_iff_eq hd.2 hq).mp hrq
        omega
      have hS : ZetaRieszUnsignedDivisorError.sieve (smallPrimes N) q=1 := by
        simp only [ZetaRieszUnsignedDivisorError.sieve,if_pos (And.intro hq.squarefree hnone)]
      simp only [if_pos hh,if_pos (hhead.mpr hh),headCoefficient,hlarge,hco,hlog,hS,mul_one,L]
    · simp only [if_neg hh,if_neg (fun h => hh (hhead.mp h)),Complex.ofReal_zero]
  have hcorrval : (if p*q∈correctionLabels u N then correctionCoefficient u N (p*q) else 0)=
      (((if (51/50 : ℝ)*N≤log p ∧ log p≤L then (log p+log q)/L*(L-log p) else 0) : ℝ) : ℂ) := by
    by_cases hh : (51/50 : ℝ)*N≤log p ∧ log p≤L
    · simp only [if_pos hh,if_pos (hcorr.mpr hh),correctionCoefficient,hlarge,hlog,L]
    · simp only [if_neg hh,if_neg (fun h => hh (hcorr.mp h)),Complex.ofReal_zero]
  have hbase : completedCoefficient L (p*q)=
      ((-(log p+log q)/L*(L-max 0 (L-log p)-max 0 (L-log q)+max 0 (L-log p-log q)) : ℝ) : ℂ) := by
    rw [completedCoefficient,if_pos hs,
      ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent L hp hq hpq.ne',hlog]
    unfold ZetaSquarefreeRieszWindows.primePairTent
    rw [max_eq_right hL.le]
    congr 1
    ring
  unfold joinedCoefficient
  rw [hheadval,hcorrval]
  by_cases hn : p*q∈primeLabels N∪semiprimeLabels N
  · simp only [if_pos hn,sub_zero]
    rw [hbase]
    unfold joinedLogCoefficient
    push_cast
    ring
  · simp only [if_neg hn,zero_add]
    rw [hbase]
    unfold joinedLogCoefficient
    push_cast
    ring

open ZetaRieszGlobalPeriodEdgePayment ZetaRieszSignedSelbergPayment
open ZetaRieszLowCountSelbergAudit

/-- The comparison preserves the original radial flag even at a retained
period endpoint. The factorial prefix itself is symmetric in the two primes. -/
def prefixCoefficient (u : ℝ) (N n : ℕ) : ℂ :=
  (prefixLogCoefficient N (SquarefreeVaughanLogSource.length u N)
    (log (largestPrime n)) (log (ZetaRieszOwnedCells.ownerCofactor n)) : ℂ)-
    (if n∈primeLabels N∪semiprimeLabels N then 0 else
      completedCoefficient (SquarefreeVaughanLogSource.length u N) n)

/-- SAME retained original support; no prime is completed, no phase is
frozen, and the signed prefix defect remains an arithmetic target. -/
def prefixPairDefect (u y : ℝ) (N : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∑ n∈
    (completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime),
      (prefixCoefficient u N n-selbergCoefficient n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n

private theorem retained_pair_data {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ} (hN : 65536≤N)
    {y : ℝ} (hy : 54≤|y|)
    (hn : n∈(completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime)) :
    (∃ p q : ℕ,p.Prime ∧ q.Prime ∧ q<p ∧ p*q=n) ∧
      (1971/1000 : ℝ)*N≤log n ∧ log n≤(2029/1000 : ℝ)*N := by
  obtain ⟨hn,hnot⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn,hl,hh⟩ := Finset.mem_filter.mp hn
  have hpair := ordinaryLabel_pair (joinedLabels_ordinary hu hU hN hn)
  have hgeom := period_log_bracket hy n
  refine ⟨?_,hl.trans hgeom.1,hgeom.2.le.trans hh⟩
  rcases hpair with hp | ⟨p,q,hp,hq,hpq,he⟩
  · exact (hnot hp).elim
  · rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact ⟨q,p,hq,hp,hlt,by simpa only [mul_comm] using he⟩
    · exact ⟨p,q,hp,hq,hgt,he⟩

/-- Uniform coefficient saving on EVERY retained distinct pair, with
the original radial support correction cancelling exactly in the difference. -/
theorem joined_sub_prefixCoefficient_bound {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N)
    (hCube : ∀ c : ℝ,c≤(4/3 : ℝ)*N → N^3≤coreFloor N c (39/20))
    {y : ℝ} (hy : 54≤|y|) {n : ℕ}
    (hn : n∈(completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime)) :
    ‖joinedCoefficient u N n-prefixCoefficient u N n‖≤
      3*log n*exp (-(N : ℝ)/1250) := by
  obtain ⟨⟨p,q,hp,hq,hpq,rfl⟩,hl,hh⟩ := retained_pair_data hu hU hN hy hn
  obtain ⟨hlarge,hco,_⟩ := canonical_pair hp hq hpq
  have hlog : log (p*q : ℕ)=log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  have hwide : (39/20 : ℝ)*N<log p+log q ∧ log p+log q≤(203/100 : ℝ)*N := by
    rw [hlog] at hl hh
    constructor <;> nlinarith only [hl,hh,hNr]
  rw [joinedCoefficient_eq_log hu hU hN hp hq hpq hwide hCube,
    prefixCoefficient,hlarge,hco,sub_sub_sub_cancel_right,←Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs,hlog]
  apply joined_sub_prefix_log_bound (by omega) (log_natCast_nonneg p)
    (log_natCast_nonneg q) (log_le_log (by exact_mod_cast hq.pos)
      (by exact_mod_cast hpq.le)) (by simpa only [hlog] using hl)
        (by simpa only [hlog] using hh)
        (ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith) hU)
  have h := length_upper hu (by omega : 2≤N)
  nlinarith only [h,Nat.cast_nonneg (α:=ℝ) N]

open ZetaRieszCentralRadialCost

/-- Exact conversion of the coefficient-error mass to the already
summed integer factorial mass; the true complex phase is still in the main. -/
theorem log_kernel_radial (N n : ℕ) (hn : 0<n) (y : ℝ) :
    log n*‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖=
      (N+1 : ℕ)*radial (N+1) (log n)/(n : ℝ) := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  have he : exp (-(3/2 : ℝ)*log n)=exp (-log n/2)/(n : ℝ) := by
    have hi : exp (-log n)=(n : ℝ)⁻¹ := by rw [exp_neg,exp_log hn0]
    calc
      _ = exp (-log n/2)*exp (-log n) := by rw [←exp_add]; congr 1; ring
      _ = _ := by simp only [hi,div_eq_mul_inv]
  rw [norm_zetaPrimeLogKernel]
  have hs : (3/2+Complex.I*(y : ℂ)).re=(3/2 : ℝ) := by simp
  rw [hs,zetaPrimeExpWeight,he]
  unfold radial
  rw [Nat.factorial_succ,pow_succ]
  push_cast
  field_simp

/-- A uniform error budget with explicit geometric saving AFTER source
normalisation. This is only the comparison error, not a bound on the main. -/
def prefixBudget (N : ℕ) : ℝ := 12*exp 2*((N : ℝ)+1)*exp (-(N : ℝ)/1600)

theorem prefixBudget_nonneg (N : ℕ) : 0≤prefixBudget N := by
  unfold prefixBudget
  positivity

private theorem source_rate_bound {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    (2*u)^(N+1)*exp (-(N : ℝ)/1250)≤2*exp (-(N : ℝ)/1600) := by
  have hu0 : 0≤2*u := by linarith
  have hbase : 2*u≤exp (1/10000 : ℝ) := by
    have h := add_one_le_exp (1/10000 : ℝ)
    unfold ZetaRieszWideOwnerAudit.radiusCeiling at hU
    linarith
  have hpow := pow_le_pow_left₀ hu0 hbase (N+1)
  rw [←exp_nat_mul] at hpow
  have hmul := mul_le_mul_of_nonneg_right hpow (exp_pos (-(N : ℝ)/1250)).le
  rw [←exp_add] at hmul
  have hrate : ((N+1 : ℕ) : ℝ)*(1/10000)-(N : ℝ)/1250≤
      (1/10000 : ℝ)-(N : ℝ)/1600 := by
    push_cast
    nlinarith only [Nat.cast_nonneg (α:=ℝ) N]
  have hconst : exp (1/10000 : ℝ)≤2 := by
    calc
      _ ≤ exp (log 2) := exp_le_exp.mpr (by linarith [log_two_gt_d9])
      _ = _ := exp_log (by norm_num)
  calc
    _ ≤ exp ((1/10000 : ℝ)-(N : ℝ)/1600) := hmul.trans
      (exp_le_exp.mpr (by simpa only [sub_eq_add_neg,neg_div] using hrate))
    _ = exp (1/10000 : ℝ)*exp (-(N : ℝ)/1600) := by
      rw [sub_eq_add_neg,exp_add,neg_div]
    _ ≤ _ := mul_le_mul_of_nonneg_right hconst (exp_pos _).le

theorem prefixBudget_tendsto : Tendsto prefixBudget atTop (𝓝 0) := by
  have h := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1
    (exp_pos (-(1/1600 : ℝ))) (exp_lt_one_iff.mpr (by norm_num : -(1/1600 : ℝ)<0))).const_mul
      (12*exp 2)
  simp only [pow_one,mul_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have he : (exp (-(1/1600 : ℝ)))^N=exp (-(N : ℝ)/1600) := by
    rw [←exp_nat_mul]
    congr 1
    ring
  simp only [he,prefixBudget,mul_assoc]

/-- A fixed exponential coefficient saving pays the WHOLE finite sum
using a summed radial mass, not a population maximum or prime density. -/
theorem source_scaled_coefficient_error_bound {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) (y : ℝ)
    (S : Finset ℕ) (hS : ∀ n∈S,0<n) (a b : ℕ→ℂ)
    (hab : ∀ n∈S,‖a n-b n‖≤3*log n*exp (-(N : ℝ)/1250)) :
    ‖(u : ℂ)^(N+1)*∑ n∈S,(a n-b n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤
      prefixBudget N := by
  have hu0 : 0≤u := by linarith
  let E := exp (-(N : ℝ)/1250)
  have hE : 0≤E := (exp_pos _).le
  have hsum : ‖∑ n∈S,(a n-b n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖≤
      3*E*((N+1 : ℕ) : ℝ)*(exp 2*2^(N+2)) := by
    calc
      _ ≤ ∑ n∈S,‖(a n-b n)*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ := norm_sum_le _ _
      _ ≤ ∑ n∈S,3*E*(log n*‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul]
        simpa only [E,mul_assoc,mul_left_comm,mul_comm] using
          mul_le_mul_of_nonneg_right (hab n hn)
            (norm_nonneg (zetaPrimeLogKernel N (3/2+Complex.I*y) n))
      _ = 3*E*((N+1 : ℕ) : ℝ)*∑ n∈S,radial (N+1) (log n)/(n : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [log_kernel_radial N n (hS n hn) y]
        ring
      _ ≤ 3*E*((N+1 : ℕ) : ℝ)*
          ∑ n∈Finset.Icc 1 (S.sup id),radial (N+1) (log n)/(n : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          exact Finset.mem_Icc.mpr ⟨hS n hn,Finset.le_sup (f:=id) hn⟩
        · intro n _ _
          unfold radial
          positivity
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (ZetaRieszSignedDensityMain.radial_integer_mass (N+1) (S.sup id)) (by positivity)
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu0]
  calc
    _ ≤ u^(N+1)*(3*E*((N+1 : ℕ) : ℝ)*(exp 2*2^(N+2))) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg hu0 _)
    _ = 6*exp 2*((N : ℝ)+1)*((2*u)^(N+1)*exp (-(N : ℝ)/1250)) := by
      dsimp [E]
      rw [mul_pow,show N+2=(N+1)+1 by omega,pow_succ]
      push_cast
      ring
    _ ≤ 6*exp 2*((N : ℝ)+1)*(2*exp (-(N : ℝ)/1600)) :=
      mul_le_mul_of_nonneg_left (source_rate_bound hu hU N) (by positivity)
    _ = _ := by unfold prefixBudget; ring

/-- The existing large-order threshold also makes every head cofactor
rough. This removes an eventual auxiliary premise from the explicit bound. -/
theorem cube_below_core {N : ℕ} (hN : 65536≤N) {c : ℝ}
    (hc : c≤(4/3 : ℝ)*N) : N^3≤coreFloor N c (39/20) := by
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hp := mul_le_mul_of_nonneg_right (show (384 : ℝ)≤N by linarith)
    (pow_nonneg hN0 3)
  have hpoly : (N : ℝ)^3≤((N : ℝ)/2)^4/((4 : ℕ).factorial : ℝ) := by
    norm_num
    nlinarith only [hp]
  have he := pow_div_factorial_le_exp ((N : ℝ)/2) (by positivity) 4
  have hf := (coreFloor_geometry (by omega : 64≤N) hc).2.2.1
  exact_mod_cast (hpoly.trans he).trans hf

/-- The mask discrepancy is paid on the ACTUAL retained signed defect,
globally over all distinct pairs. No exposed-zero hypothesis is used. -/
theorem norm_literalPairDefect_sub_prefix_le {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N)
    {y : ℝ} (hy : 54≤|y|) :
    ‖literalPairDefect u y N-prefixPairDefect u y N‖≤prefixBudget N := by
  have hCube : ∀ c : ℝ,c≤(4/3 : ℝ)*N → N^3≤coreFloor N c (39/20) :=
    fun _ hc => cube_below_core hN hc
  let S := (completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime)
  have hS : ∀ n∈S,0<n := by
    intro n hn
    obtain ⟨⟨p,q,hp,hq,_,rfl⟩,_⟩ := retained_pair_data hu hU hN hy hn
    exact Nat.mul_pos hp.pos hq.pos
  have he : literalPairDefect u y N-prefixPairDefect u y N=
      (u : ℂ)^(N+1)*∑ n∈S,(joinedCoefficient u N n-prefixCoefficient u N n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
    rw [literalPairDefect_eq_nonprime hu hU hN]
    unfold prefixPairDefect selbergDefect
    rw [←mul_sub,←Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he]
  exact source_scaled_coefficient_error_bound hu hU N y S hS
    (joinedCoefficient u N) (prefixCoefficient u N)
      (fun _ hn => joined_sub_prefixCoefficient_bound hu hU hN hCube hy hn)

theorem eventually_norm_literalPairDefect_sub_prefix_le {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ N : ℕ in atTop,
      ‖literalPairDefect u y N-prefixPairDefect u y N‖≤prefixBudget N := by
  filter_upwards [eventually_ge_atTop (65536 : ℕ)] with N hN
  exact norm_literalPairDefect_sub_prefix_le hu hU hN hy

/-- Independent geometric decay of the global owner-mask error. The
selected signed resonance is preserved exactly in `prefixPairDefect`. -/
theorem tendsto_literalPairDefect_sub_prefix {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun N => literalPairDefect u y N-prefixPairDefect u y N) atTop (𝓝 0) := by
  exact squeeze_zero_norm' (eventually_norm_literalPairDefect_sub_prefix_le hu hU hy)
    prefixBudget_tendsto

/-- Direct signed upper transfer, at a quantified cost that tends to
zero. The prefix sum is not normed and no arithmetic estimate is assumed. -/
theorem eventually_pairDefect_re_le_prefix {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ N : ℕ in atTop,
      (literalPairDefect u y N).re≤(prefixPairDefect u y N).re+prefixBudget N := by
  filter_upwards [eventually_norm_literalPairDefect_sub_prefix_le hu hU hy] with N hN
  have h := (abs_le.mp ((Complex.abs_re_le_norm
    (literalPairDefect u y N-prefixPairDefect u y N)).trans hN)).2
  simp only [Complex.sub_re] at h
  linarith only [h]

/-- Reverse signed transfer: the global comparison did not discard a
favourable phase or spend either main term's source. -/
theorem eventually_prefix_re_le_pairDefect {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ N : ℕ in atTop,
      (prefixPairDefect u y N).re≤(literalPairDefect u y N).re+prefixBudget N := by
  filter_upwards [eventually_norm_literalPairDefect_sub_prefix_le hu hU hy] with N hN
  have h := (abs_le.mp ((Complex.abs_re_le_norm
    (literalPairDefect u y N-prefixPairDefect u y N)).trans hN)).1
  simp only [Complex.sub_re] at h
  linarith only [h]

open ZetaRieszPrimeCountFrequency

/-- Spend the geometric mask payment in the ORIGINAL whole-core floor
ledger, retaining the explicit previously proved Selberg budget once. -/
theorem eventually_native_prefix_floor {u C : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (hC : 1≤C)
    (ha : ∀ k,‖(u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C) :
    ∀ᶠ j in atTop,
      -(prefixPairDefect u y (dyadicMomentOrder j)).re-
        (nativeSelbergBudget u y C j+prefixBudget (dyadicMomentOrder j))≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_budgeted_pairDefect_floor hu hU hy hC ha,
    tendsto_dyadicMomentOrder.eventually (eventually_pairDefect_re_le_prefix hu.le hU hy)]
      with j hfloor hprefix
  linarith only [hfloor,hprefix]

/-- Cofinal native-order payment: a fixed geometric error, not another
polynomial improvement to an exponentially growing majorant. -/
theorem tendsto_native_pairDefect_sub_prefix {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun j => literalPairDefect u y (dyadicMomentOrder j)-
      prefixPairDefect u y (dyadicMomentOrder j)) atTop (𝓝 0) :=
  (tendsto_literalPairDefect_sub_prefix hu hU hy).comp tendsto_dyadicMomentOrder

/-- Under the simple exposed hypothesis, BOTH prior Selberg payment and
new global owner-mask payment have proved vanishing budgets in the original
floor. Only the signed prefix upper bound is left as an arithmetic target. -/
theorem exists_native_prefix_payment_simple (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hm : analyticZetaZeroMultiplicity rho=1)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) :
    ∃ C : ℝ,1≤C ∧
      Tendsto (fun j => nativeSelbergBudget (3/2-rho.1.re) rho.1.im C j+
        prefixBudget (dyadicMomentOrder j)) atTop (𝓝 0) ∧
      ∀ᶠ j in atTop,
        -(prefixPairDefect (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)).re-
          (nativeSelbergBudget (3/2-rho.1.re) rho.1.im C j+
            prefixBudget (dyadicMomentOrder j))≤
        (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse
          (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)
            (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  obtain ⟨C,hC,hcost,hfloor⟩ := exists_native_pairDefect_payment_simple
    rho hrho hexposed hm hU hy
  have hu : 1/2≤3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  refine ⟨C,hC,?_,?_⟩
  · simpa only [add_zero,Function.comp_def] using
      hcost.add (prefixBudget_tendsto.comp tendsto_dyadicMomentOrder)
  · filter_upwards [hfloor,tendsto_dyadicMomentOrder.eventually
      (eventually_pairDefect_re_le_prefix hu hU hy)] with j hj hp
    linarith only [hj,hp]

end RiemannGaussian.ZetaRieszPairPrefixPayment

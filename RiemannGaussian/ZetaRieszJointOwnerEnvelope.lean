/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszClippedAllocationPayment
import RiemannGaussian.ZetaArithmeticLocalEnergy

/-!
# A joint radial and owner-allocation saving

The upper missing allocation tail is tilted before its radial factorial
kernel is bounded. Its exact shifted saddle pays every original owner
with log(p)>=243N/200. No count, phase, cofactor or endpoint is completed.
The smaller owners remain signed in the same whole-carrier floor ledger.
-/

noncomputable section
open Filter Topology Real MeasureTheory Set
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszJointOwnerEnvelope
open ZetaRieszFreeRadialRows ZetaRieszCanonicalOwnerRows
open ZetaRieszSaturatedRowFloor ZetaRieszUnsignedDivisorError
open ZetaRieszOwnerMaximal ZetaRieszJointAllocation
open ZetaRieszClippedAllocationPayment

private theorem joint_tilt_log :
    (1/10000 : ℝ)+(19/32 : ℝ)*log (41/40 : ℝ)-243/16400 ≤ -(1/20000) := by
  have hq : log (41/40 : ℝ) ≤ 247/10000 := by
    apply (log_le_iff_le_exp (by norm_num : (0 : ℝ)<41/40)).mpr
    have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤247/10000) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  linarith

/-- The literal tilted factorial kernel shifts its radial saddle by P/41.
Bounding the allocation and radial factors separately loses this saving. -/
theorem tilted_radial_identity (N : ℕ) {P T : ℝ} (hT : T ≠ 0) :
    ((41/40 : ℝ)*(1-P/T)+(1-(1-P/T)))^(N+1)*radialMoment N T =
      (41/40 : ℝ)^(N+1)*exp (-P/82)*radialMoment N (T-P/41) := by
  have hf : ((41/40 : ℝ)*(1-P/T)+(1-(1-P/T)))*T=
      (41/40 : ℝ)*(T-P/41) := by field_simp; ring
  unfold radialMoment
  rw [show -T/2=-P/82+(-(T-P/41)/2) by ring,exp_add]
  rw [show ((41/40 : ℝ)*(1-P/T)+(1-(1-P/T)))^(N+1)*
      (exp (-P/82)*exp (-(T-P/41)/2)*T^(N+1)/(N.factorial : ℝ)) =
        (exp (-P/82)*exp (-(T-P/41)/2)/(N.factorial : ℝ))*
          (((41/40 : ℝ)*(1-P/T)+(1-(1-P/T)))*T)^(N+1) by rw [mul_pow]; ring,
    hf,mul_pow]
  ring

private theorem missing_joint_bound {N : ℕ} (hN : 320 ≤ N) {x : ℝ}
    (hx : (7/20 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    ownerWeight N x ≤
      exp (-(13/32 : ℝ)*N*log (41/40 : ℝ))*
        ((41/40 : ℝ)*x+(1-x))^(N+1)+
      exp (((N : ℝ)/5+1)*log (5/4 : ℝ))*(93/100 : ℝ)^(N+1) := by
  have hx0 : 0 ≤ x := by linarith
  have ht : 0 ≤ log (41/40 : ℝ) := log_nonneg (by norm_num)
  have hl : 0 ≤ log (5/4 : ℝ) := log_nonneg (by norm_num)
  have hm := missed_mass_bound N hN hx0 hx1
    (exp_pos (-(13/32 : ℝ)*N*log (41/40 : ℝ))).le
    (exp_pos (((N : ℝ)/5+1)*log (5/4 : ℝ))).le
    (by norm_num : (0 : ℝ)≤41/40) (by norm_num : (0 : ℝ)≤4/5) (by
      intro k hk hcut
      have hc : (13/32 : ℝ)*N ≤ k := by
        have hh : 13*(N : ℝ)<32*k := by exact_mod_cast (by omega : 13*N<32*k)
        linarith
      rw [← exp_log (by norm_num : (0 : ℝ)<41/40),← exp_nat_mul,← exp_add]
      apply one_le_exp_iff.mpr
      simp only [log_exp]
      nlinarith [mul_le_mul_of_nonneg_right hc ht]) (by
      intro k hk hcut
      have hkN : k ≤ N+1 := by have := Finset.mem_range.mp hk; omega
      have hc : (k : ℝ) ≤ (N : ℝ)/5+1 := by
        have hh : 5*(k : ℝ) ≤ N+5 := by exact_mod_cast (by omega : 5*k ≤ N+5)
        linarith
      rw [show (4/5 : ℝ)=exp (-log (5/4 : ℝ)) by
        rw [exp_neg,exp_log (by norm_num : (0 : ℝ)<5/4)]; norm_num,
        ← exp_nat_mul,← exp_add]
      apply one_le_exp_iff.mpr
      nlinarith [mul_le_mul_of_nonneg_right hc hl])
  have hlo : (4/5 : ℝ)*x+(1-x) ≤ 93/100 := by linarith
  exact hm.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hlo (N+1)) (exp_pos _).le))

/-- The source-normalized joint rate; its strict exponential saving is
uniform throughout the restricted radius interval. -/
def jointRate : ℝ := exp (-(1/20000 : ℝ))

/-- The joint payment has a strict geometric margin. -/
theorem jointRate_bounds : 0 < jointRate ∧ jointRate < 1 := by
  exact ⟨exp_pos _,exp_lt_one_iff.mpr (by norm_num)⟩

private theorem upper_joint_envelope {u P T : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ}
    (hP : (243/200 : ℝ)*N ≤ P) (hPT : P ≤ T) (hT : 0 < T) :
    u^(N+1)*exp (-(13/32 : ℝ)*N*log (41/40 : ℝ))*
        ((41/40 : ℝ)*(1-P/T)+(1-(1-P/T)))^(N+1)*radialMoment N T ≤
      2*((N : ℝ)+1)*jointRate^N := by
  have hP0 : 0 ≤ P := le_trans (by positivity) hP
  have hV : 0 ≤ T-P/41 := by linarith
  have hnorm : u^(N+1)*exp (-(13/32 : ℝ)*N*log (41/40 : ℝ))*
      ((41/40 : ℝ)*(1-P/T)+(1-(1-P/T)))^(N+1)*radialMoment N T =
        (u^(N+1)*exp (-(13/32 : ℝ)*N*log (41/40 : ℝ)))*
          (((41/40 : ℝ)*(1-P/T)+(1-(1-P/T)))^(N+1)*radialMoment N T) := by ring
  rw [hnorm,tilted_radial_identity N hT.ne']
  have hb := mul_le_mul_of_nonneg_left (radialMoment_le N hV)
    (by positivity : 0 ≤ (41/40 : ℝ)^(N+1)*exp (-P/82))
  apply (mul_le_mul_of_nonneg_left hb (by positivity :
    0 ≤ u^(N+1)*exp (-(13/32 : ℝ)*N*log (41/40 : ℝ)))).trans
  have hPexp : exp (-P/82) ≤ exp (-(243/16400 : ℝ)*N) :=
    exp_le_exp.mpr (by linarith)
  have h2u : 2*u ≤ exp (1/10000 : ℝ) := by
    have h := add_one_le_exp (1/10000 : ℝ)
    have hU' : u ≤ (10001/20000 : ℝ) := hU
    linarith
  have hqpow : (41/40 : ℝ)^N=exp ((N : ℝ)*log (41/40 : ℝ)) := by
    rw [exp_nat_mul,exp_log (by norm_num : (0 : ℝ)<41/40)]
  have heq : (u^(N+1)*exp (-(13/32 : ℝ)*N*log (41/40 : ℝ)))*
      ((41/40 : ℝ)^(N+1)*exp (-P/82)*radialEnvelope N) =
        (2*u*(41/40)*((N : ℝ)+1))*((2*u)^N*(41/40 : ℝ)^N*
          exp (-(13/32 : ℝ)*N*log (41/40 : ℝ))*exp (-P/82)) := by
    unfold radialEnvelope
    rw [pow_succ,pow_succ,pow_succ,mul_pow]
    ring
  rw [heq]
  have hf : 2*u*(41/40)*((N : ℝ)+1) ≤ 2*((N : ℝ)+1) := by
    have hU' : u ≤ (10001/20000 : ℝ) := hU
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hr : (2*u)^N*(41/40 : ℝ)^N*
      exp (-(13/32 : ℝ)*N*log (41/40 : ℝ))*exp (-P/82) ≤ jointRate^N := by
    calc
      _ ≤ (exp (1/10000 : ℝ))^N*(41/40 : ℝ)^N*
          exp (-(13/32 : ℝ)*N*log (41/40 : ℝ))*exp (-(243/16400 : ℝ)*N) := by
        gcongr
      _ = exp ((N : ℝ)*((1/10000 : ℝ)+(19/32 : ℝ)*log (41/40 : ℝ)-243/16400)) := by
        rw [← exp_nat_mul,hqpow,← exp_add,← exp_add,← exp_add]
        congr 1
        ring
      _ ≤ exp ((N : ℝ)*(-(1/20000 : ℝ))) :=
        exp_le_exp.mpr (mul_le_mul_of_nonneg_left joint_tilt_log (Nat.cast_nonneg (α := ℝ) N))
      _ = _ := by rw [jointRate,exp_nat_mul]
  exact mul_le_mul hf hr (by positivity) (by positivity)

private theorem lower_joint_envelope {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    u^(N+1)*exp (((N : ℝ)/5+1)*log (5/4 : ℝ))*
        (93/100 : ℝ)^(N+1)*radialEnvelope N ≤
      4*((N : ℝ)+1)*jointRate^N := by
  have hl : log (93/100 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ) ≤ -(1/600) := by
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<93/100),log_tilt_bounds.2]
  have h2u : 2*u ≤ exp (1/10000 : ℝ) := by
    have h := add_one_le_exp (1/10000 : ℝ)
    have hU' : u ≤ (10001/20000 : ℝ) := hU
    linarith
  have hlog : (1/10000 : ℝ)+log (93/100 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ) ≤ -(1/20000) := by
    linarith
  have heq : u^(N+1)*exp (((N : ℝ)/5+1)*log (5/4 : ℝ))*
      (93/100 : ℝ)^(N+1)*radialEnvelope N =
        (2*u*(5/4)*(93/100)*((N : ℝ)+1))*
          ((2*u)^N*exp ((N : ℝ)*(log (93/100 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ)))) := by
    have hp : (93/100 : ℝ)^N=exp ((N : ℝ)*log (93/100 : ℝ)) := by
      rw [exp_nat_mul,exp_log (by norm_num : (0 : ℝ)<93/100)]
    unfold radialEnvelope
    rw [pow_succ,pow_succ,mul_pow,show ((N : ℝ)/5+1)*log (5/4 : ℝ)=
      log (5/4 : ℝ)+(N : ℝ)/5*log (5/4 : ℝ) by ring,exp_add,
      exp_log (by norm_num : (0 : ℝ)<5/4),hp,
      show (N : ℝ)*(log (93/100 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ))=
        (N : ℝ)*log (93/100 : ℝ)+(N : ℝ)/5*log (5/4 : ℝ) by ring,exp_add]
    ring
  rw [heq]
  have hf : 2*u*(5/4)*(93/100)*((N : ℝ)+1) ≤ 4*((N : ℝ)+1) := by
    have hU' : u ≤ (10001/20000 : ℝ) := hU
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hr : (2*u)^N*exp ((N : ℝ)*(log (93/100 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ))) ≤ jointRate^N := by
    calc
      _ ≤ (exp (1/10000 : ℝ))^N*exp ((N : ℝ)*(log (93/100 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ))) := by
        gcongr
      _ = exp ((N : ℝ)*((1/10000 : ℝ)+log (93/100 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ))) := by
        rw [← exp_nat_mul,← exp_add]
        congr 1
        ring
      _ ≤ exp ((N : ℝ)*(-(1/20000 : ℝ))) :=
        exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) N))
      _ = _ := by rw [jointRate,exp_nat_mul]
  exact mul_le_mul hf hr (by positivity) (by positivity)

/-- The complete original owner allocation and radial kernel have one
joint exponential bound. No height, count or cutoff approximation enters. -/
theorem source_scaled_owner_radial_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 320 ≤ N)
    {P T : ℝ} (hP : (243/200 : ℝ)*N ≤ P) (hPT : P ≤ (13/20 : ℝ)*T)
    (hT : 0 < T) :
    u^(N+1)*ownerWeight N (1-P/T)*radialMoment N T ≤
      6*((N : ℝ)+1)*jointRate^N := by
  have hP0 : 0 ≤ P := le_trans (by positivity) hP
  have hx : (7/20 : ℝ) ≤ 1-P/T := by
    have h := (div_le_iff₀ hT).mpr hPT
    linarith
  have hx1 : 1-P/T ≤ 1 := by linarith [div_nonneg hP0 hT.le]
  have hm := mul_le_mul_of_nonneg_right (missing_joint_bound hN hx hx1)
    (radialMoment_nonneg N hT.le)
  have hm' := mul_le_mul_of_nonneg_left hm (pow_nonneg hu (N+1))
  have hhi := upper_joint_envelope hu hU hP (by linarith) hT
  have hlo := mul_le_mul_of_nonneg_left (radialMoment_le N hT.le)
    (by positivity : 0 ≤ u^(N+1)*exp (((N : ℝ)/5+1)*log (5/4 : ℝ))*(93/100 : ℝ)^(N+1))
  have hlo' := lower_joint_envelope hu hU N
  nlinarith only [hm',hhi,hlo,hlo']

/-- A signed physical atom inherits the joint saving while retaining its
full phase. It holds uniformly for every real ordinate. -/
theorem source_scaled_physicalWeight_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 320 ≤ N)
    {P T : ℝ} (hP : (243/200 : ℝ)*N ≤ P) (hPT : P ≤ (13/20 : ℝ)*T)
    (hT : 0 < T) (y : ℝ) :
    |u^(N+1)*physicalWeight N P y T| ≤ 6*((N : ℝ)+1)*jointRate^N := by
  have hP0 : 0 ≤ P := le_trans (by positivity) hP
  have hx : 0 ≤ 1-P/T := by
    have hh : P/T ≤ 1 := (div_le_iff₀ hT).mpr (by linarith)
    linarith
  have hx1 : 1-P/T ≤ 1 := by linarith [div_nonneg hP0 hT.le]
  have hw := (ownerWeight_bounds N hx hx1).1
  rw [physicalWeight,abs_mul,abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hu _),
    abs_of_nonneg hw,abs_of_nonneg (radialMoment_nonneg N hT.le)]
  have hb := mul_le_of_le_one_right
    (mul_nonneg (pow_nonneg hu (N+1)) (mul_nonneg hw (radialMoment_nonneg N hT.le)))
    (abs_cos_le_one (y*T))
  calc
    _ ≤ u^(N+1)*ownerWeight N (1-P/T)*radialMoment N T := by
      nlinarith only [hb]
    _ ≤ _ := source_scaled_owner_radial_bound hu hU hN hP hPT hT

/-- Only rows not previously paid are selected. This payment cannot
spend either the full-window or the earlier owner-boundary credit twice. -/
def jointRows (u : ℝ) (N : ℕ) : Finset (ℕ×ℕ) :=
  (residualRows u N).filter (fun pb => (243/200 : ℝ)*N ≤ log pb.1)

private theorem residual_row_mem {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ residualRows u N) : pb ∈ rows u N :=
  (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).1

private theorem joint_row_mem {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (h : pb ∈ jointRows u N) : pb ∈ rows u N :=
  residual_row_mem (Finset.mem_filter.mp h).1

private theorem joint_atom_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N d : ℕ} (hN : 320 ≤ N)
    {pb : ℕ×ℕ} (hpb : pb ∈ jointRows u N)
    (hd : d ∈ Finset.Ioc (lower N pb.1 pb.2)
      (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)) (y : ℝ) :
    |u^(N+1)*physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)| ≤
      6*((N : ℝ)+1)*jointRate^N := by
  obtain ⟨hp,hb,hs,hpd,hmax,hH,hM,hlo,hhi,hsat,hshare⟩ := rows_geometry (joint_row_mem hpb)
  have hd' := Finset.mem_Ioc.mp hd
  have hdl : log (lower N pb.1 pb.2) ≤ log d :=
    log_le_log (by exact_mod_cast hM) (by exact_mod_cast hd'.1.le)
  have hn : (320 : ℝ)≤N := by exact_mod_cast hN
  have hT : 0 < log (pb.1*pb.2 : ℕ)+log d := by linarith
  apply source_scaled_physicalWeight_bound hu hU hN (Finset.mem_filter.mp hpb).2
    (by linarith) hT y

private theorem row_reciprocal_bound {u : ℝ} {N : ℕ} {pb : ℕ×ℕ} (hpb : pb ∈ rows u N) :
    (∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
      (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2), (d : ℝ)⁻¹) ≤
        1+(203/100 : ℝ)*N := by
  have hg := rows_geometry hpb
  have hMX := (Finset.mem_filter.mp hpb).2.2.2.2.2
  have hM := hg.2.2.2.2.2.2.1
  have hX := hM.trans_le hMX
  have hs : Finset.Ioc (lower N pb.1 pb.2)
      (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2) ⊆
        Finset.Icc 1 (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2) := by
    intro d hd
    have hd' := Finset.mem_Ioc.mp hd
    exact Finset.mem_Icc.mpr ⟨by omega,hd'.2⟩
  have hh := harmonic_le_one_add_log (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)
  rw [harmonic_eq_sum_Icc,Rat.cast_sum] at hh
  push_cast at hh
  have hlog : log (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2) ≤ (203/100 : ℝ)*N := by
    have hhi := hg.2.2.2.2.2.2.2.2.1
    linarith [log_natCast_nonneg (pb.1*pb.2)]
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)).trans
    (hh.trans (add_le_add_right hlog 1))

/-- The original signed integer row, including its actual moving endpoints,
inherits the joint tilt. No lattice or prime-count completion is required. -/
theorem source_scaled_joint_row_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 320 ≤ N)
    {pb : ℕ×ℕ} (hpb : pb ∈ jointRows u N) (y : ℝ) :
    |u^(N+1)*(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
      (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2),
        physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))| ≤
      6*((N : ℝ)+1)*jointRate^N*(1+(203/100 : ℝ)*N) := by
  rw [Finset.mul_sum]
  have hb d (hd : d ∈ Finset.Ioc (lower N pb.1 pb.2)
      (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)) :
      |u^(N+1)*(physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))| ≤
        (6*((N : ℝ)+1)*jointRate^N)*(d : ℝ)⁻¹ := by
    rw [← mul_div_assoc,abs_div,abs_of_nonneg (a := (d : ℝ)) (Nat.cast_nonneg d),div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (joint_atom_bound hu hU hN hpb hd y) (by positivity)
  have hs := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb)
  calc
    _ ≤ ∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2),
        (6*((N : ℝ)+1)*jointRate^N)*(d : ℝ)⁻¹ := hs
    _ = (6*((N : ℝ)+1)*jointRate^N)*
        (∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
          (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2), (d : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (row_reciprocal_bound (joint_row_mem hpb))
      (by positivity [jointRate_bounds.1])

/-- This is the unchanged signed density sum on the newly paid owner band. -/
def jointDensityMain (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ pb ∈ jointRows u N,
    densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
      (lower N pb.1 pb.2) (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)

/-- All owner rows, prime counts and radial periods share one budget. -/
def jointErrorBudget (N : ℕ) : ℝ := 162*((N : ℝ)+1)^4*jointRate^N

/-- The polynomial all-count cost preserves the joint exponential saving. -/
theorem tendsto_jointErrorBudget : Tendsto jointErrorBudget atTop (𝓝 0) := by
  change Tendsto (fun N => jointErrorBudget N) atTop (𝓝 0)
  simpa only [jointErrorBudget,mul_assoc,mul_zero] using
    (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 4
      jointRate_bounds.1 jointRate_bounds.2).const_mul 162

/-- The enlarged paid owner band is an independent whole signed-main
estimate, uniform in the ordinate and retaining every literal row mask. -/
theorem source_scaled_jointDensityMain_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 320 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) (y : ℝ) :
    |u^(N+1)*jointDensityMain u y N| ≤ jointErrorBudget N := by
  let Q := 6*((N : ℝ)+1)*jointRate^N*(1+(203/100 : ℝ)*N)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity [jointRate_bounds.1]
  have hb pb (hpb : pb ∈ jointRows u N) :
      |u^(N+1)*densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
        (lower N pb.1 pb.2) (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)| ≤
          (1 : ℝ)/(pb.1*pb.2 : ℕ)*Q := by
    rw [densityRow_physical]
    have hc := row_density_coefficient (by omega : 32 ≤ N) hL (joint_row_mem hpb)
    have hi := source_scaled_joint_row_bound hu hU hN hpb y
    calc
      _ = |((μ pb.2 : ℝ)*ZetaRieszSignedConvolution.pairHinge
          (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
          (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*
          density (pb.1*pb.2).primeFactors| *
            |u^(N+1)*(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
              (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2),
              physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ _ := mul_le_mul hc hi (abs_nonneg _) (by positivity)
  unfold jointDensityMain
  rw [Finset.mul_sum]
  have hs := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb)
  rw [← Finset.sum_mul] at hs
  have houter : (∑ pb ∈ jointRows u N, (1 : ℝ)/(pb.1*pb.2 : ℕ)) ≤
      (1+(203/100 : ℝ)*N)^2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (fun _ hp => joint_row_mem hp)
      (fun _ _ _ => by positivity)).trans (rows_outer_harmonic_bound u N)
  apply (hs.trans (mul_le_mul_of_nonneg_right houter hQ)).trans
  have hbase : 1+(203/100 : ℝ)*N ≤ 3*((N : ℝ)+1) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hp := pow_le_pow_left₀ (by positivity) hbase 3
  calc
    _ = 6*((N : ℝ)+1)*(1+(203/100 : ℝ)*N)^3*jointRate^N := by dsimp [Q]; ring
    _ ≤ 6*((N : ℝ)+1)*(3*((N : ℝ)+1))^3*jointRate^N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity))
        (pow_nonneg jointRate_bounds.1.le N)
    _ = _ := by unfold jointErrorBudget; ring

/-- No exposed-zero or prime-phase hypothesis enters this decay theorem. -/
theorem tendsto_source_scaled_jointDensityMain {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun N => u^(N+1)*jointDensityMain u y N) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := jointErrorBudget) ?_ tendsto_jointErrorBudget
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hl,eventually_ge_atTop (320 : ℕ)] with N hL hN
  rw [Real.norm_eq_abs]
  exact source_scaled_jointDensityMain_bound (by linarith) hU hN (by nlinarith only [hL]) y

/-- Remaining original density rows after all three disjoint payments. -/
def lowOwnerRows (u : ℝ) (N : ℕ) : Finset (ℕ×ℕ) := residualRows u N \ jointRows u N

/-- All signs, original moving endpoints and counts remain in this sum. -/
def lowOwnerDensityMain (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ pb ∈ lowOwnerRows u N,
    densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
      (lower N pb.1 pb.2) (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)

/-- The upper-owner threshold is strictly lowered in the unpaid main.
The unsigned and saturation crossings are still retained with their signs. -/
theorem lowOwner_row_boundary {u : ℝ} {N : ℕ} {pb : ℕ×ℕ} (h : pb ∈ lowOwnerRows u N) :
    log pb.1 < (243/200 : ℝ)*N ∧
      ((37/20 : ℝ)*N < log (pb.1*pb.2 : ℕ) ∨
        log pb.1+SquarefreeVaughanLogSource.length u N < (203/100 : ℝ)*N) := by
  obtain ⟨hr,hj⟩ := Finset.mem_sdiff.mp h
  refine ⟨?_,(residual_row_boundary hr).2⟩
  by_contra hn
  exact hj (Finset.mem_filter.mpr ⟨hr,le_of_not_gt hn⟩)

/-- The third signed row payment is disjoint from both earlier payments. -/
theorem residualDensityMain_eq_joint_lowOwner (u y : ℝ) (N : ℕ) :
    residualDensityMain u y N = jointDensityMain u y N+lowOwnerDensityMain u y N := by
  have hs : jointRows u N ⊆ residualRows u N := Finset.filter_subset _ _
  unfold residualDensityMain jointDensityMain lowOwnerDensityMain lowOwnerRows
  rw [← Finset.sum_sdiff hs]
  ring

/-- All previously proved costs plus the additional disjoint joint-tilt payment. -/
def lowOwnerErrorBudget (y : ℝ) (N : ℕ) : ℝ := residualErrorBudget y N+jointErrorBudget N

/-- No old error is charged again when the newly paid rows are removed. -/
theorem tendsto_lowOwnerErrorBudget (y : ℝ) : Tendsto (lowOwnerErrorBudget y) atTop (𝓝 0) := by
  change Tendsto (fun N => lowOwnerErrorBudget y N) atTop (𝓝 0)
  simpa only [lowOwnerErrorBudget,zero_add] using
    (tendsto_residualErrorBudget y).add tendsto_jointErrorBudget

/-- The final joined carrier retains only the smaller owners in its
unpaid density main. A numerical floor on this joint remainder is OPEN. -/
theorem eventually_joined_floor_with_lowOwner_rows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      u^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        (canonicalRemaining u y j-endpointRows u y j+
          lowOwnerDensityMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))-
        lowOwnerErrorBudget y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ≤
      ((u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re := by
  have hf := eventually_joined_floor_with_residual_rows hu hU hy
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hf,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hl,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (320 : ℕ))] with j hj hL hN
  have hb := (abs_le.mp (source_scaled_jointDensityMain_bound (by linarith) hU hN
    (by nlinarith only [hL]) y)).1
  rw [residualDensityMain_eq_joint_lowOwner] at hj
  unfold lowOwnerErrorBudget
  nlinarith only [hj,hb]

/-- The payment also applies to ORIGINAL finite labels, rather than only
their signed density rows. All other masks stay in the given set S. -/
def literalPopulation (S A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ 3 ≤ n.primeFactors.card ∧
    ZetaRieszPrimeEndpoint.largestPrime n ∈ A ∧
    (243/200 : ℝ)*N ≤ log (ZetaRieszPrimeEndpoint.largestPrime n) ∧
    log (ZetaRieszPrimeEndpoint.largestPrime n) ≤ (13/20 : ℝ)*log n)

private theorem norm_literal_atom {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 320 ≤ N)
    (S A : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (hn : n ∈ literalPopulation S A N) :
    ‖(u : ℂ)^(N+1)*residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (6*((N : ℝ)+1)*jointRate^N)*((n.divisors.card : ℝ)/(n : ℝ)) := by
  obtain ⟨_,hs,hc,hpA,hP,hshare⟩ := Finset.mem_filter.mp hn
  have ho := ZetaRieszJointPrimeEnergy.owner_data hs hc
  let p := ZetaRieszPrimeEndpoint.largestPrime n
  let a := ZetaRieszOwnedCells.ownerCofactor n
  have hp : p.Prime := ho.1
  have hpa : p*a=n := ho.2.1
  have ha : Squarefree a := ho.2.2.1
  have hac : 2 ≤ a.primeFactors.card := ho.2.2.2.1
  have hmax : ∀ q ∈ a.primeFactors, q < p := by
    intro q hq
    exact ho.2.2.2.2 q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
  have hpn : p ∈ n.primeFactors := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega)
  have hn1 : 1 < n := hp.one_lt.trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero)
    (Nat.dvd_of_mem_primeFactors hpn))
  have hnp : ¬n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
  have hf := ownerWeight_eq_fibre A N ha hac hp hmax hpA
  rw [hpa] at hf
  have hl : log a/log n=1-log p/log n := by
    have hlog : log n=log p+log a := by
      rw [← hpa,Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha.ne_zero)]
    have hd : log p+log a ≠ 0 := by
      rw [← hlog]
      exact (log_pos (by exact_mod_cast hn1)).ne'
    rw [hlog]
    field_simp
    ring
  rw [hl] at hf
  have hbA := ZetaRieszNonownerAllocation.boundedShare_owner_split A N n
  have hnowner := (boundedShare_bounds (A.erase p) N n).1
  have hW : 1-boundedShare A N n ≤ ownerWeight N (1-log p/log n) := by
    change boundedShare A N n=boundedShare (A ∩ {p}) N n+boundedShare (A.erase p) N n at hbA
    linarith
  have hW0 : 0 ≤ 1-boundedShare A N n := sub_nonneg.mpr (boundedShare_bounds A N n).2
  have hnR : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hs.ne_zero
  have hT : 0 < log n := log_pos (by exact_mod_cast hn1)
  have hx0 : 0 ≤ 1-log p/log n := by
    have h := (div_le_iff₀ hT).mpr hshare
    linarith
  have hx1 : 1-log p/log n ≤ 1 := by linarith [div_nonneg (log_natCast_nonneg p) hT.le]
  have hWnonneg := (ownerWeight_bounds N hx0 hx1).1
  have hcoef := (SquarefreeVaughanLogSource.norm_coefficient_le hL n).trans
    (zetaMoebiusLogMajorant_le_card_mul_log n)
  have hkernel : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ =
      exp (-(3/2 : ℝ)*log n)*(log n)^N/(N.factorial : ℝ) := by
    rw [norm_zetaPrimeLogKernel]
    norm_num [zetaPrimeExpWeight]
    ring
  have hnorm : ‖(u : ℂ)^(N+1)*residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ =
      u^(N+1)*(1-boundedShare A N n)*‖SquarefreeVaughanLogSource.coefficient L n‖*
        (exp (-(3/2 : ℝ)*log n)*(log n)^N/(N.factorial : ℝ)) := by
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu,
      residualCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hW0,hkernel]
    ring
  rw [hnorm]
  have hb := mul_le_mul
    (mul_le_mul_of_nonneg_left hW (pow_nonneg hu (N+1))) hcoef
    (norm_nonneg _) (mul_nonneg (pow_nonneg hu (N+1)) hWnonneg)
  have hb' := mul_le_mul_of_nonneg_right hb
    (by positivity : 0 ≤ exp (-(3/2 : ℝ)*log n)*(log n)^N/(N.factorial : ℝ))
  apply hb'.trans
  have he : exp (-(3/2 : ℝ)*log n)=exp (-log n/2)/(n : ℝ) := by
    rw [show -(3/2 : ℝ)*log n=-log n/2+(-log n) by ring,exp_add,exp_neg,exp_log hnR]
    ring
  calc
    _ = (u^(N+1)*ownerWeight N (1-log p/log n)*radialMoment N (log n))*
        ((n.divisors.card : ℝ)/(n : ℝ)) := by rw [he,radialMoment,pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (source_scaled_owner_radial_bound hu hU hN hP hshare hT) (by positivity)

/-- A literal all-count payment has one fixed summable arithmetic constant.
The small Rankin cost is paid from the joint exponential margin. -/
def literalErrorBudget (N : ℕ) : ℝ :=
  6*divisorSquareDirichletMass (1+1/262144)*((N : ℝ)+1)*exp (-(1/25000 : ℝ))^N

/-- The literal all-count norm budget decays independently of all zeros. -/
theorem tendsto_literalErrorBudget : Tendsto literalErrorBudget atTop (𝓝 0) := by
  change Tendsto (fun N => literalErrorBudget N) atTop (𝓝 0)
  simpa only [literalErrorBudget,pow_one,mul_assoc,mul_zero] using
    (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1
      (exp_pos (-(1/25000 : ℝ))) (exp_lt_one_iff.mpr (by norm_num))).const_mul
        (6*divisorSquareDirichletMass (1+1/262144))

/-- The joint owner/radial bound also permits the ORIGINAL prime selection
to depend on the label. This is needed for singleton canonical owners;
no exponential owner-count factor is introduced. -/
theorem source_scaled_variable_population_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 320 ≤ N)
    (D : Finset ℕ) (A : ℕ → Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (hD : ∀ n ∈ D, n ∈ literalPopulation D (A n) N)
    (hS : ∀ n ∈ D, log n ≤ (203/100 : ℝ)*N) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ D,
      residualCoefficient (A n) L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        literalErrorBudget N := by
  let Q := 6*((N : ℝ)+1)*jointRate^N
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity [jointRate_bounds.1]
  have hmajor n (hn : n ∈ D) : (n.divisors.card : ℝ)/(n : ℝ) ≤
      exp ((203/26214400 : ℝ)*N)*((n.divisors.card : ℝ)^2*(n : ℝ)^(-(1+1/262144 : ℝ))) := by
    have hs := (Finset.mem_filter.mp (hD n hn)).2.1
    have hnR : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hs.ne_zero
    have ht := hS n hn
    have hdc : (1 : ℝ)≤n.divisors.card := by
      exact_mod_cast Finset.one_le_card.mpr ⟨1,Nat.one_mem_divisors.mpr hs.ne_zero⟩
    have he : (n : ℝ)⁻¹ ≤ exp ((203/26214400 : ℝ)*N)*(n : ℝ)^(-(1+1/262144 : ℝ)) := by
      rw [rpow_def_of_pos hnR,← exp_log hnR,← exp_neg,← exp_add]
      simp only [log_exp]
      apply exp_le_exp.mpr
      linarith
    rw [div_eq_mul_inv]
    exact (mul_le_mul (by nlinarith : (n.divisors.card : ℝ)≤(n.divisors.card : ℝ)^2) he
      (inv_nonneg.mpr hnR.le) (sq_nonneg _)).trans_eq (by ring)
  rw [Finset.mul_sum]
  have hs : ‖∑ n ∈ D, (u : ℂ)^(N+1)*
      (residualCoefficient (A n) L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖ ≤
      ∑ n ∈ D, Q*(exp ((203/26214400 : ℝ)*N)*
        ((n.divisors.card : ℝ)^2*(n : ℝ)^(-(1+1/262144 : ℝ)))) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    simpa only [Q,mul_assoc] using
      (norm_literal_atom hu hU hN D (A n) hL y (hD n hn)).trans
        (mul_le_mul_of_nonneg_left (hmajor n hn) hQ)
  have hsum := (summable_card_divisors_sq_mul_rpow_neg
    (by norm_num : (1 : ℝ)<1+1/262144)).sum_le_tsum D (fun _ _ => by positivity)
  have hs' : ‖∑ n ∈ D, (u : ℂ)^(N+1)*
      (residualCoefficient (A n) L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)‖ ≤
      (Q*exp ((203/26214400 : ℝ)*N))*divisorSquareDirichletMass (1+1/262144) := by
    apply hs.trans
    calc
      _ = (Q*exp ((203/26214400 : ℝ)*N))*
          (∑ n ∈ D, (n.divisors.card : ℝ)^2*(n : ℝ)^(-(1+1/262144 : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  have hr : jointRate^N*exp ((203/26214400 : ℝ)*N) ≤ exp (-(1/25000 : ℝ))^N := by
    rw [jointRate,← exp_nat_mul,← exp_add,← exp_nat_mul]
    apply exp_le_exp.mpr
    have hn0 : (0 : ℝ)≤N := Nat.cast_nonneg N
    nlinarith only [hn0]
  apply hs'.trans
  calc
    _ = (6*divisorSquareDirichletMass (1+1/262144)*((N : ℝ)+1))*
        (jointRate^N*exp ((203/26214400 : ℝ)*N)) := by dsimp [Q]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr
      (by positivity [divisorSquareDirichletMass_nonneg (1+1/262144)])

/-- The WHOLE original signed prime sum on the enlarged owner population
has independent source-scale decay, with every additional mask retained. -/
theorem source_scaled_literal_population_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 320 ≤ N)
    (S A : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (hS : ∀ n ∈ S, log n ≤ (203/100 : ℝ)*N) :
    ‖(u : ℂ)^(N+1)*∑ n ∈ literalPopulation S A N,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
        literalErrorBudget N := by
  apply source_scaled_variable_population_bound hu hU hN
    (literalPopulation S A N) (fun _ => A) hL y
  · intro n hn
    exact Finset.mem_filter.mpr ⟨hn,(Finset.mem_filter.mp hn).2⟩
  · intro n hn
    exact hS n (Finset.mem_filter.mp hn).1

/-- The paid part of the ORIGINAL core, with every physical/count/radial
mask and the full original residual coefficient retained. -/
def literalCorePaid (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ literalPopulation (ZetaRieszParityPacket.coreBand u N K)
    (ZetaRieszAnnulusJoint.intermediatePrimes u N) N,
      residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The exact signed complement after the independent literal payment.
Neither a favorable observation nor another allocation is spent twice. -/
def literalCoreRest (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ ZetaRieszParityPacket.coreBand u N K\
    literalPopulation (ZetaRieszParityPacket.coreBand u N K)
      (ZetaRieszAnnulusJoint.intermediatePrimes u N) N,
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The paid literal population is an exact subset of the original core. -/
theorem coreResponse_eq_paid_rest (u y : ℝ) (N K : ℕ) :
    ZetaRieszParityPacket.coreResponse u y N K=literalCorePaid u y N K+literalCoreRest u y N K := by
  have hs : literalPopulation (ZetaRieszParityPacket.coreBand u N K)
      (ZetaRieszAnnulusJoint.intermediatePrimes u N) N ⊆
        ZetaRieszParityPacket.coreBand u N K := Finset.filter_subset _ _
  unfold ZetaRieszParityPacket.coreResponse literalCorePaid literalCoreRest
  rw [← Finset.sum_sdiff hs]
  ring

/-- Every retained literal mask is discharged by actual core membership;
the sector bound assumes no arithmetic cancellation or zeta zero. -/
theorem source_scaled_literalCorePaid_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 320 ≤ N)
    (y : ℝ) (K : ℕ) :
    ‖(u : ℂ)^(N+1)*literalCorePaid u y N K‖ ≤ literalErrorBudget N := by
  apply source_scaled_literal_population_bound hu hU hN
    (ZetaRieszParityPacket.coreBand u N K) (ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length_pos u N) y
  intro n hn
  exact (Finset.mem_filter.mp hn).2.2

/-- The current joint carrier differs from its literal signed rest by an
explicit geometric cost. The whole -79/1000 floor for that rest is OPEN. -/
theorem joined_sub_literalCoreRest_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 320 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) (y : ℝ) (K : ℕ) :
    ‖(u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N K-literalCoreRest u y N K)‖ ≤
      2*(19/20 : ℝ)^N*zetaMoebiusLogMajorantMass (1+1/256)+literalErrorBudget N := by
  have hg := ZetaRieszGammaJoint.core_joined_bound hu hU N K y hL
  have hp := source_scaled_literalCorePaid_bound hu hU hN y K
  have he : (u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N K-literalCoreRest u y N K)=
      -((u : ℂ)^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K-
        ZetaRieszGammaJoint.joinedPhysical u y N K))+(u : ℂ)^(N+1)*literalCorePaid u y N K := by
    rw [coreResponse_eq_paid_rest]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_neg]
  exact add_le_add hg hp

/-- Independently paid literal labels can be deleted on any cofinal
order/count schedule, uniformly even when the phase height moves. -/
theorem tendsto_joined_sub_literalCoreRest {u : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun j => (u : ℂ)^(orders j+1)*
      (ZetaRieszGammaJoint.joinedPhysical u (heights j) (orders j) (counts j)-
        literalCoreRest u (heights j) (orders j) (counts j))) atTop (𝓝 0) := by
  have hpaid : Tendsto (fun j => (u : ℂ)^(orders j+1)*
      literalCorePaid u (heights j) (orders j) (counts j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun j => literalErrorBudget (orders j)) ?_
      (tendsto_literalErrorBudget.comp ho)
    filter_upwards [ho.eventually (eventually_ge_atTop (320 : ℕ))] with j hj
    exact source_scaled_literalCorePaid_bound hu.le hU hj (heights j) (counts j)
  have h := (ZetaRieszGammaJoint.tendsto_core_sub_joined hu hU heights orders counts ho).neg.add hpaid
  simp only [neg_zero,zero_add] at h
  apply h.congr'
  filter_upwards [] with j
  rw [coreResponse_eq_paid_rest]
  ring

/-- On the actual dyadic core, every nonzero original atom left after
the literal payment has owner log below 243N/200. The physical and
nondominant conditions are deduced from the original masks. -/
theorem literal_rest_owner_cut (j : ℕ) (hj : 32 ≤ j) (u : ℝ) {n : ℕ}
    (hn : n ∈ ZetaRieszParityPacket.coreBand u
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)\
      literalPopulation (ZetaRieszParityPacket.coreBand u
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))
        (ZetaRieszAnnulusJoint.intermediatePrimes u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
        (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    (hcoeff : residualCoefficient
      (ZetaRieszAnnulusJoint.intermediatePrimes u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) n ≠ 0) :
    log (ZetaRieszPrimeEndpoint.largestPrime n) <
      (243/200 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  obtain ⟨hncore,hnnot⟩ := Finset.mem_sdiff.mp hn
  have hnnarrow := (Finset.mem_filter.mp hncore).1
  have hnnd := (Finset.mem_filter.mp hnnarrow).1
  have hnret := (Finset.mem_sdiff.mp hnnd).1
  have hnS := (Finset.mem_sdiff.mp hnret).1
  obtain ⟨hnfew,hw⟩ := Finset.mem_filter.mp hnS
  obtain ⟨hncentral,hc3,hcK⟩ := Finset.mem_filter.mp hnfew
  have hs : Squarefree n := by
    by_contra hh
    apply hcoeff
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hh]
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hphi := ZetaRieszDominantAllocation.nondominant_prime_log_lt j hj u hnnd hcoeff
    (ZetaRieszPrimeEndpoint.largestPrime n) hp
  by_contra hncut
  have hP : (243/200 : ℝ)*N ≤ log (ZetaRieszPrimeEndpoint.largestPrime n) := le_of_not_gt hncut
  have hpN : N^2 < ZetaRieszPrimeEndpoint.largestPrime n := by
    by_contra hh
    have hsmall := ZetaRieszMaskSupport.few_smooth_divisor_log_le j hj hs
      (Nat.dvd_of_mem_primeFactors hp) hcK (by
        intro q hq
        have he : q=ZetaRieszPrimeEndpoint.largestPrime n := by
          simpa only [hpp.primeFactors,Finset.mem_singleton] using hq
        simpa only [he] using le_of_not_gt hh)
    have hN0 : (0 : ℝ)<N := by
      dsimp [N,ZetaRieszPrimeCountFrequency.dyadicMomentOrder,ZetaRieszPrimeCountFrequency.dyadicPrimeCount]
      positivity
    change log (ZetaRieszPrimeEndpoint.largestPrime n) ≤ (N : ℝ)/4 at hsmall
    linarith
  have hpX : ZetaRieszPrimeEndpoint.largestPrime n <
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hncentral).1).1).2 _ hp
  have hpA := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N _).mpr ⟨hpp,hpN,hpX⟩
  exact hnnot (Finset.mem_filter.mpr ⟨hncore,hs,hc3,hpA,hP,hphi.le⟩)

end RiemannGaussian.ZetaRieszJointOwnerEnvelope

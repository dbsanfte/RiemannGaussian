/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFreeRadialRows

/-!
# Paying the canonical owner-threshold boundary

The actual owner weight has two binomial tails. On every canonical row
with log(p)>=507N/400, the literal nondominant mask puts its cofactor
share in [7/20,47/125]. Both tails beat the source growth. All counts and
periods on these rows are paid together; the two other moving boundaries
remain signed in the final comparison floor.
-/

noncomputable section
open Filter Topology Real MeasureTheory Set
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszClippedAllocationPayment
open ZetaRieszFreeRadialRows ZetaRieszCanonicalOwnerRows
open ZetaRieszSaturatedRowFloor ZetaRieszUnsignedDivisorError
open ZetaRieszOwnerMaximal ZetaRieszJointAllocation

private theorem upper_tilt_log : log (1047/1000 : ℝ)-(13/32 : ℝ)*log (9/8 : ℝ) ≤ -(1/600) := by
  have hlo : (2/17 : ℝ) ≤ log (9/8 : ℝ) := by
    have h := sum_range_le_log_div (by norm_num : (0 : ℝ)≤1/17)
      (by norm_num : (1/17 : ℝ)<1) 1
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hhi : log (1047/1000 : ℝ) ≤ 23/500 := by
    apply (log_le_iff_le_exp (by norm_num : (0 : ℝ)<1047/1000)).mpr
    have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤23/500) 3
    norm_num [Finset.sum_range_succ] at h
    linarith
  linarith

/-- Two explicit tilts pay the ORIGINAL missing owner mass, including
the exact integer unpaid-order endpoints. -/
theorem ownerWeight_exponential {N : ℕ} (hN : 320 ≤ N) {x : ℝ}
    (hx : (7/20 : ℝ) ≤ x) (hx1 : x ≤ (47/125 : ℝ)) :
    ownerWeight N x ≤ 3*exp (-(N : ℝ)/600) := by
  have hx0 : 0 ≤ x := by linarith
  have hxone : x ≤ 1 := by linarith
  let B := exp (-(13/32 : ℝ)*N*log (9/8 : ℝ))
  let C := exp (((N : ℝ)/5+1)*log (5/4 : ℝ))
  have ht : 0 ≤ log (9/8 : ℝ) := log_nonneg (by norm_num)
  have hl : 0 ≤ log (5/4 : ℝ) := log_nonneg (by norm_num)
  have hm := missed_mass_bound N hN hx0 hxone
    (exp_pos (-(13/32 : ℝ)*N*log (9/8 : ℝ))).le
    (exp_pos (((N : ℝ)/5+1)*log (5/4 : ℝ))).le
    (by norm_num : (0 : ℝ)≤9/8) (by norm_num : (0 : ℝ)≤4/5) (by
      intro k hk hcut
      have hc : (13/32 : ℝ)*N ≤ k := by
        have hh : 13*(N : ℝ)<32*k := by exact_mod_cast (by omega : 13*N<32*k)
        linarith
      rw [← exp_log (by norm_num : (0 : ℝ)<9/8),← exp_nat_mul,← exp_add]
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
  have hhi : (9/8 : ℝ)*x+(1-x) ≤ 1047/1000 := by linarith
  have hlo : (4/5 : ℝ)*x+(1-x) ≤ 93/100 := by linarith
  have hb := hm.trans (add_le_add
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hhi (N+1)) (exp_pos _).le)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hlo (N+1)) (exp_pos _).le))
  have heh : B*(1047/1000 : ℝ)^(N+1)=
      (1047/1000 : ℝ)*exp ((N : ℝ)*(log (1047/1000 : ℝ)-(13/32 : ℝ)*log (9/8 : ℝ))) := by
    dsimp [B]
    have hp : (1047/1000 : ℝ)^N=exp ((N : ℝ)*log (1047/1000 : ℝ)) := by
      rw [exp_nat_mul,exp_log (by norm_num : (0 : ℝ)<1047/1000)]
    rw [pow_succ,hp,show exp (-(13/32 : ℝ)*N*log (9/8 : ℝ))*
      (exp ((N : ℝ)*log (1047/1000 : ℝ))*(1047/1000 : ℝ)) =
        (1047/1000 : ℝ)*(exp (-(13/32 : ℝ)*N*log (9/8 : ℝ))*
          exp ((N : ℝ)*log (1047/1000 : ℝ))) by ring,← exp_add]
    congr 1
    ring
  have hel : C*(93/100 : ℝ)^(N+1)=
      ((5/4 : ℝ)*(93/100))*exp ((N : ℝ)*(log (93/100 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ))) := by
    dsimp [C]
    have hp : (93/100 : ℝ)^N=exp ((N : ℝ)*log (93/100 : ℝ)) := by
      rw [exp_nat_mul,exp_log (by norm_num : (0 : ℝ)<93/100)]
    rw [pow_succ,hp,show ((N : ℝ)/5+1)*log (5/4 : ℝ)=
      log (5/4 : ℝ)+(N : ℝ)/5*log (5/4 : ℝ) by ring,exp_add,
      exp_log (by norm_num : (0 : ℝ)<5/4)]
    rw [show (5/4 : ℝ)*exp ((N : ℝ)/5*log (5/4 : ℝ))*
      (exp ((N : ℝ)*log (93/100 : ℝ))*(93/100 : ℝ)) =
        ((5/4 : ℝ)*(93/100))*(exp ((N : ℝ)/5*log (5/4 : ℝ))*
          exp ((N : ℝ)*log (93/100 : ℝ))) by ring,← exp_add]
    congr 1
    ring
  have hloglo : log (93/100 : ℝ)+(1/5 : ℝ)*log (5/4 : ℝ) ≤ -(1/600) := by
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<93/100),
      log_tilt_bounds.2]
  change ownerWeight N x ≤ _ at hb
  change ownerWeight N x ≤ _
  change ownerWeight N x ≤ B*(1047/1000 : ℝ)^(N+1)+C*(93/100 : ℝ)^(N+1) at hb
  rw [heh,hel] at hb
  have hh := exp_le_exp.mpr (mul_le_mul_of_nonneg_left upper_tilt_log (Nat.cast_nonneg (α := ℝ) N))
  have hl' := exp_le_exp.mpr (mul_le_mul_of_nonneg_left hloglo (Nat.cast_nonneg (α := ℝ) N))
  rw [show (N : ℝ)*(-(1/600 : ℝ))=-(N : ℝ)/600 by ring] at hh hl'
  nlinarith [exp_pos (-(N : ℝ)/600)]

/-- Only the shortened original rows are selected, so this payment is
disjoint from the free radial-window payment. -/
def allocationRows (u : ℝ) (N : ℕ) : Finset (ℕ×ℕ) :=
  (clippedRows u N).filter (fun pb => (507/400 : ℝ)*N ≤ log pb.1)

private theorem allocation_row_mem {u : ℝ} {N : ℕ} {pb : ℕ×ℕ}
    (hpb : pb ∈ allocationRows u N) : pb ∈ rows u N :=
  (Finset.mem_sdiff.mp (Finset.mem_filter.mp hpb).1).1

/-- The literal nondominant mask and original radial upper endpoint
force both missing factorial tails away from their phase transitions. -/
theorem allocation_row_share {u : ℝ} {N d : ℕ} (hN : 32 ≤ N) {pb : ℕ×ℕ}
    (hpb : pb ∈ allocationRows u N)
    (hd : d ∈ Finset.Ioc (lower N pb.1 pb.2)
      (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)) :
    (7/20 : ℝ) ≤ 1-log pb.1/(log (pb.1*pb.2 : ℕ)+log d) ∧
      1-log pb.1/(log (pb.1*pb.2 : ℕ)+log d) ≤ (47/125 : ℝ) := by
  have hr := allocation_row_mem hpb
  obtain ⟨hp,hb,hs,hpd,hmax,hH,hM,hlo,hhi,hsat,hshare⟩ := rows_geometry hr
  have hd' := Finset.mem_Ioc.mp hd
  have hdl : log (lower N pb.1 pb.2) ≤ log d :=
    log_le_log (by exact_mod_cast hM) (by exact_mod_cast hd'.1.le)
  have hdu : log d ≤ log (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2) :=
    log_le_log (by exact_mod_cast hM.trans hd'.1) (by exact_mod_cast hd'.2)
  have hP := (Finset.mem_filter.mp hpb).2
  have hn : (32 : ℝ)≤N := by exact_mod_cast hN
  have hT : 0 < log (pb.1*pb.2 : ℕ)+log d := by linarith
  constructor
  · have hh : log pb.1/(log (pb.1*pb.2 : ℕ)+log d) ≤ 13/20 :=
      (div_le_iff₀ hT).mpr (by linarith)
    linarith
  · have hh : (78/125 : ℝ) ≤ log pb.1/(log (pb.1*pb.2 : ℕ)+log d) :=
      (le_div_iff₀ hT).mpr (by linarith)
    linarith

private theorem allocation_physical_bound {u : ℝ} {N d : ℕ} (hN : 320 ≤ N)
    {pb : ℕ×ℕ} (hpb : pb ∈ allocationRows u N)
    (hd : d ∈ Finset.Ioc (lower N pb.1 pb.2)
      (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)) (y : ℝ) :
    |physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)| ≤
      3*exp (-(N : ℝ)/600)*radialEnvelope N := by
  have hs := allocation_row_share (by omega : 32 ≤ N) hpb hd
  have hx0 : 0 ≤ 1-log pb.1/(log (pb.1*pb.2 : ℕ)+log d) := by linarith [hs.1]
  have hx1 : 1-log pb.1/(log (pb.1*pb.2 : ℕ)+log d) ≤ 1 := by linarith [hs.2]
  have hw := ownerWeight_bounds N hx0 hx1
  have he := ownerWeight_exponential hN hs.1 hs.2
  have ht : 0 ≤ log (pb.1*pb.2 : ℕ)+log d :=
    add_nonneg (log_natCast_nonneg _) (log_natCast_nonneg _)
  rw [physicalWeight,abs_mul,abs_mul,abs_of_nonneg hw.1,
    abs_of_nonneg (radialMoment_nonneg N ht)]
  exact (mul_le_of_le_one_right (mul_nonneg hw.1 (radialMoment_nonneg N ht)) (abs_cos_le_one _)).trans
    (mul_le_mul he (radialMoment_le N ht) (radialMoment_nonneg N ht) (by positivity))

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

private theorem allocation_inner_bound {u : ℝ} {N : ℕ} (hN : 320 ≤ N)
    {pb : ℕ×ℕ} (hpb : pb ∈ allocationRows u N) (y : ℝ) :
    |(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
      (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2),
        physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))| ≤
      (3*exp (-(N : ℝ)/600)*radialEnvelope N)*(1+(203/100 : ℝ)*N) := by
  have hb d (hd : d ∈ Finset.Ioc (lower N pb.1 pb.2)
      (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)) :
      |physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ)| ≤
        (3*exp (-(N : ℝ)/600)*radialEnvelope N)*(d : ℝ)⁻¹ := by
    rw [abs_div,abs_of_nonneg (a := (d : ℝ)) (Nat.cast_nonneg d),div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (allocation_physical_bound hN hpb hd y) (by positivity)
  have hs := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb)
  rw [← Finset.mul_sum] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left (row_reciprocal_bound (allocation_row_mem hpb))
    (by positivity [radialEnvelope_pos N]))

private theorem normalized_allocation_envelope {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (N : ℕ) :
    u^(N+1)*radialEnvelope N*exp (-(N : ℝ)/600) ≤
      2*((N : ℝ)+1)*(999/1000 : ℝ)^N := by
  have hr : 0 ≤ 2*u*exp (-(1/600 : ℝ)) := by positivity
  have hrate : 2*u*exp (-(1/600 : ℝ)) ≤ 999/1000 := by
    rw [exp_neg,mul_inv_le_iff₀ (exp_pos _)]
    have he := add_one_le_exp (1/600 : ℝ)
    have huU : u ≤ (10001/20000 : ℝ) := hU
    nlinarith
  have he : u^(N+1)*radialEnvelope N*exp (-(N : ℝ)/600) =
      2*u*((N : ℝ)+1)*(2*u*exp (-(1/600 : ℝ)))^N := by
    unfold radialEnvelope
    rw [mul_pow,mul_pow,← exp_nat_mul,pow_succ,pow_succ]
    rw [show -(N : ℝ)/600=(N : ℝ)*(-(1/600 : ℝ)) by ring]
    ring
  rw [he]
  have hfac : 2*u*((N : ℝ)+1) ≤ 2*((N : ℝ)+1) := by
    have huU : u ≤ (10001/20000 : ℝ) := hU
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact mul_le_mul hfac (pow_le_pow_left₀ hr hrate N) (pow_nonneg hr N) (by positivity)

/-- The actual signed density rows selected for this disjoint payment. -/
def allocationDensityMain (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ pb ∈ allocationRows u N,
    densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
      (lower N pb.1 pb.2) (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)

/-- All counts and periods on the owner-threshold boundary have one
geometric source-scale budget. -/
def allocationErrorBudget (N : ℕ) : ℝ := 162*((N : ℝ)+1)^4*(999/1000 : ℝ)^N

theorem tendsto_allocationErrorBudget : Tendsto allocationErrorBudget atTop (𝓝 0) := by
  change Tendsto (fun N => allocationErrorBudget N) atTop (𝓝 0)
  simpa only [allocationErrorBudget,mul_assoc,mul_zero] using
    (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 4
      (by norm_num : (0 : ℝ)<999/1000) (by norm_num)).const_mul 162

/-- A whole signed main sector is paid using its exact owner allocation;
no ordinary-prime phase replacement or completed cofactor is used. -/
theorem source_scaled_allocationDensityMain_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 320 ≤ N)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) (y : ℝ) :
    |u^(N+1)*allocationDensityMain u y N| ≤ allocationErrorBudget N := by
  let Q := 6*((N : ℝ)+1)*(1+(203/100 : ℝ)*N)*(999/1000 : ℝ)^N
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hb pb (hpb : pb ∈ allocationRows u N) :
      |u^(N+1)*densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
        (lower N pb.1 pb.2) (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)| ≤
          (1 : ℝ)/(pb.1*pb.2 : ℕ)*Q := by
    rw [densityRow_physical]
    have hi := mul_le_mul_of_nonneg_left (allocation_inner_bound hN hpb y) (pow_nonneg hu (N+1))
    have hi' : |u^(N+1)*(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
        (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2),
          physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))| ≤ Q := by
      rw [abs_mul,abs_of_nonneg (pow_nonneg hu _)]
      calc
        _ ≤ u^(N+1)*((3*exp (-(N : ℝ)/600)*radialEnvelope N)*(1+(203/100 : ℝ)*N)) := hi
        _ = (3*(1+(203/100 : ℝ)*N))*(u^(N+1)*radialEnvelope N*exp (-(N : ℝ)/600)) := by ring
        _ ≤ (3*(1+(203/100 : ℝ)*N))*(2*((N : ℝ)+1)*(999/1000 : ℝ)^N) :=
          mul_le_mul_of_nonneg_left (normalized_allocation_envelope hu hU N) (by positivity)
        _ = Q := by dsimp [Q]; ring
    have hc := row_density_coefficient (by omega : 32 ≤ N) hL (allocation_row_mem hpb)
    calc
      _ = |((μ pb.2 : ℝ)*ZetaRieszSignedConvolution.pairHinge
        (SquarefreeVaughanLogSource.length u N) pb.1 pb.2/
          (SquarefreeVaughanLogSource.length u N*(pb.1*pb.2 : ℕ)))*density (pb.1*pb.2).primeFactors| *
          |u^(N+1)*(∑ d ∈ Finset.Ioc (lower N pb.1 pb.2)
            (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2),
              physicalWeight N (log pb.1) y (log (pb.1*pb.2 : ℕ)+log d)/(d : ℝ))| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ _ := mul_le_mul hc hi' (abs_nonneg _) (by positivity)
  unfold allocationDensityMain
  rw [Finset.mul_sum]
  have hs := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb)
  rw [← Finset.sum_mul] at hs
  have houter : (∑ pb ∈ allocationRows u N, (1 : ℝ)/(pb.1*pb.2 : ℕ)) ≤
      (1+(203/100 : ℝ)*N)^2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (fun _ hp => allocation_row_mem hp)
      (fun _ _ _ => by positivity)).trans (rows_outer_harmonic_bound u N)
  have hs' := hs.trans (mul_le_mul_of_nonneg_right houter hQ)
  apply hs'.trans
  have hbase : 1+(203/100 : ℝ)*N ≤ 3*((N : ℝ)+1) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hp := pow_le_pow_left₀ (by positivity) hbase 3
  calc
    _ = 6*((N : ℝ)+1)*(1+(203/100 : ℝ)*N)^3*(999/1000 : ℝ)^N := by dsimp [Q]; ring
    _ ≤ 6*((N : ℝ)+1)*(3*((N : ℝ)+1))^3*(999/1000 : ℝ)^N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ = _ := by unfold allocationErrorBudget; ring

/-- The second signed main payment has no exposed-zero premise. -/
theorem tendsto_source_scaled_allocationDensityMain {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun N => u^(N+1)*allocationDensityMain u y N) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := allocationErrorBudget) ?_ tendsto_allocationErrorBudget
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hl,eventually_ge_atTop (320 : ℕ)] with N hL hN
  rw [Real.norm_eq_abs]
  exact source_scaled_allocationDensityMain_bound (by linarith) hU hN (by nlinarith only [hL]) y

/-- Original density rows left after BOTH disjoint signed main payments. -/
def residualRows (u : ℝ) (N : ℕ) : Finset (ℕ×ℕ) := clippedRows u N \ allocationRows u N

/-- The still unpaid density sum, retaining all its Möbius signs,
counts, phases and integer endpoints. -/
def residualDensityMain (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ pb ∈ residualRows u N,
    densityRow N (SquarefreeVaughanLogSource.length u N) y pb.1 pb.2
      (lower N pb.1 pb.2) (upper N (SquarefreeVaughanLogSource.length u N) pb.1 pb.2)

/-- Exact taxonomy of the two remaining moving boundaries. The
nondominant owner-threshold boundary has been eliminated. -/
theorem residual_row_boundary {u : ℝ} {N : ℕ} {pb : ℕ×ℕ} (hpb : pb ∈ residualRows u N) :
    log pb.1 < (507/400 : ℝ)*N ∧
      ((37/20 : ℝ)*N < log (pb.1*pb.2 : ℕ) ∨
        log pb.1+SquarefreeVaughanLogSource.length u N < (203/100 : ℝ)*N) := by
  obtain ⟨hc,ha⟩ := Finset.mem_sdiff.mp hpb
  obtain ⟨hr,hf⟩ := Finset.mem_sdiff.mp hc
  have hp : log pb.1 < (507/400 : ℝ)*N := by
    by_contra hn
    exact ha (Finset.mem_filter.mpr ⟨hc,le_of_not_gt hn⟩)
  refine ⟨hp,?_⟩
  by_cases hprod : log (pb.1*pb.2 : ℕ) ≤ (37/20 : ℝ)*N
  · right
    by_contra hn
    exact hf (Finset.mem_filter.mpr ⟨hr,hprod,hp.le,le_of_not_gt hn⟩)
  · exact Or.inl (lt_of_not_ge hprod)

theorem clippedDensityMain_eq_allocation_residual (u y : ℝ) (N : ℕ) :
    clippedDensityMain u y N = allocationDensityMain u y N+residualDensityMain u y N := by
  have hs : allocationRows u N ⊆ clippedRows u N := Finset.filter_subset _ _
  unfold clippedDensityMain allocationDensityMain residualDensityMain residualRows
  rw [← Finset.sum_sdiff hs]
  ring

/-- Old comparison costs plus the two disjoint main-sector payments. -/
def residualErrorBudget (y : ℝ) (N : ℕ) : ℝ := clippedErrorBudget y N+allocationErrorBudget N

theorem tendsto_residualErrorBudget (y : ℝ) : Tendsto (residualErrorBudget y) atTop (𝓝 0) := by
  change Tendsto (fun N => residualErrorBudget y N) atTop (𝓝 0)
  simpa only [residualErrorBudget,zero_add] using
    (tendsto_clippedErrorBudget y).add tendsto_allocationErrorBudget

/-- Both signed main sectors disappear from the whole-carrier floor.
Only the two remaining clipped-boundary geometries and the untouched
literal incidences still require a JOINT independent numerical floor. -/
theorem eventually_joined_floor_with_residual_rows {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      u^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        (canonicalRemaining u y j-endpointRows u y j+
          residualDensityMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))-
        residualErrorBudget y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ≤
      ((u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re := by
  have hf := eventually_joined_floor_with_clipped_rows hu hU hy
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ)≤11/16)
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)
  filter_upwards [hf,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hl,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (320 : ℕ))] with j hj hL hN
  have hb := (abs_le.mp (source_scaled_allocationDensityMain_bound (by linarith) hU hN
    (by nlinarith only [hL]) y)).1
  rw [clippedDensityMain_eq_allocation_residual] at hj
  unfold residualErrorBudget
  nlinarith only [hj,hb]

end RiemannGaussian.ZetaRieszClippedAllocationPayment

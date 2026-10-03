/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerLatticePhase

/-!
# Independent signed bound for the joined tagged-owner density main

The phase sum is bounded AFTER exact signed integration on the complete
literal core window. Only then is the logarithmic density scalar bounded.
Tags and owners aggregate at a fixed polynomial cost. This does not
silently extend the dyadic-shell comparison to a full window, or discard
internal arithmetic masks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszTaggedOwnerPhase
open ZetaRieszTaggedOwnerComparison ZetaRieszOwnerLatticePhase
open ZetaRieszSmoothOwnerDiscrepancy ZetaRieszCofactorDiscrepancy

private theorem profile_steps {R : ℕ} (_hR : 0<R) (f : ℕ→ℝ) :
    (∑ D∈Finset.Icc 1 R, (f D-f (D+1)))=f 1-f (R+1) := by
  have he : Finset.Icc 1 R=Finset.Ico 1 (R+1) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.add_sub_cancel,Nat.add_zero,Nat.zero_add,Nat.add_comm,Nat.add_left_comm,
    Nat.add_assoc] using Finset.sum_range_sub' (fun i => f (i+1)) R

private theorem profile_step_nonneg {b : ℝ} (D : ℕ) (hD : 0<D) :
    0 ≤ max 0 (b-log D)-max 0 (b-log (D+1 : ℕ)) := by
  have hlog := log_le_log (show (0 : ℝ)<D by exact_mod_cast hD)
    (show (D : ℝ)≤(D+1 : ℕ) by exact_mod_cast Nat.le_succ D)
  exact sub_nonneg.mpr (max_le_max_left 0 (by linarith only [hlog]))

theorem taggedDensityPrefix_bound (S : Finset ℕ) (hS : ∀ q∈S, q.Prime)
    {r : ℕ} (hr : r.Prime) (D : ℕ) :
    |taggedDensityPrefix S r D|≤2*(1+log D) := by
  have hi : ∀ q∈insert r S, q.Prime := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hr
    · exact hS q hq
  exact ((abs_sub _ _).trans (add_le_add
    (ZetaRieszLongCutoffError.roughDensityPrefix_bound S hS D)
    (ZetaRieszLongCutoffError.roughDensityPrefix_bound (insert r S) hi D))).trans_eq (by ring)

/-- This scalar cap is used only AFTER the signed phase saving. -/
theorem taggedRieszScalar_bound (S : Finset ℕ) (hS : ∀ q∈S, q.Prime)
    {r R : ℕ} (hr : r.Prime) (hR : 0<R) {b : ℝ} (hb : 0≤b)
    (hend : b≤log (R+1 : ℕ)) :
    |taggedRieszScalar S r R b|≤2*b*(1+log R) := by
  let f := fun D : ℕ => max 0 (b-log D)
  have hsum : (∑ D∈Finset.Icc 1 R, (f D-f (D+1)))=b := by
    rw [profile_steps hR f]
    simp only [f,Nat.cast_one,log_one,sub_zero,max_eq_right hb,
      max_eq_left (sub_nonpos.mpr hend)]
  unfold taggedRieszScalar
  calc
    _ ≤ ∑ D∈Finset.Icc 1 R,
        |(f D-f (D+1))*taggedDensityPrefix S r D| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ D∈Finset.Icc 1 R, (f D-f (D+1))*(2*(1+log R)) := by
      apply Finset.sum_le_sum
      intro D hD
      have hd := Finset.mem_Icc.mp hD
      have hs := profile_step_nonneg (b := b) D hd.1
      rw [abs_mul,abs_of_nonneg hs]
      apply mul_le_mul_of_nonneg_left ((taggedDensityPrefix_bound S hS hr D).trans ?_) hs
      have hl := log_le_log (show (0 : ℝ)<D by exact_mod_cast hd.1)
        (show (D : ℝ)≤R by exact_mod_cast hd.2)
      linarith only [hl]
    _ = _ := by rw [← Finset.sum_mul,hsum]; ring

private theorem shell_sum_eq (M X : ℕ) (a : ℕ→ℝ) (y c : ℝ) :
    (∑ n∈Finset.Icc 1 X, shellWeight M X a y c n)=
      ∑ n∈Finset.Ioc M X, a n*cos (y*(c+log n))/(n : ℝ) := by
  have hs : Finset.Ioc M X⊆Finset.Icc 1 X := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega,hn'.2⟩
  have hsub := Finset.sum_subset (f := shellWeight M X a y c) hs (by
    intro n hn hnot
    have hx := (Finset.mem_Icc.mp hn).2
    have hlo : ¬M<n := fun h => hnot (Finset.mem_Ioc.mpr ⟨h,hx⟩)
    simp [shellWeight,hlo])
  rw [← hsub]
  apply Finset.sum_congr rfl
  intro n hn
  rw [shellWeight,if_pos (Finset.mem_Ioc.mp hn)]

/-- The main is an interval sum with no artificial shell-end dependence. -/
theorem taggedOwnerMain_eq_sum (S : Finset ℕ) (N M X R r p : ℕ) (L y : ℝ) :
    taggedOwnerMain S N M X R r p L y =
      (taggedRieszScalar S r R (L-log p)*
        (∑ a∈Finset.Ioc M X, ownerAmplitude N (log p) a*cos (y*(log p+log a))/(a : ℝ)))/(L*p) := by
  unfold taggedOwnerMain
  rw [shell_sum_eq]

/-- Independent source-normalized bound on the EXISTING signed density
main, with complete core endpoints, every cofactor count and old allocation. -/
theorem normalized_tagged_main_core_bound (S : Finset ℕ) (hS : ∀ q∈S, q.Prime)
    {N R r p : ℕ} (hN : 64≤N) (hr : r.Prime) (hR : 0<R) (hp : p.Prime)
    (hc : 1≤log p) (hcN : log p≤(4/3 : ℝ)*N) {L u y : ℝ}
    (hpL : log p≤L) (hend : L-log p≤log (R+1 : ℕ)) (hlogR : log R≤2*N)
    (hy : 54≤|y|) (hu : 0≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    |u^(N+1)*taggedOwnerMain S N
      (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) R r p L y|≤
      (2*(1+2*(N : ℝ))/(p : ℝ))*ownerSamplingBudget u y N := by
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hL : 0<L := by linarith only [hc,hpL]
  have hR1 : (1 : ℝ)≤R := by exact_mod_cast hR
  have hs := taggedRieszScalar_bound S hS hr hR (sub_nonneg.mpr hpL) hend
  have hsb : |taggedRieszScalar S r R (L-log p)|≤2*L*(1+2*(N : ℝ)) := by
    have hr0 := log_nonneg hR1
    have hbL : L-log p≤L := by linarith only [hc]
    have hb0 : 0≤L-log p := sub_nonneg.mpr hpL
    have h := mul_le_mul hbL (add_le_add_left hlogR 1) (by linarith only [hr0]) hL.le
    nlinarith only [hs,h]
  have hd : |taggedRieszScalar S r R (L-log p)|/(L*p)≤2*(1+2*(N : ℝ))/(p : ℝ) := by
    exact (div_le_div_of_nonneg_right hsb (mul_pos hL hp0).le).trans_eq (by field_simp)
  have hw := normalized_core_lattice_sum_bound hN hc hcN hy hu hU
  have hB : 0≤ownerSamplingBudget u y N := by
    unfold ownerSamplingBudget
    positivity
  unfold taggedOwnerMain
  rw [shell_sum_eq]
  have he : |u^(N+1)*((taggedRieszScalar S r R (L-log p)*
      (∑ n∈Finset.Ioc (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)),
        ownerAmplitude N (log p) n*cos (y*(log p+log n))/(n : ℝ)))/(L*p))|=
      (|taggedRieszScalar S r R (L-log p)|/(L*p))*
      |u^(N+1)*(∑ n∈Finset.Ioc (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)),
        ownerAmplitude N (log p) n*cos (y*(log p+log n))/(n : ℝ))| := by
    simp only [abs_mul,abs_div,abs_of_nonneg (mul_pos hL hp0).le]
    ring
  rw [he]
  exact mul_le_mul hd hw (abs_nonneg _) (by positivity)

/-- Joint signed main for ALL owners and retained tags. The polynomial
price is applied only after the geometric signed phase estimate. -/
theorem global_core_tagged_main_bound {N Q : ℕ} (hN : 64≤N) (T V P : Finset ℕ)
    (S : ℕ→Finset ℕ) (hT : ∀ r∈T, r.Prime ∧ r≤N^3) (hV : V⊆T)
    (hS : ∀ r∈V, S r⊆T) (R : ℕ→ℕ)
    {L u y : ℝ} (hu : 0≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    (hP : ∀ p∈P, p.Prime ∧ p≤Q ∧ 1≤log p ∧ log p≤(4/3 : ℝ)*N ∧ log p≤L)
    (hQ : log Q≤(203/100 : ℝ)*N)
    (hR : ∀ p∈P, 0<R p ∧ L-log p≤log (R p+1 : ℕ) ∧ log (R p)≤2*N) :
    |u^(N+1)*∑ p∈P, ∑ r∈V, taggedOwnerMain (S r) N
      (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) (R p) r p L y|≤
      10*((N : ℝ)+1)^5*ownerSamplingBudget u y N := by
  have hB : 0≤ownerSamplingBudget u y N := by unfold ownerSamplingBudget; positivity
  have hcard : (V.card : ℝ)≤(N : ℝ)^3 := by
    have hs : V⊆Finset.Icc 1 (N^3) := by
      intro r hr
      exact Finset.mem_Icc.mpr ⟨(hT r (hV hr)).1.pos,(hT r (hV hr)).2⟩
    have h := Finset.card_le_card hs
    simp only [Nat.card_Icc,Nat.add_sub_cancel] at h
    exact_mod_cast h
  have hh : (∑ p∈P, (p : ℝ)⁻¹)≤1+(203/100 : ℝ)*N :=
    (marked_harmonic_bound P (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1⟩)).trans
      (by linarith only [hQ])
  have he p (hp : p∈P) r (hr : r∈V) :
      |u^(N+1)*taggedOwnerMain (S r) N
        (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100)) (R p) r p L y|≤
        (2*(1+2*(N : ℝ))/(p : ℝ))*ownerSamplingBudget u y N :=
    normalized_tagged_main_core_bound (S r)
      (fun q hq => (hT q (hS r hr hq)).1)
      hN (hT r (hV hr)).1 (hR p hp).1 (hP p hp).1
      (hP p hp).2.2.1 (hP p hp).2.2.2.1 (hP p hp).2.2.2.2
      (hR p hp).2.1 (hR p hp).2.2 hy hu hU
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p∈P, ∑ r∈V, (2*(1+2*(N : ℝ))/(p : ℝ))*ownerSamplingBudget u y N := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Finset.mul_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (he p hp))
    _ = (2*(1+2*(N : ℝ))*ownerSamplingBudget u y N)*(V.card : ℝ)*
        (∑ p∈P, (p : ℝ)⁻¹) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ (2*(1+2*(N : ℝ))*ownerSamplingBudget u y N)*(N : ℝ)^3*
        (1+(203/100 : ℝ)*N) := by
      gcongr
    _ ≤ _ := by
      have hn : 0≤(N : ℝ) := Nat.cast_nonneg N
      have hp : 2*(1+2*(N : ℝ))*(N : ℝ)^3*(1+(203/100 : ℝ)*N)≤
          10*((N : ℝ)+1)^5 := by
        calc
          _ ≤ (4*((N : ℝ)+1))*((N : ℝ)+1)^3*((5/2 : ℝ)*((N : ℝ)+1)) := by
            have hA : 2*(1+2*(N : ℝ))≤4*((N : ℝ)+1) := by linarith
            have hC : 1+(203/100 : ℝ)*N≤(5/2 : ℝ)*((N : ℝ)+1) := by linarith
            have hpow := pow_le_pow_left₀ hn (show (N : ℝ)≤N+1 by linarith) 3
            exact mul_le_mul (mul_le_mul hA hpow (by positivity) (by positivity))
              hC (by positivity) (by positivity)
          _ = _ := by ring
      have h := mul_le_mul_of_nonneg_right hp hB
      calc
        _ = (2*(1+2*(N : ℝ))*(N : ℝ)^3*(1+(203/100 : ℝ)*N))*
          ownerSamplingBudget u y N := by ring
        _ ≤ _ := h

theorem global_core_tagged_main_budget_tendsto (u y : ℝ) :
    Tendsto (fun N : ℕ => 10*((N : ℝ)+1)^5*ownerSamplingBudget u y N) atTop (𝓝 0) := by
  simpa only [mul_zero,mul_assoc] using (ownerSamplingBudget_polynomial_tendsto 5 u y).const_mul 10

end RiemannGaussian.ZetaRieszTaggedOwnerPhase

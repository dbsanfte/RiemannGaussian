/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrefixCoherenceAudit
import RiemannGaussian.ZetaRieszSharperCountPayment

/-!
# A quadratic null profile reactivates the common signed moment

The minimum count-three condition allows a quadratic divisor-log
correction without changing the original carrier. A smaller profile
energy alone is nevertheless not a smaller whole-floor cost: the new
profile activates cutoff one, where every literal sharp prefix is one.

For the concrete near-least-energy correction 4/3,-1/(3N), the actual
one-sided cost is at least (log 2)/4 times the positive part of the
ENTIRE original signed weight sum. No claim is made that this common
moment is large or small on the native arithmetic support.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszNullProfileAudit
open ZetaRieszCofactorPhaseEnergy ZetaRieszCutoffPeriodFloor
open ZetaRieszCenteredPrimeEnergy ZetaRieszPrefixCoherenceAudit
open ZetaRieszRejoinedPhaseFloor ZetaRieszJointPrimeEnergy
open ZetaRieszJointAllocation ZetaRieszWideOwnerAudit
open ZetaRieszPostHingeEnergy

/-- A concrete log-quadratic correction close to the continuous
least-energy profile on the native total-log window. -/
def candidateProfile (X N : ℕ) (L : ℝ) : ℕ → ℝ :=
  correctedProfile X L (4/3) (-1/(3*(N : ℝ)))

/-- Exact early logarithmic shape of every quadratic null correction. -/
theorem corrected_early_difference {X k : ℕ} (hX : 1 ≤ X) (hk : k ≤ X)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : log k ≤ L) (linear quadratic : ℝ) :
    correctedProfile X L linear quadratic k-correctedProfile X L linear quadratic 1 =
      (linear-1)*log k+quadratic*(log k)^2 := by
  simp only [correctedProfile,centeredProfile,if_pos hk,if_pos hX,
    Nat.cast_one,log_one,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,
    sub_zero,max_eq_right hL0,max_eq_right (sub_nonneg.mpr hL)]
  ring

/-- Keeping even the first TWO early increments inactive uniquely fixes
the original unit-log correction. A nontrivial quadratic profile cannot
retain that already protected low-cutoff geometry for free. -/
theorem flat_early_iff {X : ℕ} (hX : 3 ≤ X) {L : ℝ} (hL : log 3 ≤ L)
    (linear quadratic : ℝ) :
    (correctedProfile X L linear quadratic 1=correctedProfile X L linear quadratic 2 ∧
      correctedProfile X L linear quadratic 2=correctedProfile X L linear quadratic 3) ↔
      linear=1 ∧ quadratic=0 := by
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have h23 : log (2 : ℝ) < log 3 := log_lt_log (by norm_num) (by norm_num)
  have hL0 : 0 ≤ L := by linarith only [hl2,h23,hL]
  have he2 := corrected_early_difference (by omega : 1 ≤ X) (by omega : 2 ≤ X)
    hL0 (le_trans h23.le hL) linear quadratic
  have he3 := corrected_early_difference (by omega : 1 ≤ X) hX hL0 hL linear quadratic
  constructor
  · rintro ⟨h12,h23'⟩
    rw [h12,sub_self] at he2
    rw [h12,h23',sub_self] at he3
    norm_num only [Nat.cast_ofNat] at he2 he3
    have hz2 : (linear-1+quadratic*log 2)*log 2=0 := by nlinarith only [he2]
    have hz3 : (linear-1+quadratic*log 3)*log 3=0 := by nlinarith only [he3]
    have ha2 := (mul_eq_zero.mp hz2).resolve_right hl2.ne'
    have ha3 := (mul_eq_zero.mp hz3).resolve_right (by linarith : log (3 : ℝ) ≠ 0)
    have hb : quadratic*(log 3-log 2)=0 := by nlinarith only [ha2,ha3]
    have hq := (mul_eq_zero.mp hb).resolve_right (by linarith : log (3 : ℝ)-log 2 ≠ 0)
    refine ⟨?_,hq⟩
    rw [hq,zero_mul,add_zero] at ha2
    linarith only [ha2]
  · rintro ⟨rfl,rfl⟩
    have he1 := correctedProfile_flat (by omega : 1 ≤ X)
      (show log (1 : ℕ) ≤ L by simpa only [Nat.cast_one,log_one] using hL0)
    have he2' := correctedProfile_flat (by omega : 2 ≤ X) (le_trans h23.le hL)
    have he3' := correctedProfile_flat hX hL
    exact ⟨he1.trans he2'.symm,he2'.trans he3'.symm⟩

/-- Null moments preserve the ACTUAL original atom on every count-three
label. No phase, physical condition, count or allocation is changed. -/
theorem candidate_prefix_eq {n X : ℕ} (hn : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) (hX : n ≤ X) (N : ℕ) (L : ℝ) :
    (∑ d ∈ Finset.Icc 1 X,candidateProfile X N L d*
      (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0)) =
      VaughanLogAverage.riesz L n :=
  corrected_prefix_eq hn hc hX L (4/3) (-1/(3*(N : ℝ)))

/-- The newly active first step is exact; the endpoint centering cancels. -/
theorem candidate_first_step {X : ℕ} (hX : 2 ≤ X) {L : ℝ} (hL : log 2 ≤ L)
    (N : ℕ) :
    candidateProfile X N L 1-candidateProfile X N L 2 =
      -(1/3-log 2/(3*(N : ℝ)))*log 2 := by
  have hL0 : 0 ≤ L := (log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hL
  simp only [candidateProfile,correctedProfile,centeredProfile,
    if_pos (by omega : 1 ≤ X),if_pos hX,Nat.cast_one,log_one,
    Nat.cast_ofNat,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,
    sub_zero,max_eq_right hL0,max_eq_right (sub_nonneg.mpr hL)]
  ring

/-- A fixed early slope persists uniformly in the moving order. -/
theorem candidate_first_step_le {X N : ℕ} (hX : 2 ≤ X) (hN : 4 ≤ N)
    {L : ℝ} (hL : log 2 ≤ L) :
    candidateProfile X N L 1-candidateProfile X N L 2 ≤ -log 2/4 := by
  have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : log (2 : ℝ) ≤ 1 := by
    linarith only [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hd : log (2 : ℝ)/(3*(N : ℝ)) ≤ 1/12 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3*(N : ℝ))).mpr
    linarith only [hNR,hlog]
  rw [candidate_first_step hX hL]
  nlinarith only [hd,log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

/-- Unlike the original flat-before-L profile, this correction always
activates the coherent first channel. -/
theorem candidate_first_active {X N : ℕ} (hX : 2 ≤ X) (hN : 4 ≤ N)
    {L : ℝ} (hL : log 2 ≤ L) :
    1 ∈ activeCutoffs X (candidateProfile X N L) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
  have hs := candidate_first_step_le hX hN hL
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  intro he
  rw [he,sub_self] at hs
  linarith only [hs,hlog]

/-- The actual squared energy must now include the entire common
moment. This is a necessary cost, not an estimate of that moment. -/
theorem candidate_phaseEnergy_common_lower {X N : ℕ} (hX : 2 ≤ X) (hN : 4 ≤ N)
    {L : ℝ} (hL : log 2 ≤ L) (S : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ S,w n)^2 ≤ phaseEnergy X S w (candidateProfile X N L) :=
  phaseEnergy_one_lower X S w _ (candidate_first_active hX hN hL)

/-- The first adverse contribution has a fixed signed source cost.
All counts and label phases stay inside ONE common moment. -/
theorem candidate_negativeCost_common_lower {X N : ℕ} (hX : 2 ≤ X) (hN : 4 ≤ N)
    {L : ℝ} (hL : log 2 ≤ L) (S : Finset ℕ) (w : ℕ → ℝ) :
    max (∑ n ∈ S,w n) 0*log 2/4 ≤
      negativeCost X S w (candidateProfile X N L) := by
  let M := ∑ n ∈ S,w n
  by_cases hm : 0 < M
  · have hs := candidate_first_step_le hX hN hL
    have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have hstep : candidateProfile X N L 1-candidateProfile X N L 2 < 0 := by
      linarith only [hs,hlog]
    have hbad : (∑ n ∈ S,w n)*
        (candidateProfile X N L 1-candidateProfile X N L 2) < 0 :=
      mul_neg_of_pos_of_neg hm hstep
    have hb := negativeCost_one_lower X S w _ (candidate_first_active hX hN hL) hbad
    rw [max_eq_left hm.le]
    have hh := mul_le_mul_of_nonneg_left hs hm.le
    linarith only [hb,hh]
  · rw [max_eq_right (le_of_not_gt hm)]
    simp only [zero_mul,zero_div]
    exact sqrt_nonneg _

open ZetaRieszParityPacket ZetaRieszAnnulusJoint

/-- This necessary common-moment cost applies to the original literal
core and its exact source-normalized phase/allocation weight. The
arithmetic magnitude of the moment is still an OPEN estimate. -/
theorem native_candidate_common_lower {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    {N : ℕ} (hN : 65536 ≤ N) (K : ℕ) (y : ℝ)
    (hS : (coreBand u N K).Nonempty) :
    let S := coreBand u N K
    let X := max 1 (S.sup id)
    let A := intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    max (∑ n ∈ S.filter Squarefree,w n) 0*log 2/4 ≤
      negativeCost X (S.filter Squarefree) w (candidateProfile X N L) := by
  let S := coreBand u N K
  let X := max 1 (S.sup id)
  have hX : 2 ≤ X := by
    obtain ⟨n,hn⟩ := hS
    have hc := core_count hn
    have hn2 : 2 ≤ n := by
      by_contra h
      have : n=0 ∨ n=1 := by omega
      rcases this with rfl|rfl <;> simp at hc
    exact hn2.trans ((Finset.le_sup (f := id) hn).trans (le_max_right _ _))
  have hL : log (2 : ℝ) ≤ SquarefreeVaughanLogSource.length u N := by
    have hh := length_ge_rational hN hu hU
    have hNR : (65536 : ℝ) ≤ N := by exact_mod_cast hN
    have hl := log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith only [hh,hNR,hl]
  exact candidate_negativeCost_common_lower hX (by omega : 4 ≤ N) hL _ _

end RiemannGaussian.ZetaRieszNullProfileAudit

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszDirectPhaseFloor

/-!
# Signed antiphase credit after joining every count and cutoff

The actual adverse cutoff set is fixed by the whole original sum. Sum its
divisor Gram first, then retain a NEGATIVE credit on opposite-phase pairs
whose joined Gram is nonnegative. Only the squared phase mismatch is paid.
No count, radial period, owner or physical label is independently clipped.

The credit is literal, not a numerical lower bound on its size. The signed
rest minus this credit still needs the independent whole-floor estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszAntiphaseCredit
open ZetaRieszCofactorPhaseEnergy ZetaRieszDiagonalPayment
open ZetaRieszNearLabelPayment ZetaRieszPhaseOrbitPayment
open ZetaRieszJointPrimeEnergy ZetaRieszJointAllocation
open ZetaRieszSmoothOwnerDiscrepancy ZetaRieszWideOwnerAudit
open ZetaRieszCutoffPeriodFloor ZetaRieszPostHingeEnergy

/-- Every retained pair uses the SAME original adverse cutoff set. -/
def cutoffGram (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (n m : ℕ) : ℝ :=
  ∑ k ∈ ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f,
    sharp k n*sharp k m/(k : ℝ)

/-- The already unpaid family, with no new count or owner restriction. -/
def retainedPair (N : ℕ) (y : ℝ) (n m : ℕ) : Prop :=
  ¬(N : ℝ)/1000 < log (Nat.gcd n m) ∧
    ¬nearPair (exp (-(N : ℝ)/1000)) n m ∧
    ¬logNear (phaseOffsets y N) (phaseWidth y N) n m

/-- Join cutoffs BEFORE using the sign of a divisor interaction. -/
theorem nonOrbitEnergy_eq_gram (X N : ℕ) (S : Finset ℕ)
    (w f : ℕ → ℝ) (y : ℝ) :
    nonOrbitEnergy X N S w f y = ∑ n ∈ S,∑ m ∈ S.erase n,
      if retainedPair N y n m then w n*w m*cutoffGram X S w f n m else 0 := by
  unfold nonOrbitEnergy
  simp only [Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  unfold retainedPair cutoffGram
  split_ifs with hg hd ho
  all_goals simp_all only [not_true_eq_false,not_false_eq_true,and_true,
    false_and,and_false,zero_div,Finset.sum_const_zero]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- All odd half-periods in the finite original label range. -/
def antiphaseOffsets (y : ℝ) (N : ℕ) : Finset ℝ :=
  (Finset.Icc (-(phaseRadius y N : ℤ)-1) (phaseRadius y N : ℤ)).image
    (fun k : ℤ => (2*(k : ℝ)+1)*Real.pi/y)

/-- Fixed-height capacity of the complete finite odd-period union. -/
def antiphaseCount (y : ℝ) : ℝ := phaseCount y+1

/-- Wider than the old norm-paid band. Its credit is NOT discarded. -/
def antiphaseWidth (y : ℝ) (N : ℕ) : ℝ :=
  exp (-(N : ℝ)/10000)/(1+|y|)

theorem antiphaseOffsets_symm (y : ℝ) (N : ℕ) :
    ∀ a ∈ antiphaseOffsets y N,-a ∈ antiphaseOffsets y N := by
  rintro a ha
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp ha
  refine Finset.mem_image.mpr ⟨-k-1,Finset.mem_Icc.mpr ?_,?_⟩
  · obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hk
    constructor <;> omega
  · push_cast
    ring

theorem antiphaseOffsets_card_le (y : ℝ) (N : ℕ) :
    ((antiphaseOffsets y N).card : ℝ) ≤ antiphaseCount y*((N : ℝ)+1) := by
  have hh := Finset.card_image_le
    (s := Finset.Icc (-(phaseRadius y N : ℤ)-1) (phaseRadius y N : ℤ))
    (f := fun k : ℤ => (2*(k : ℝ)+1)*Real.pi/y)
  have hc : (antiphaseOffsets y N).card ≤ 2*phaseRadius y N+2 := by
    unfold antiphaseOffsets
    rw [Int.card_Icc] at hh
    omega
  have h : ((antiphaseOffsets y N).card : ℝ) ≤ (2*phaseRadius y N+2 : ℕ) := by
    exact_mod_cast hc
  simp only [antiphaseCount,phaseCount,phaseRadius,Nat.cast_add,Nat.cast_mul,
    Nat.cast_ofNat,Nat.cast_one] at h ⊢
  nlinarith only [h,Nat.cast_nonneg (α := ℝ) N]

theorem antiphaseWidth_bounds {y : ℝ} (hy : 3 ≤ |y|) (N : ℕ) :
    0 ≤ antiphaseWidth y N ∧ antiphaseWidth y N ≤ 1/4 ∧
      |y| * antiphaseWidth y N ≤ exp (-(N : ℝ)/10000) ∧
      antiphaseWidth y N ≤ exp (-(N : ℝ)/10000) := by
  have hden : 0 < 1+|y| := by positivity
  have he : exp (-(N : ℝ)/10000) ≤ 1 := exp_le_one_iff.mpr
    (by linarith only [Nat.cast_nonneg (α := ℝ) N])
  unfold antiphaseWidth
  refine ⟨by positivity,?_,?_,?_⟩
  · apply (div_le_iff₀ hden).mpr
    linarith only [hy,he]
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [exp_pos (-(N : ℝ)/10000)]
  · exact div_le_self (exp_pos _).le (by linarith only [abs_nonneg y])

/-- No odd phase period on the literal finite label range is omitted. -/
theorem antiphaseNear_of_resonance {X N n m : ℕ} {y ε : ℝ} (hy : 1 ≤ y)
    (hεu : ε ≤ 1) (hn : n ∈ Finset.Icc 1 X) (hm : m ∈ Finset.Icc 1 X)
    (hX : log X ≤ 3*((N : ℝ)+1)) {k : ℤ}
    (hk : |y*(log n-log m)-(2*(k : ℝ)+1)*Real.pi| ≤ y*ε) :
    logNear (antiphaseOffsets y N) ε n m := by
  have hy0 : 0 < y := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hnX : log n ≤ log X := log_le_log hn0
    (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
  have hmX : log m ≤ log X := log_le_log hm0
    (by exact_mod_cast (Finset.mem_Icc.mp hm).2)
  have hdiff : |log n-log m| ≤ 3*((N : ℝ)+1) := by
    rw [abs_le]
    constructor <;> linarith only [hnX,hmX,hX,log_natCast_nonneg n,log_natCast_nonneg m]
  have ht : |(2*(k : ℝ)+1)*Real.pi| ≤ y*(4*((N : ℝ)+1)) := by
    have ha := abs_sub_le ((2*(k : ℝ)+1)*Real.pi) (y*(log n-log m)) 0
    simp only [sub_zero] at ha
    have hh := mul_le_mul_of_nonneg_left hdiff hy0.le
    rw [abs_sub_comm ((2*(k : ℝ)+1)*Real.pi),abs_mul y,abs_of_pos hy0] at ha
    have he := mul_le_mul_of_nonneg_left hεu hy0.le
    linarith only [ha,hk,hh,he,mul_nonneg hy0.le (Nat.cast_nonneg (α := ℝ) N)]
  have hodd : |2*(k : ℝ)+1| ≤ y*(4*((N : ℝ)+1)) := by
    rw [abs_mul,abs_of_pos Real.pi_pos] at ht
    have hh := mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ Real.pi by linarith only [Real.pi_gt_three]) (abs_nonneg (2*(k : ℝ)+1))
    nlinarith only [ht,hh]
  have htwo : 2*|(k : ℝ)| ≤ |2*(k : ℝ)+1|+1 := by
    have hh := abs_sub (2*(k : ℝ)+1) 1
    rw [show 2*(k : ℝ)+1-1=2*(k : ℝ) by ring,abs_mul] at hh
    norm_num at hh
    exact hh
  have hY : y ≤ (⌈|y|⌉₊ : ℝ) := by simpa only [abs_of_pos hy0] using Nat.le_ceil |y|
  have hkQ : |(k : ℝ)| ≤ (phaseRadius y N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hY (show 0 ≤ 4*((N : ℝ)+1) by positivity)
    simp only [phaseRadius,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    nlinarith only [hodd,htwo,hh,Nat.cast_nonneg (α := ℝ) N,abs_nonneg (k : ℝ)]
  have hki : k ∈ Finset.Icc (-(phaseRadius y N : ℤ)-1) (phaseRadius y N : ℤ) := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp hkQ
    have hlo' : -(phaseRadius y N : ℤ) ≤ k := by exact_mod_cast hlo
    exact Finset.mem_Icc.mpr ⟨by omega,by exact_mod_cast hhi⟩
  refine ⟨(2*(k : ℝ)+1)*Real.pi/y,Finset.mem_image.mpr ⟨k,hki,rfl⟩,?_⟩
  have he : log n-log m-(2*(k : ℝ)+1)*Real.pi/y=
      (y*(log n-log m)-(2*(k : ℝ)+1)*Real.pi)/y := by field_simp
  rw [he,abs_div,abs_of_pos hy0]
  exact (div_le_iff₀ hy0).mpr (by linarith only [hk])

/-- Opposite product phases give a SQUARE mismatch, not a linear error. -/
theorem antiphase_cos_sum_bound {y : ℝ} (hy : 3 ≤ |y|) (N n m : ℕ)
    (h : logNear (antiphaseOffsets y N) (antiphaseWidth y N) n m) :
    |cos (y*log n)+cos (y*log m)| ≤ exp (-(N : ℝ)/10000) := by
  have hy0 : y ≠ 0 := by intro h; norm_num [h] at hy
  obtain ⟨a,ha,hclose⟩ := h
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp ha
  have hcos : cos (y*log m+(2*(k : ℝ)+1)*Real.pi) = -cos (y*log m) := by
    rw [show y*log m+(2*(k : ℝ)+1)*Real.pi =
      (y*log m+Real.pi)+(k : ℝ)*(2*Real.pi) by ring,
      cos_add_int_mul_two_pi,cos_add_pi]
  have he : y*log n-(y*log m+(2*(k : ℝ)+1)*Real.pi) =
      y*(log n-log m-(2*(k : ℝ)+1)*Real.pi/y) := by field_simp; ring
  have hb := abs_cos_sub_cos_le (y*log n)
    (y*log m+(2*(k : ℝ)+1)*Real.pi)
  rw [he,abs_mul] at hb
  rw [hcos,sub_neg_eq_add] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left hclose (abs_nonneg y)).trans
    (antiphaseWidth_bounds hy N).2.2.1)

/-- The nonnegative envelope is exact; its full allocation is retained. -/
def amplitude (A : Finset ℕ) (L u : ℝ) (N n : ℕ) : ℝ :=
  u^(N+1)*(1-boundedShare A N n)*radial N (log n)/L/(n : ℝ)

theorem amplitude_nonneg (A : Finset ℕ) {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u)
    (N n : ℕ) : 0 ≤ amplitude A L u N n := by
  unfold amplitude
  exact div_nonneg (div_nonneg
    (mul_nonneg (mul_nonneg (pow_nonneg hu _) (sub_nonneg.mpr (boundedShare_bounds A N n).2))
      (radial_bounds N (log_natCast_nonneg n)).1) (by linarith)) (Nat.cast_nonneg n)

theorem weight_eq_amplitude (A : Finset ℕ) (L u y : ℝ) (N n : ℕ) :
    u^(N+1)*primeWeight A L y N n 1 =
      -amplitude A L u N n*cos (y*log n) := by
  simp only [primeWeight,amplitude,radial,one_mul,Nat.cast_one,log_one,zero_add,mul_one]
  ring

theorem amplitude_le (A : Finset ℕ) {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u)
    (N : ℕ) {n : ℕ} (hn : 0 < n) :
    amplitude A L u N n ≤ (u^(N+1)*radialCap N)/(n : ℝ) := by
  have he := weight_eq_amplitude A L u 0 N n
  simp only [zero_mul,cos_zero,mul_one] at he
  have hb := mul_le_mul_of_nonneg_left (primeWeight_total_le A N 0 hL hn)
    (pow_nonneg hu (N+1))
  rw [← abs_of_nonneg (pow_nonneg hu (N+1)),← abs_mul,he,abs_neg,
    abs_of_nonneg (amplitude_nonneg A hL hu N n)] at hb
  rw [abs_of_nonneg (pow_nonneg hu (N+1))] at hb
  exact hb.trans_eq (by ring)

/-- Select only after the ORIGINAL cutoffs have been jointly summed. -/
def creditedPair (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ) (n m : ℕ) : Prop :=
  retainedPair N y n m ∧
    logNear (antiphaseOffsets y N) (antiphaseWidth y N) n m ∧
    0 ≤ cutoffGram X S w f n m

/-- Every other correlation remains literal and signed. -/
def signedRest (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ S,∑ m ∈ S.erase n,
    if creditedPair X N S w f y n m then 0 else
      if retainedPair N y n m then w n*w m*cutoffGram X S w f n m else 0

/-- Explicit NEGATIVE quadratic credit, joined across every prime count. -/
def reserve (X N : ℕ) (A S : Finset ℕ) (L u y : ℝ) (f : ℕ → ℝ) : ℝ :=
  let w := fun n => u^(N+1)*primeWeight A L y N n 1
  ∑ n ∈ S,∑ m ∈ S.erase n,if creditedPair X N S w f y n m then
    amplitude A L u N n*amplitude A L u N m*cutoffGram X S w f n m*
      (cos (y*log n)^2+cos (y*log m)^2)/2 else 0

/-- Only the squared failure of exact antiphase matching is an error. -/
def leakage (X N : ℕ) (A S : Finset ℕ) (L u y : ℝ) (f : ℕ → ℝ) : ℝ :=
  let w := fun n => u^(N+1)*primeWeight A L y N n 1
  ∑ n ∈ S,∑ m ∈ S.erase n,if creditedPair X N S w f y n m then
    amplitude A L u N n*amplitude A L u N m*cutoffGram X S w f n m*
      (cos (y*log n)+cos (y*log m))^2/2 else 0

theorem reserve_nonneg (X N : ℕ) (A S : Finset ℕ) {L u : ℝ}
    (hL : 1 ≤ L) (hu : 0 ≤ u) (y : ℝ) (f : ℕ → ℝ) :
    0 ≤ reserve X N A S L u y f := by
  apply Finset.sum_nonneg
  intro n _
  apply Finset.sum_nonneg
  intro m _
  split_ifs with h
  · exact div_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (amplitude_nonneg A hL hu N n) (amplitude_nonneg A hL hu N m)) h.2.2)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))) (by norm_num)
  · exact le_rfl

theorem leakage_nonneg (X N : ℕ) (A S : Finset ℕ) {L u : ℝ}
    (hL : 1 ≤ L) (hu : 0 ≤ u) (y : ℝ) (f : ℕ → ℝ) :
    0 ≤ leakage X N A S L u y f := by
  apply Finset.sum_nonneg
  intro n _
  apply Finset.sum_nonneg
  intro m _
  split_ifs with h
  · exact div_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (amplitude_nonneg A hL hu N n) (amplitude_nonneg A hL hu N m)) h.2.2)
      (sq_nonneg _)) (by norm_num)
  · exact le_rfl

/-- Exact signed cancellation INSIDE the original whole energy.
Neither the rest nor the reserve is charged by an absolute allowance. -/
theorem nonOrbitEnergy_eq_rest_sub_reserve_add_leakage (X N : ℕ) (A S : Finset ℕ)
    (L u y : ℝ) (f : ℕ → ℝ) :
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    nonOrbitEnergy X N S w f y = signedRest X N S w f y-
      reserve X N A S L u y f+leakage X N A S L u y f := by
  dsimp only
  rw [nonOrbitEnergy_eq_gram]
  simp only [signedRest,reserve,leakage,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  by_cases hc : creditedPair X N S (fun n => u^(N+1)*primeWeight A L y N n 1) f y n m
  · simp only [if_pos hc,if_pos hc.1]
    rw [weight_eq_amplitude A L u y N n,weight_eq_amplitude A L u y N m]
    ring
  · simp only [if_neg hc]
    split_ifs <;> ring

/-- Used only on leakage. The reserve keeps the actual joined Gram. -/
theorem cutoffGram_bound (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    |cutoffGram X S w f n m| ≤
      (1+log X)*(n.divisors.card : ℝ)*(m.divisors.card : ℝ) := by
  let K := ZetaRieszRejoinedPhaseFloor.negativeCutoffs X S w f
  have hK : K ⊆ Finset.Icc 1 X := by
    intro k hk
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1
  have hh : (∑ k ∈ K,(k : ℝ)⁻¹) ≤ 1+log X :=
    (Finset.sum_le_sum_of_subset_of_nonneg hK (fun _ _ _ => by positivity)).trans
      (by simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
        using harmonic_le_one_add_log X)
  calc
    _ ≤ ∑ k ∈ K,|sharp k n*sharp k m/(k : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ K,((n.divisors.card : ℝ)*(m.divisors.card : ℝ))/(k : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      have ha : |(k : ℝ)|=(k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
      rw [abs_div,abs_mul,ha]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (abs_sharp_le hn k) (abs_sharp_le hm k) (abs_nonneg _) (by positivity))
        (Nat.cast_nonneg k)
    _ = (∑ k ∈ K,(k : ℝ)⁻¹)*((n.divisors.card : ℝ)*(m.divisors.card : ℝ)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ _ := (mul_le_mul_of_nonneg_right hh (by positivity)).trans_eq (by ring)

/-- Capacity across ALL odd phase periods; no density or count premise. -/
theorem antiphase_pair_mass_bound (X N : ℕ) (S : Finset ℕ) {y : ℝ}
    (hy : 3 ≤ |y|) (hX : S ⊆ Finset.Icc 1 X) (hS : S ⊆ literalWindow N) :
    (∑ n ∈ S,∑ m ∈ S,if logNear (antiphaseOffsets y N) (antiphaseWidth y N) n m then
      ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) ≤
      5*antiphaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/10000)*
        exp (log X/262144)*divisorSquareDirichletMass (1+1/262144) := by
  have hl n (hn : n ∈ S) : exp ((7/4 : ℝ)*N) ≤ (n : ℝ) := by
    have hp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp (hX hn)).1
    have hh := ((mem_literalWindow N n).mp (hS hn)).1
    exact (exp_le_exp.mpr hh.le).trans_eq (exp_log hp)
  obtain ⟨he0,he,_,hew⟩ := antiphaseWidth_bounds hy N
  have hb := logNear_pair_mass_bound X S (antiphaseOffsets y N) hX
    (antiphaseOffsets_symm y N) he0 he hl
  have hi : exp (-((7/4 : ℝ)*N)) ≤ exp (-(N : ℝ)/10000) :=
    exp_le_exp.mpr (by nlinarith only [Nat.cast_nonneg (α := ℝ) N])
  have hh : 4*antiphaseWidth y N+exp (-((7/4 : ℝ)*N)) ≤
      5*exp (-(N : ℝ)/10000) := by linarith only [hew,hi]
  have hprod := mul_le_mul (antiphaseOffsets_card_le y N) hh (by positivity)
    (show 0 ≤ antiphaseCount y*((N : ℝ)+1) by unfold antiphaseCount phaseCount; positivity)
  exact hb.trans ((mul_le_mul_of_nonneg_right hprod
    (by positivity [divisorSquareDirichletMass_nonneg (1+1/262144)])).trans_eq (by ring))

/-- The ONLY absolute pair cost is the squared mismatch. The literal
negative reserve is absent from the right-hand side and remains unspent. -/
theorem leakage_bound (X N : ℕ) (A S : Finset ℕ) (f : ℕ → ℝ) {y L u : ℝ}
    (hy : 3 ≤ |y|) (hL : 1 ≤ L) (hu : 0 ≤ u)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hwin : S ⊆ literalWindow N) :
    leakage X N A S L u y f ≤
      (1+log X)*(u^(N+1)*radialCap N)^2*
        (5*antiphaseCount y*((N : ℝ)+1)*exp (-(3/10000 : ℝ)*N)*
          exp (log X/262144)*divisorSquareDirichletMass (1+1/262144)) := by
  let w := fun n => u^(N+1)*primeWeight A L y N n 1
  let V := u^(N+1)*radialCap N
  let H := 1+log X
  let C := H*V^2*exp (-(N : ℝ)/5000)
  let P := ∑ n ∈ S,∑ m ∈ S,
    if logNear (antiphaseOffsets y N) (antiphaseWidth y N) n m then
      ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0
  have hH : 0 ≤ H := by
    have hh : (1 : ℝ) ≤ X := by exact_mod_cast hX
    dsimp [H]
    linarith [log_nonneg hh]
  have hV : 0 ≤ V := by dsimp [V]; positivity [radialCap_nonneg N]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hterm n (hn : n ∈ S) m (hm : m ∈ S) :
      (if creditedPair X N S w f y n m then
        amplitude A L u N n*amplitude A L u N m*cutoffGram X S w f n m*
          (cos (y*log n)+cos (y*log m))^2/2 else 0) ≤
      C*(if logNear (antiphaseOffsets y N) (antiphaseWidth y N) n m then
        ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) := by
    by_cases hc : creditedPair X N S w f y n m
    · rw [if_pos hc,if_pos hc.2.1]
      have hn0 := (Finset.mem_Icc.mp (hS hn)).1
      have hm0 := (Finset.mem_Icc.mp (hS hm)).1
      have ha0 := amplitude_nonneg A hL hu N n
      have hb0 := amplitude_nonneg A hL hu N m
      have hab := mul_le_mul (amplitude_le A hL hu N hn0)
        (amplitude_le A hL hu N hm0) hb0 (div_nonneg hV (Nat.cast_nonneg n))
      have hg : cutoffGram X S w f n m ≤ H*(n.divisors.card : ℝ)*(m.divisors.card : ℝ) :=
        (le_abs_self _).trans (cutoffGram_bound X S w f hn0 hm0)
      have hbase := mul_le_mul hab hg hc.2.2 (by positivity : 0 ≤ (V/(n : ℝ))*(V/(m : ℝ)))
      have hs := (sq_le_sq₀ (abs_nonneg _) (exp_pos (-(N : ℝ)/10000)).le).mpr
        (antiphase_cos_sum_bound hy N n m hc.2.1)
      have he : exp (-(N : ℝ)/10000)^2=exp (-(N : ℝ)/5000) := by
        rw [pow_two,← exp_add]
        congr 1
        ring
      rw [sq_abs,he] at hs
      have hb := mul_le_mul hbase hs (sq_nonneg _)
        (show 0 ≤ (V/(n : ℝ))*(V/(m : ℝ))*(H*(n.divisors.card : ℝ)*(m.divisors.card : ℝ)) by positivity)
      calc
        _ ≤ amplitude A L u N n*amplitude A L u N m*cutoffGram X S w f n m*
            (cos (y*log n)+cos (y*log m))^2 := div_le_self
              (mul_nonneg (mul_nonneg (mul_nonneg ha0 hb0) hc.2.2) (sq_nonneg _)) (by norm_num)
        _ ≤ _ := hb
        _ = _ := by dsimp [C]; ring
    · rw [if_neg hc]
      split_ifs <;> positivity
  have hb : leakage X N A S L u y f ≤ C*P := by
    calc
      _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,C*
          (if logNear (antiphaseOffsets y N) (antiphaseWidth y N) n m then
            ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) :=
        Finset.sum_le_sum (fun n hn => Finset.sum_le_sum
          (fun m hm => hterm n hn m (Finset.mem_of_mem_erase hm)))
      _ ≤ ∑ n ∈ S,∑ m ∈ S,C*
          (if logNear (antiphaseOffsets y N) (antiphaseWidth y N) n m then
            ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) :=
        Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset _ _) (fun _ _ _ => by split_ifs <;> positivity))
      _ = _ := by simp only [P,Finset.mul_sum]
  have hmass := mul_le_mul_of_nonneg_left (antiphase_pair_mass_bound X N S hy hS hwin) hC
  apply hb.trans (hmass.trans_eq ?_)
  dsimp [C,H,V]
  have he : exp (-(N : ℝ)/5000)*exp (-(N : ℝ)/10000)=
      exp (-(3/10000 : ℝ)*N) := by rw [← exp_add]; congr 1; ring
  rw [← he]
  ring

/-- Capacity contributes one width, and the cosine identity contributes
TWO MORE. Their combined rate beats the true squared source growth. -/
theorem antiphase_source_rate {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (N : ℕ) :
    (2*u)^(2*(N+1))*exp ((3/262144-3/10000 : ℝ)*N) ≤
      4*radiusCeiling^2*exp (-(1/20000 : ℝ)*N) := by
  have hlog := ZetaRieszManyBinRateAudit.radius_growth_bounds.2
  have hr : 0 < 2*radiusCeiling := by norm_num [radiusCeiling]
  have he : (2*radiusCeiling)^(2*(N+1)) =
      4*radiusCeiling^2*exp (2*(N : ℝ)*log (2*radiusCeiling)) := by
    rw [show 2*(N+1)=2*N+2 by omega,pow_add,pow_two]
    have hpow : (2*radiusCeiling)^(2*N)=
        exp (((2*N : ℕ) : ℝ)*log (2*radiusCeiling)) := by rw [exp_nat_mul,exp_log hr]
    rw [hpow]
    push_cast
    ring
  calc
    _ ≤ (2*radiusCeiling)^(2*(N+1))*exp ((3/262144-3/10000 : ℝ)*N) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity : 0 ≤ 2*u) (by linarith : 2*u≤2*radiusCeiling) _)
        (exp_pos _).le
    _ = 4*radiusCeiling^2*exp
        ((2*log (2*radiusCeiling)+3/262144-3/10000)*(N : ℝ)) := by
      rw [he,mul_assoc,← exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by
      nlinarith only [hlog,Nat.cast_nonneg (α := ℝ) N])) (by positivity)

/-- Fixed-height constant, finite but unevaluated. -/
def leakageConstant (y : ℝ) : ℝ :=
  80*radiusCeiling^2*antiphaseCount y*
    divisorSquareDirichletMass (1+1/262144)*exp (3/262144)

/-- The vanishing price of phase mismatch, leaving the reserve signed. -/
def leakagePrice (y : ℝ) (N : ℕ) : ℝ :=
  sqrt (4*leakageConstant y)*((N : ℝ)+1)^3*exp (-(1/40000 : ℝ)*N)

private theorem leakageConstant_nonneg (y : ℝ) : 0 ≤ leakageConstant y := by
  unfold leakageConstant antiphaseCount phaseCount
  positivity [divisorSquareDirichletMass_nonneg (1+1/262144)]

/-- An unconditional, source-scale geometric payment of leakage ONLY.
All original counts, allocation and prime/label masks remain joined. -/
theorem weighted_leakage_bound (X N : ℕ) (A S : Finset ℕ) (f : ℕ → ℝ)
    {y L u : ℝ} (hy : 3 ≤ |y|) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hwin : S ⊆ literalWindow N)
    (hlog : log X ≤ 3*((N : ℝ)+1)) :
    leakage X N A S L u y f ≤
      leakageConstant y*((N : ℝ)+1)^4*exp (-(1/20000 : ℝ)*N) := by
  let V := u^(N+1)*radialCap N
  have hb := leakage_bound X N A S f hy hL hu hX hS hwin
  have hh : 1+log X ≤ 4*((N : ℝ)+1) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have he : exp (log X/262144) ≤
      exp (3/262144)*exp ((3/262144 : ℝ)*N) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    linarith only [hlog]
  have hprod := mul_le_mul hh he (exp_pos _).le (show 0 ≤ 4*((N : ℝ)+1) by positivity)
  have hvpow : V^2=((N : ℝ)+1)^2*(2*u)^(2*(N+1)) := by
    dsimp [V,radialCap]
    rw [show 2*(N+1)=(N+1)*2 by omega,pow_mul]
    simp only [mul_pow]
    ring
  have hQ : 0 ≤ V^2*(5*antiphaseCount y*((N : ℝ)+1)*exp (-(3/10000 : ℝ)*N))*
      divisorSquareDirichletMass (1+1/262144) := by
    positivity [divisorSquareDirichletMass_nonneg (1+1/262144),
      show 0 ≤ antiphaseCount y by unfold antiphaseCount phaseCount; positivity]
  have hc := mul_le_mul_of_nonneg_right hprod hQ
  have hg := mul_le_mul_of_nonneg_left (antiphase_source_rate hu hU N)
    (show 0 ≤ 20*antiphaseCount y*((N : ℝ)+1)^4*
      divisorSquareDirichletMass (1+1/262144)*exp (3/262144) by
      positivity [divisorSquareDirichletMass_nonneg (1+1/262144),
        show 0 ≤ antiphaseCount y by unfold antiphaseCount phaseCount; positivity])
  calc
    _ ≤ (1+log X)*V^2*(5*antiphaseCount y*((N : ℝ)+1)*exp (-(3/10000 : ℝ)*N)*
        exp (log X/262144)*divisorSquareDirichletMass (1+1/262144)) := hb
    _ = ((1+log X)*exp (log X/262144))*
        (V^2*(5*antiphaseCount y*((N : ℝ)+1)*exp (-(3/10000 : ℝ)*N))*
          divisorSquareDirichletMass (1+1/262144)) := by ring
    _ ≤ (4*((N : ℝ)+1)*(exp (3/262144)*exp ((3/262144 : ℝ)*N)))*
        (V^2*(5*antiphaseCount y*((N : ℝ)+1)*exp (-(3/10000 : ℝ)*N))*
          divisorSquareDirichletMass (1+1/262144)) := hc
    _ = (20*antiphaseCount y*((N : ℝ)+1)^4*
        divisorSquareDirichletMass (1+1/262144)*exp (3/262144))*
          ((2*u)^(2*(N+1))*exp ((3/262144-3/10000 : ℝ)*N)) := by
      rw [hvpow]
      have ht : exp ((3/262144 : ℝ)*N)*exp (-(3/10000 : ℝ)*N)=
          exp ((3/262144-3/10000 : ℝ)*N) := by rw [← exp_add]; congr 1; ring
      rw [← ht]
      ring
    _ ≤ _ := hg.trans_eq (by unfold leakageConstant; ring)

/-- Keep the NEGATIVE reserve inside the price, rather than spending it
as an absolute error. The original adverse cutoff set is never changed. -/
theorem cost_le_rest_sub_reserve (X N : ℕ) (A S : Finset ℕ) {L u : ℝ}
    (hL : 1 ≤ L) (hu : 0 ≤ u) (y : ℝ) (f : ℕ → ℝ) {P : ℝ} (hP : 0 ≤ P) :
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    sqrt (max (nonOrbitEnergy X N S w f y) 0*P) ≤
      sqrt (max (signedRest X N S w f y-reserve X N A S L u y f) 0*P)+
        sqrt (leakage X N A S L u y f*P) := by
  let w := fun n => u^(N+1)*primeWeight A L y N n 1
  have he := nonOrbitEnergy_eq_rest_sub_reserve_add_leakage X N A S L u y f
  have hl := leakage_nonneg X N A S hL hu y f
  have hm : max (nonOrbitEnergy X N S w f y) 0 ≤
      max (signedRest X N S w f y-reserve X N A S L u y f) 0+
        leakage X N A S L u y f := by
    apply max_le
    · rw [he]
      linarith only [le_max_left (signedRest X N S w f y-reserve X N A S L u y f) 0]
    · exact add_nonneg (le_max_right _ _) hl
  have hb := mul_le_mul_of_nonneg_right hm hP
  have hA : 0 ≤ max (signedRest X N S w f y-reserve X N A S L u y f) 0*P := by positivity
  have hB : 0 ≤ leakage X N A S L u y f*P := mul_nonneg hl hP
  have hC : 0 ≤ max (nonOrbitEnergy X N S w f y) 0*P := by positivity
  dsimp only
  apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [sq_sqrt hC]
  nlinarith only [hb,sq_sqrt hA,sq_sqrt hB,
    mul_nonneg (sqrt_nonneg (max (signedRest X N S w f y-reserve X N A S L u y f) 0*P))
      (sqrt_nonneg (leakage X N A S L u y f*P))]

theorem weighted_leakage_price (X N : ℕ) (A S : Finset ℕ) (f : ℕ → ℝ)
    {y L u P : ℝ} (hy : 3 ≤ |y|) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hwin : S ⊆ literalWindow N)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hP : 0 ≤ P) (hPu : P ≤ 4*((N : ℝ)+1)^2) :
    sqrt (leakage X N A S L u y f*P) ≤ leakagePrice y N := by
  have he := weighted_leakage_bound X N A S f hy hL hu hU hX hS hwin hlog
  have hleak := leakage_nonneg X N A S hL hu y f
  have hC := leakageConstant_nonneg y
  have hp := mul_le_mul he hPu hP
    (by positivity : 0 ≤ leakageConstant y*((N : ℝ)+1)^4*exp (-(1/20000 : ℝ)*N))
  have hprice : 0 ≤ leakagePrice y N := by unfold leakagePrice; positivity
  apply (sq_le_sq₀ (sqrt_nonneg _) hprice).mp
  have hs : (leakagePrice y N)^2 =
      (leakageConstant y*((N : ℝ)+1)^4*exp (-(1/20000 : ℝ)*N))*(4*((N : ℝ)+1)^2) := by
    unfold leakagePrice
    rw [mul_pow,mul_pow,sq_sqrt (by positivity : 0 ≤ 4*leakageConstant y),
      pow_two (exp _),← exp_add]
    have hrat : -(1/40000 : ℝ)*N+ -(1/40000 : ℝ)*N= -(1/20000 : ℝ)*N := by ring
    rw [hrat]
    ring
  rw [hs,sq_sqrt (mul_nonneg hleak hP)]
  exact hp

theorem tendsto_leakagePrice (y : ℝ) : Tendsto (leakagePrice y) atTop (𝓝 0) := by
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    (exp_pos (-(1/40000 : ℝ))) (exp_lt_one_iff.mpr (by norm_num : -(1/40000 : ℝ) < 0))
  have hh := ht.const_mul (sqrt (4*leakageConstant y))
  simpa only [mul_zero] using hh.congr' (Eventually.of_forall fun N => by
    unfold leakagePrice
    rw [← exp_nat_mul]
    rw [show exp ((N : ℝ)*(-(1/40000)))=exp (-(1/40000)*(N : ℝ)) by congr 1; ring]
    ring)

/-- A signed upper estimate on the WHOLE remaining energy. The negative
credit is kept; only its geometric leakage is added back. -/
theorem energy_le_rest_sub_reserve (X N : ℕ) (A S : Finset ℕ) (f : ℕ → ℝ)
    {y L u : ℝ} (hy : 3 ≤ |y|) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hwin : S ⊆ literalWindow N)
    (hlog : log X ≤ 3*((N : ℝ)+1)) :
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    nonOrbitEnergy X N S w f y ≤
      signedRest X N S w f y-reserve X N A S L u y f+
        leakageConstant y*((N : ℝ)+1)^4*exp (-(1/20000 : ℝ)*N) := by
  dsimp only
  rw [nonOrbitEnergy_eq_rest_sub_reserve_add_leakage]
  exact add_le_add le_rfl (weighted_leakage_bound X N A S f hy hL hu hU hX hS hwin hlog)

open ZetaRieszParityPacket ZetaRieszAnnulusJoint

/-- Native WHOLE-floor comparison after signed antiphase cancellation.
Every count and original literal mask is retained. This is not the final
numerical floor: the rest minus the literal credit still needs its bound. -/
theorem joined_floor {u y : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (hy : 3 ≤ |y|) {N : ℕ} (hN : 65536 ≤ N) (K : ℕ) :
    let A := intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let S := coreBand u N K
    let X := max 1 (S.sup id)
    let f := correctedProfile X L 1 0
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    -sqrt (max (signedRest X N (S.filter Squarefree) w f y-
      reserve X N A (S.filter Squarefree) L u y f) 0*((129/200 : ℝ)*N))-
      ZetaRieszDirectPhaseFloor.joinedError u y N K-leakagePrice y N ≤
        ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N K
  let X := max 1 (S.sup id)
  let f := correctedProfile X L 1 0
  let w := fun n => u^(N+1)*primeWeight A L y N n 1
  have hX : 0 < X := by dsimp [X]; omega
  have hwin : S ⊆ literalWindow N := ZetaRieszDirectPhaseFloor.core_subset_window u N K
  have hswin := (Finset.filter_subset Squarefree S).trans hwin
  have hSX : S.filter Squarefree ⊆ Finset.Icc 1 X := by
    intro n hn
    obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hs.ne_zero,
      (Finset.le_sup (f := id) hn).trans (le_max_right _ _)⟩
  have hlog : log X ≤ 3*((N : ℝ)+1) := window_sup_log S hwin
  have hL : 1 ≤ L := by
    have hh := length_ge_rational hN hu hU
    have hn : (65536 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [L]
    linarith
  have hp : 0 ≤ (129/200 : ℝ)*N := by positivity
  have hpu : (129/200 : ℝ)*N ≤ 4*((N : ℝ)+1)^2 := by
    nlinarith only [Nat.cast_nonneg (α := ℝ) N]
  have hfloor := ZetaRieszDirectPhaseFloor.joined_floor hu hU hy hN K
  have hcost := cost_le_rest_sub_reserve X N A (S.filter Squarefree) hL hu.le y f hp
  have hprice := weighted_leakage_price X N A (S.filter Squarefree) f hy hL hu.le hU
    hX hSX hswin hlog hp hpu
  dsimp only at hfloor hcost hprice ⊢
  linarith only [hfloor,hcost,hprice]

/-- The additional price is source-o(1) for FIXED phase height. No zero
or independent cancellation assumption enters either paid error. -/
theorem tendsto_joined_error {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (y : ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => ZetaRieszDirectPhaseFloor.joinedError u y (orders t) (counts t)+
      leakagePrice y (orders t)) atTop (𝓝 0) := by
  simpa only [add_zero,Function.comp_def] using
    (ZetaRieszDirectPhaseFloor.tendsto_joinedError hu hU y orders counts ho).add
      ((tendsto_leakagePrice y).comp ho)

/-- Signed credit on the ORIGINAL cofinal order/count schedule. The
independent small bound on rest-minus-reserve remains an explicit open task. -/
theorem eventually_joined_floor {u y : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (hy : 54 ≤ y) :
    ∀ᶠ j : ℕ in atTop,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := coreBand u N K
      let X := max 1 (S.sup id)
      let f := correctedProfile X L 1 0
      let w := fun n => u^(N+1)*primeWeight A L y N n 1;
      -sqrt (max (signedRest X N (S.filter Squarefree) w f y-
        reserve X N A (S.filter Squarefree) L u y f) 0*((129/200 : ℝ)*N))-
        ZetaRieszDirectPhaseFloor.joinedError u y N K-leakagePrice y N ≤
          ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (eventually_ge_atTop (65536 : ℕ))] with j hj
  exact joined_floor hu hU (by rw [abs_of_pos (by linarith : 0 < y)]; linarith) hj _

end RiemannGaussian.ZetaRieszAntiphaseCredit

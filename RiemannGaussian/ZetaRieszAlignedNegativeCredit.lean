/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAntiphaseCredit
import RiemannGaussian.ZetaRieszSharperCountPayment

/-!
# Negative joined Gram interactions at aligned label phases

The actual adverse cutoff set is selected once for the entire remaining
core. Positive joined Gram interactions at opposite phases have already
been retained as a negative credit. This module retains the complementary
negative-Gram, aligned-phase credit. Only its squared phase mismatch is
bounded absolutely, with an explicit source-scale geometric rate.

The two credits are disjoint by the sign of the SAME joined Gram. The
terminal inequality keeps both credits in the original joined floor.
Neither credit's native mass is bounded here: the combined signed rest
still needs its independent numerical budget. This is not a zero exclusion.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszAlignedNegativeCredit
open ZetaRieszCofactorPhaseEnergy ZetaRieszDiagonalPayment
open ZetaRieszNearLabelPayment ZetaRieszPhaseOrbitPayment
open ZetaRieszJointPrimeEnergy ZetaRieszJointAllocation
open ZetaRieszSmoothOwnerDiscrepancy ZetaRieszWideOwnerAudit
open ZetaRieszCutoffPeriodFloor ZetaRieszPostHingeEnergy
open ZetaRieszAntiphaseCredit

/-- Wider aligned phase band on the still unpaid pair population.
The old exponentially thinner alignment band remains excluded. -/
def alignedPair (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ) (n m : ℕ) : Prop :=
  retainedPair N y n m ∧
    logNear (phaseOffsets y N) (antiphaseWidth y N) n m ∧
    cutoffGram X S w f n m < 0

/-- Sign selection is made AFTER the whole original cutoff Gram is joined. -/
theorem alignedPair_not_creditedPair (X N : ℕ) (S : Finset ℕ)
    (w f : ℕ → ℝ) (y : ℝ) (n m : ℕ)
    (h : alignedPair X N S w f y n m) :
    ¬creditedPair X N S w f y n m := by
  intro ha
  exact (not_le.mpr h.2.2) ha.2.2

/-- Alignment controls a difference, whereas antiphase controls a sum. -/
theorem aligned_cos_diff_bound {y : ℝ} (hy : 3 ≤ |y|) (N n m : ℕ)
    (h : logNear (phaseOffsets y N) (antiphaseWidth y N) n m) :
    |cos (y*log n)-cos (y*log m)| ≤ exp (-(N : ℝ)/10000) := by
  have hy0 : y ≠ 0 := by intro h; norm_num [h] at hy
  obtain ⟨a,ha,hclose⟩ := h
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp ha
  have hcos : cos (y*log m+2*Real.pi*(k : ℝ)) = cos (y*log m) := by
    rw [show y*log m+2*Real.pi*(k : ℝ) =
      y*log m+(k : ℝ)*(2*Real.pi) by ring,cos_add_int_mul_two_pi]
  have he : y*log n-(y*log m+2*Real.pi*(k : ℝ)) =
      y*(log n-log m-2*Real.pi*(k : ℝ)/y) := by field_simp; ring
  have hb := abs_cos_sub_cos_le (y*log n) (y*log m+2*Real.pi*(k : ℝ))
  rw [he,abs_mul,hcos] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left hclose (abs_nonneg y)).trans
    (antiphaseWidth_bounds hy N).2.2.1)

/-- Explicit negative credit on the actual negative joined Gram. -/
def alignedReserve (X N : ℕ) (A S : Finset ℕ) (L u y : ℝ) (f : ℕ → ℝ) : ℝ :=
  let w := fun n => u^(N+1)*primeWeight A L y N n 1
  ∑ n ∈ S,∑ m ∈ S.erase n,if alignedPair X N S w f y n m then
    amplitude A L u N n*amplitude A L u N m*(-cutoffGram X S w f n m)*
      (cos (y*log n)^2+cos (y*log m)^2)/2 else 0

/-- Only the squared failure of phase agreement is an error. -/
def alignedLeakage (X N : ℕ) (A S : Finset ℕ) (L u y : ℝ) (f : ℕ → ℝ) : ℝ :=
  let w := fun n => u^(N+1)*primeWeight A L y N n 1
  ∑ n ∈ S,∑ m ∈ S.erase n,if alignedPair X N S w f y n m then
    amplitude A L u N n*amplitude A L u N m*(-cutoffGram X S w f n m)*
      (cos (y*log n)-cos (y*log m))^2/2 else 0

/-- Every other interaction remains signed, on the SAME adverse cutoff set. -/
def signedRemainder (X N : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ S,∑ m ∈ S.erase n,
    if creditedPair X N S w f y n m ∨ alignedPair X N S w f y n m then 0 else
      if retainedPair N y n m then w n*w m*cutoffGram X S w f n m else 0

/-- Nonnegativity does not supply a native lower bound on the reserve's mass. -/
theorem alignedReserve_nonneg (X N : ℕ) (A S : Finset ℕ) {L u : ℝ}
    (hL : 1 ≤ L) (hu : 0 ≤ u) (y : ℝ) (f : ℕ → ℝ) :
    0 ≤ alignedReserve X N A S L u y f := by
  apply Finset.sum_nonneg
  intro n _
  apply Finset.sum_nonneg
  intro m _
  split_ifs with h
  · exact div_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (amplitude_nonneg A hL hu N n) (amplitude_nonneg A hL hu N m))
        (neg_nonneg.mpr h.2.2.le))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))) (by norm_num)
  · exact le_rfl

theorem alignedLeakage_nonneg (X N : ℕ) (A S : Finset ℕ) {L u : ℝ}
    (hL : 1 ≤ L) (hu : 0 ≤ u) (y : ℝ) (f : ℕ → ℝ) :
    0 ≤ alignedLeakage X N A S L u y f := by
  apply Finset.sum_nonneg
  intro n _
  apply Finset.sum_nonneg
  intro m _
  split_ifs with h
  · exact div_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (amplitude_nonneg A hL hu N n) (amplitude_nonneg A hL hu N m))
        (neg_nonneg.mpr h.2.2.le)) (sq_nonneg _)) (by norm_num)
  · exact le_rfl

/-- Exact cancellation inside the previous SIGNED remainder, without
reselecting cutoffs, counts, owners, phases, or any literal mask. -/
theorem signedRest_eq_remainder_sub_alignedReserve_add_leakage
    (X N : ℕ) (A S : Finset ℕ) (L u y : ℝ) (f : ℕ → ℝ) :
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    signedRest X N S w f y = signedRemainder X N S w f y-
      alignedReserve X N A S L u y f+alignedLeakage X N A S L u y f := by
  dsimp only
  simp only [signedRest,signedRemainder,alignedReserve,alignedLeakage,
    ← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  by_cases hc : alignedPair X N S (fun n => u^(N+1)*primeWeight A L y N n 1) f y n m
  · have ha := alignedPair_not_creditedPair X N S _ f y n m hc
    simp only [if_pos hc,if_neg ha,if_pos (Or.inr hc),if_pos hc.1]
    rw [weight_eq_amplitude A L u y N n,weight_eq_amplitude A L u y N m]
    ring
  · by_cases ha : creditedPair X N S (fun n => u^(N+1)*primeWeight A L y N n 1) f y n m
    · simp only [if_pos ha,if_neg hc,if_pos (Or.inl ha)]
      ring
    · have hnone := not_or.mpr ⟨ha,hc⟩
      simp only [if_neg ha,if_neg hc,if_neg hnone]
      split_ifs <;> ring

/-- Both signs of joined Gram are handled in ONE exact whole-energy ledger. -/
theorem nonOrbitEnergy_eq_remainder_sub_reserves_add_leakages
    (X N : ℕ) (A S : Finset ℕ) (L u y : ℝ) (f : ℕ → ℝ) :
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    nonOrbitEnergy X N S w f y = signedRemainder X N S w f y-
      reserve X N A S L u y f-alignedReserve X N A S L u y f+
      leakage X N A S L u y f+alignedLeakage X N A S L u y f := by
  dsimp only
  rw [nonOrbitEnergy_eq_rest_sub_reserve_add_leakage,
    signedRest_eq_remainder_sub_alignedReserve_add_leakage]
  ring

/-- Capacity across ALL aligned phase periods; no density or count premise. -/
theorem aligned_pair_mass_bound (X N : ℕ) (S : Finset ℕ) {y : ℝ}
    (hy : 3 ≤ |y|) (hX : S ⊆ Finset.Icc 1 X) (hS : S ⊆ literalWindow N) :
    (∑ n ∈ S,∑ m ∈ S,if logNear (phaseOffsets y N) (antiphaseWidth y N) n m then
      ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) ≤
      5*antiphaseCount y*((N : ℝ)+1)*exp (-(N : ℝ)/10000)*
        exp (log X/262144)*divisorSquareDirichletMass (1+1/262144) := by
  have hl n (hn : n ∈ S) : exp ((7/4 : ℝ)*N) ≤ (n : ℝ) := by
    have hp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp (hX hn)).1
    have hh := ((mem_literalWindow N n).mp (hS hn)).1
    exact (exp_le_exp.mpr hh.le).trans_eq (exp_log hp)
  obtain ⟨he0,he,_,hew⟩ := antiphaseWidth_bounds hy N
  have hb := logNear_pair_mass_bound X S (phaseOffsets y N) hX
    (phaseOffsets_symm y N) he0 he hl
  have hi : exp (-((7/4 : ℝ)*N)) ≤ exp (-(N : ℝ)/10000) :=
    exp_le_exp.mpr (by nlinarith only [Nat.cast_nonneg (α := ℝ) N])
  have hh : 4*antiphaseWidth y N+exp (-((7/4 : ℝ)*N)) ≤
      5*exp (-(N : ℝ)/10000) := by linarith only [hew,hi]
  have hprod := mul_le_mul (show ((phaseOffsets y N).card : ℝ) ≤ antiphaseCount y*((N : ℝ)+1) by
    apply (phaseOffsets_card_le y N).trans
    unfold antiphaseCount
    nlinarith only [Nat.cast_nonneg (α := ℝ) N]) hh (by positivity)
    (show 0 ≤ antiphaseCount y*((N : ℝ)+1) by unfold antiphaseCount phaseCount; positivity)
  exact hb.trans ((mul_le_mul_of_nonneg_right hprod
    (by positivity [divisorSquareDirichletMass_nonneg (1+1/262144)])).trans_eq (by ring))

/-- The ONLY absolute pair cost is the squared mismatch. The literal
negative reserve is absent from the right-hand side and remains unspent. -/
theorem alignedLeakage_bound (X N : ℕ) (A S : Finset ℕ) (f : ℕ → ℝ) {y L u : ℝ}
    (hy : 3 ≤ |y|) (hL : 1 ≤ L) (hu : 0 ≤ u)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hwin : S ⊆ literalWindow N) :
    alignedLeakage X N A S L u y f ≤
      (1+log X)*(u^(N+1)*radialCap N)^2*
        (5*antiphaseCount y*((N : ℝ)+1)*exp (-(3/10000 : ℝ)*N)*
          exp (log X/262144)*divisorSquareDirichletMass (1+1/262144)) := by
  let w := fun n => u^(N+1)*primeWeight A L y N n 1
  let V := u^(N+1)*radialCap N
  let H := 1+log X
  let C := H*V^2*exp (-(N : ℝ)/5000)
  let P := ∑ n ∈ S,∑ m ∈ S,
    if logNear (phaseOffsets y N) (antiphaseWidth y N) n m then
      ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0
  have hH : 0 ≤ H := by
    have hh : (1 : ℝ) ≤ X := by exact_mod_cast hX
    dsimp [H]
    linarith [log_nonneg hh]
  have hV : 0 ≤ V := by dsimp [V]; positivity [radialCap_nonneg N]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hterm n (hn : n ∈ S) m (hm : m ∈ S) :
      (if alignedPair X N S w f y n m then
        amplitude A L u N n*amplitude A L u N m*(-cutoffGram X S w f n m)*
          (cos (y*log n)-cos (y*log m))^2/2 else 0) ≤
      C*(if logNear (phaseOffsets y N) (antiphaseWidth y N) n m then
        ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) := by
    by_cases hc : alignedPair X N S w f y n m
    · rw [if_pos hc,if_pos hc.2.1]
      have hn0 := (Finset.mem_Icc.mp (hS hn)).1
      have hm0 := (Finset.mem_Icc.mp (hS hm)).1
      have ha0 := amplitude_nonneg A hL hu N n
      have hb0 := amplitude_nonneg A hL hu N m
      have hab := mul_le_mul (amplitude_le A hL hu N hn0)
        (amplitude_le A hL hu N hm0) hb0 (div_nonneg hV (Nat.cast_nonneg n))
      have hg : -cutoffGram X S w f n m ≤ H*(n.divisors.card : ℝ)*(m.divisors.card : ℝ) :=
        (neg_le_abs _).trans (cutoffGram_bound X S w f hn0 hm0)
      have hbase := mul_le_mul hab hg (neg_nonneg.mpr hc.2.2.le) (by positivity : 0 ≤ (V/(n : ℝ))*(V/(m : ℝ)))
      have hs := (sq_le_sq₀ (abs_nonneg _) (exp_pos (-(N : ℝ)/10000)).le).mpr
        (aligned_cos_diff_bound hy N n m hc.2.1)
      have he : exp (-(N : ℝ)/10000)^2=exp (-(N : ℝ)/5000) := by
        rw [pow_two,← exp_add]
        congr 1
        ring
      rw [sq_abs,he] at hs
      have hb := mul_le_mul hbase hs (sq_nonneg _)
        (show 0 ≤ (V/(n : ℝ))*(V/(m : ℝ))*(H*(n.divisors.card : ℝ)*(m.divisors.card : ℝ)) by positivity)
      calc
        _ ≤ amplitude A L u N n*amplitude A L u N m*(-cutoffGram X S w f n m)*
            (cos (y*log n)-cos (y*log m))^2 := div_le_self
              (mul_nonneg (mul_nonneg (mul_nonneg ha0 hb0) (neg_nonneg.mpr hc.2.2.le)) (sq_nonneg _)) (by norm_num)
        _ ≤ _ := hb
        _ = _ := by dsimp [C]; ring
    · rw [if_neg hc]
      split_ifs <;> positivity
  have hb : alignedLeakage X N A S L u y f ≤ C*P := by
    calc
      _ ≤ ∑ n ∈ S,∑ m ∈ S.erase n,C*
          (if logNear (phaseOffsets y N) (antiphaseWidth y N) n m then
            ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) :=
        Finset.sum_le_sum (fun n hn => Finset.sum_le_sum
          (fun m hm => hterm n hn m (Finset.mem_of_mem_erase hm)))
      _ ≤ ∑ n ∈ S,∑ m ∈ S,C*
          (if logNear (phaseOffsets y N) (antiphaseWidth y N) n m then
            ((n.divisors.card : ℝ)/(n : ℝ))*((m.divisors.card : ℝ)/(m : ℝ)) else 0) :=
        Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset _ _) (fun _ _ _ => by split_ifs <;> positivity))
      _ = _ := by simp only [P,Finset.mul_sum]
  have hmass := mul_le_mul_of_nonneg_left (aligned_pair_mass_bound X N S hy hS hwin) hC
  apply hb.trans (hmass.trans_eq ?_)
  dsimp [C,H,V]
  have he : exp (-(N : ℝ)/5000)*exp (-(N : ℝ)/10000)=
      exp (-(3/10000 : ℝ)*N) := by rw [← exp_add]; congr 1; ring
  rw [← he]
  ring

/-- An unconditional, source-scale geometric payment of leakage ONLY; neither signed reserve is charged.
All original counts, allocation and prime/label masks remain joined. -/
theorem weighted_alignedLeakage_bound (X N : ℕ) (A S : Finset ℕ) (f : ℕ → ℝ)
    {y L u : ℝ} (hy : 3 ≤ |y|) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hwin : S ⊆ literalWindow N)
    (hlog : log X ≤ 3*((N : ℝ)+1)) :
    alignedLeakage X N A S L u y f ≤
      leakageConstant y*((N : ℝ)+1)^4*exp (-(1/20000 : ℝ)*N) := by
  let V := u^(N+1)*radialCap N
  have hb := alignedLeakage_bound X N A S f hy hL hu hX hS hwin
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


/-- The new signed main differs from the old one ONLY by the mismatch.
Thus adding a second credit is not an independent numerical energy saving. -/
theorem combinedMain_eq_previous_sub_leakage
    (X N : ℕ) (A S : Finset ℕ) (L u y : ℝ) (f : ℕ → ℝ) :
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    signedRemainder X N S w f y-reserve X N A S L u y f-
        alignedReserve X N A S L u y f =
      signedRest X N S w f y-reserve X N A S L u y f-
        alignedLeakage X N A S L u y f := by
  dsimp only
  rw [signedRest_eq_remainder_sub_alignedReserve_add_leakage]
  ring

/-- A genuine signed upper inequality on the entire actual energy.
Both credits remain negative; only the two geometric mismatches are paid. -/
theorem energy_le_remainder_sub_reserves (X N : ℕ) (A S : Finset ℕ) (f : ℕ → ℝ)
    {y L u : ℝ} (hy : 3 ≤ |y|) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hwin : S ⊆ literalWindow N)
    (hlog : log X ≤ 3*((N : ℝ)+1)) :
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    nonOrbitEnergy X N S w f y ≤
      signedRemainder X N S w f y-reserve X N A S L u y f-
        alignedReserve X N A S L u y f+
        2*leakageConstant y*((N : ℝ)+1)^4*exp (-(1/20000 : ℝ)*N) := by
  dsimp only
  rw [nonOrbitEnergy_eq_remainder_sub_reserves_add_leakages]
  have hanti := weighted_leakage_bound X N A S f hy hL hu hU hX hS hwin hlog
  have halign := weighted_alignedLeakage_bound X N A S f hy hL hu hU hX hS hwin hlog
  linarith only [hanti,halign]

/-- Exact old/new comparison: this cannot replace the missing global budget. -/
theorem previousMain_le_combinedMain_add_error (X N : ℕ) (A S : Finset ℕ) (f : ℕ → ℝ)
    {y L u : ℝ} (hy : 3 ≤ |y|) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hwin : S ⊆ literalWindow N)
    (hlog : log X ≤ 3*((N : ℝ)+1)) :
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    signedRest X N S w f y-reserve X N A S L u y f ≤
      signedRemainder X N S w f y-reserve X N A S L u y f-
        alignedReserve X N A S L u y f+
        leakageConstant y*((N : ℝ)+1)^4*exp (-(1/20000 : ℝ)*N) := by
  dsimp only
  have he := combinedMain_eq_previous_sub_leakage X N A S L u y f
  have hl := weighted_alignedLeakage_bound X N A S f hy hL hu hU hX hS hwin hlog
  dsimp only at he
  linarith only [he,hl]

/-- Independent one-sided payment of the literal newly selected branch.
This is an UPPER estimate, not a norm bound or a reserve lower estimate. -/
theorem aligned_contribution_upper_bound (X N : ℕ) (A S : Finset ℕ) (f : ℕ → ℝ)
    {y L u : ℝ} (hy : 3 ≤ |y|) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hwin : S ⊆ literalWindow N)
    (hlog : log X ≤ 3*((N : ℝ)+1)) :
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    signedRest X N S w f y-signedRemainder X N S w f y ≤
      leakageConstant y*((N : ℝ)+1)^4*exp (-(1/20000 : ℝ)*N) := by
  dsimp only
  rw [signedRest_eq_remainder_sub_alignedReserve_add_leakage]
  have hr := alignedReserve_nonneg X N A S hL hu y f
  have he := weighted_alignedLeakage_bound X N A S f hy hL hu hU hX hS hwin hlog
  linarith only [hr,he]

private theorem creditConstant_nonneg (y : ℝ) : 0 ≤ leakageConstant y := by
  unfold leakageConstant antiphaseCount phaseCount
  positivity [divisorSquareDirichletMass_nonneg (1+1/262144)]

/-- Price only the squared alignment mismatch. -/
theorem weighted_alignedLeakage_price (X N : ℕ) (A S : Finset ℕ) (f : ℕ → ℝ)
    {y L u P : ℝ} (hy : 3 ≤ |y|) (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (hX : 0 < X) (hS : S ⊆ Finset.Icc 1 X) (hwin : S ⊆ literalWindow N)
    (hlog : log X ≤ 3*((N : ℝ)+1)) (hP : 0 ≤ P) (hPu : P ≤ 4*((N : ℝ)+1)^2) :
    sqrt (alignedLeakage X N A S L u y f*P) ≤ leakagePrice y N := by
  have he := weighted_alignedLeakage_bound X N A S f hy hL hu hU hX hS hwin hlog
  have hleak := alignedLeakage_nonneg X N A S hL hu y f
  have hC := creditConstant_nonneg y
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

/-- Sum both signed credits BEFORE the whole-energy square root. -/
theorem cost_le_remainder_sub_reserves (X N : ℕ) (A S : Finset ℕ) {L u : ℝ}
    (hL : 1 ≤ L) (hu : 0 ≤ u) (y : ℝ) (f : ℕ → ℝ) {P : ℝ} (hP : 0 ≤ P) :
    let w := fun n => u^(N+1)*primeWeight A L y N n 1;
    sqrt (max (nonOrbitEnergy X N S w f y) 0*P) ≤
      sqrt (max (signedRemainder X N S w f y-reserve X N A S L u y f-
        alignedReserve X N A S L u y f) 0*P)+
        sqrt (leakage X N A S L u y f*P)+
        sqrt (alignedLeakage X N A S L u y f*P) := by
  let w := fun n => u^(N+1)*primeWeight A L y N n 1
  let Q := signedRemainder X N S w f y-reserve X N A S L u y f-
    alignedReserve X N A S L u y f
  have he := nonOrbitEnergy_eq_remainder_sub_reserves_add_leakages X N A S L u y f
  have hl := leakage_nonneg X N A S hL hu y f
  have ha := alignedLeakage_nonneg X N A S hL hu y f
  have hm : max (nonOrbitEnergy X N S w f y) 0 ≤
      max Q 0+leakage X N A S L u y f+alignedLeakage X N A S L u y f := by
    apply max_le
    · rw [he]
      dsimp [Q]
      linarith only [le_max_left Q 0]
    · exact add_nonneg (add_nonneg (le_max_right _ _) hl) ha
  have hb := mul_le_mul_of_nonneg_right hm hP
  have hA : 0 ≤ max Q 0*P := by positivity
  have hB : 0 ≤ leakage X N A S L u y f*P := mul_nonneg hl hP
  have hC : 0 ≤ alignedLeakage X N A S L u y f*P := mul_nonneg ha hP
  have hD : 0 ≤ max (nonOrbitEnergy X N S w f y) 0*P := by positivity
  dsimp only
  apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
  rw [sq_sqrt hD]
  nlinarith only [hb,sq_sqrt hA,sq_sqrt hB,sq_sqrt hC,
    mul_nonneg (sqrt_nonneg (max Q 0*P)) (sqrt_nonneg (leakage X N A S L u y f*P)),
    mul_nonneg (sqrt_nonneg (max Q 0*P)) (sqrt_nonneg (alignedLeakage X N A S L u y f*P)),
    mul_nonneg (sqrt_nonneg (leakage X N A S L u y f*P))
      (sqrt_nonneg (alignedLeakage X N A S L u y f*P))]

open ZetaRieszParityPacket ZetaRieszAnnulusJoint ZetaRieszPrimeCountFrequency

/-- Both credit branches apply to the CURRENT reduced count energy while
bounding the ORIGINAL joinedPhysical at its ORIGINAL count cutoff.
All errors occur once. The numerical signed budget is still unproved. -/
theorem eventually_joined_floor {u y : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (hy : 54 ≤ y) :
    ∀ᶠ j : ℕ in atTop,
      let N := dyadicMomentOrder j
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := coreBand u N (ZetaRieszSharperCountPayment.countCeiling j)
      let X := max 1 (S.sup id)
      let f := correctedProfile X L 1 0
      let w := fun n => u^(N+1)*primeWeight A L y N n 1;
      -sqrt (max (signedRemainder X N (S.filter Squarefree) w f y-
        reserve X N A (S.filter Squarefree) L u y f-
        alignedReserve X N A (S.filter Squarefree) L u y f) 0*((129/200 : ℝ)*N))-
        ZetaRieszSharperCountPayment.joinedError u y j-2*leakagePrice y N ≤
          ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  have hy' : 3 ≤ |y| := by rw [abs_of_pos (by linarith : 0 < y)]; linarith
  filter_upwards [ZetaRieszSharperCountPayment.eventually_joined_floor hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))] with j hj hN
  let N := dyadicMomentOrder j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (ZetaRieszSharperCountPayment.countCeiling j)
  let X := max 1 (S.sup id)
  let f := correctedProfile X L 1 0
  have hX : 0 < X := by dsimp [X]; omega
  have hwin : S ⊆ literalWindow N := ZetaRieszDirectPhaseFloor.core_subset_window u N _
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
  have hc := cost_le_remainder_sub_reserves X N A (S.filter Squarefree) hL hu.le y f hp
  have ha := weighted_leakage_price X N A (S.filter Squarefree) f hy' hL hu.le hU
    hX hSX hswin hlog hp hpu
  have hb := weighted_alignedLeakage_price X N A (S.filter Squarefree) f hy' hL hu.le hU
    hX hSX hswin hlog hp hpu
  dsimp only at hj hc ha hb ⊢
  linarith only [hj,hc,ha,hb]

/-- The paid prices vanish for fixed height. This does not bound the
signed remainder minus either reserve. -/
theorem tendsto_joined_error {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling) (y : ℝ) :
    Tendsto (fun j => ZetaRieszSharperCountPayment.joinedError u y j+
      2*leakagePrice y (dyadicMomentOrder j)) atTop (𝓝 0) := by
  have hp := ((tendsto_leakagePrice y).comp tendsto_dyadicMomentOrder).const_mul 2
  simpa only [add_zero,mul_zero,Function.comp_def] using
    (ZetaRieszSharperCountPayment.tendsto_joinedError hu hU y).add hp

end RiemannGaussian.ZetaRieszAlignedNegativeCredit

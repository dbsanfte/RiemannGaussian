/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerCurvatureFloor
import RiemannGaussian.ZetaRieszStaggeredFloor

set_option autoImplicit false

/-!
# Joint owner-factorial floors for the literal two-hinge prime fibre

Keep the owner allocation in the signed prime-period kernel. Freeze only
the two-hinge cofactor response, retaining its quarter slope and the exact
period width. No owner-allocation variation is charged. These are local
arithmetic inequalities; the source-normalized whole floor remains open.
-/

noncomputable section
open Set Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszJointOwnerFibreFloor
open ZetaRieszJointAllocation ZetaRieszFixedCountPeriod ZetaRieszSignedPeriodFloor
open ZetaRieszStaggeredFloor ZetaRieszAllowancePrimeBoxes
open ZetaRieszOwnerCurvatureFloor

/-- The exact quarter slope of the changing hinge. The second hinge is
constant on the largest-prime fibre and adds no variation. -/
theorem cofactor_response_variation_quarter {k : ℕ} (hk : 2 ≤ k) {v : ℝ} {a : ℕ}
    (ha : a ∈ cofactors k v) (L D E : ℝ) :
    |response L D a-response L E a| ≤ (2 : ℝ)^k/4*|D-E| := by
  have hd := cofactor_data ha
  have hh := ZetaRieszTentSlope.riesz_cutoff_lipschitz_quarter (D-L) (E-L) hd.1
    (by omega)
  rw [ZetaRieszTentSlope.absolute_divisor_mass_eq_card hd.1,
    ZetaRieszSmoothHead.card_divisors_of_squarefree hd.1,hd.2.1,
    Nat.cast_pow,Nat.cast_ofNat] at hh
  simp only [sub_sub_sub_cancel_right] at hh
  simp only [response,sub_sub_sub_cancel_right]
  exact hh.trans_eq (by ring)

/-- The negative curvature and prime endpoint cost of the joined owner
kernel. This is an explicit error budget, not another carrier. -/
def jointPeriodCost (N : ℕ) (v y b : ℝ) : ℝ :=
  (2*Real.pi/y)*((N : ℝ)+1)/((v-Real.pi/y)*(v-Real.pi/y-b)^2*y^2)+
    4/(v-Real.pi/y-b)^2

/-- The response displacement is the actual half-period, not a unit log
interval. At height at least 54 this is at most 1/64 of the old cutoff cost. -/
theorem quarter_period_width_le {y : ℝ} (hy : 54 ≤ y) :
    Real.pi/(4*y) ≤ 1/64 := by
  have hy0 : 0 < y := by linarith
  have hπ : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  calc
    _ = (Real.pi/y)/4 := by ring
    _ ≤ _ := by linarith

/-- Exact identification of the original owner-only signed part with
the joined factorial kernel. Both Riesz cutoffs and the phase are unchanged. -/
theorem owner_signedPart_fibre_eq {k : ℕ} (hk : 2 ≤ k) (e : ℝ) (A : Finset ℕ)
    {v y L : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y)
    (hL : (67/100 : ℝ)*v ≤ L) {a p : ℕ} (ha : a ∈ cofactors k v)
    (hp : p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y))
    (hpA : p ∈ A) (N : ℕ) :
    signedPart e (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L y N (p*a) =
      (1/L/a)*(e*partResponse e k L (Real.log p+Real.log a) a*
        (selectedAmplitude N (Finset.range (N+2)\ZetaRieszWingHighOrders.unpaidOrders N)
          (Real.log a) (Real.log p+Real.log a)*(p : ℝ)⁻¹*
            Real.cos (y*(Real.log p+Real.log a)))) := by
  have hyabs : |y| = y := abs_of_pos (by linarith)
  have hg := fibre_geometry hv (by rwa [hyabs]) ha (by simpa only [hyabs] using hp)
  have hd := cofactor_data ha
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hg.1.ne_zero)
      (by exact_mod_cast hd.1.ne_zero)]
  have he := selectedAmplitude_eq_fibre A N hd.1 (by omega) hg.1 hg.2.1 hpA
  rw [hlog] at he
  rw [signedPart_fibre_eq hk e _ hv hy hL ha hp,he]
  ring

set_option maxHeartbeats 800000 in
/-- A signed floor for the actual owner fibre. The old allocation
variation term is absent; only the quarter-slope half-period response
variation remains beside the joint curvature and prime endpoint costs. -/
theorem owner_signedPart_fibre_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e| = 1)
    (A : Finset ℕ) {v y L : ℝ} (hv : 100 ≤ v) (hNv : (N : ℝ)+2 ≤ v)
    (hy : 54 ≤ y) (hL : (67/100 : ℝ)*v ≤ L) {a : ℕ} (ha : a ∈ cofactors k v)
    (hlog : 5000 ≤ v-Real.pi/y-Real.log a)
    (hA : ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : Real.sin (y*v) = 0) (hsign : e*Real.cos (y*v) ≤ 0) :
    -(2*amplitude N v/(L*a))*
        (responseConstant k*Real.log a.minFac*jointPeriodCost N v y (Real.log a)+
          ((2 : ℝ)^k*Real.pi/(4*y))/(v-Real.pi/y-Real.log a)) ≤
      ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
        signedPart e (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L y N (p*a) := by
  let D := logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)
  let S := Finset.range (N+2)\ZetaRieszWingHighOrders.unpaidOrders N
  let R := fun p : ℕ => partResponse e k L (Real.log p+Real.log a) a
  let R₀ := partResponse e k L v a
  let w := fun p : ℕ => selectedAmplitude N S (Real.log a) (Real.log p+Real.log a)*(p : ℝ)⁻¹
  let g := fun p => w p*Real.cos (y*(Real.log p+Real.log a))
  let E := (2 : ℝ)^k*Real.pi/(4*y)
  let B := responseConstant k*Real.log a.minFac
  let W := 2*amplitude N v
  let b := v-Real.pi/y-Real.log a
  let c := e*R₀
  have hS : S ⊆ Finset.range (N+2) := Finset.sdiff_subset
  have hy0 : 0 < y := by linarith
  have hyabs : |y| = y := abs_of_pos hy0
  have hy' : 54 ≤ |y| := by rwa [hyabs]
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := by linarith
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hd := cofactor_data ha
  have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero hd.1.ne_zero
  have hB : 0 ≤ B := mul_nonneg (responseConstant_pos k).le (Real.log_natCast_nonneg _)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (amplitude_nonneg N hv0.le)
  have hcost : 0 ≤ jointPeriodCost N v y (Real.log a) := by
    have ht : 0 < v-Real.pi/y := by dsimp [b] at hb0; linarith [Real.log_natCast_nonneg a]
    unfold jointPeriodCost
    positivity
  have hgeo (p : ℕ) (hp : p ∈ D) := fibre_geometry hv hy' ha (by simpa only [hyabs] using hp)
  have hT (p : ℕ) (hp : p ∈ D) : Real.log a < Real.log p+Real.log a := by
    have hp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast (hgeo p hp).1.one_lt)
    linarith
  have hc : |c| ≤ B := by
    dsimp only [c,R₀]
    rw [abs_mul,he,one_mul]
    exact (partResponse_bound he k L v a).trans (cofactor_response_bound hk ha L v)
  have hcphase : c*Real.cos (y*v) ≤ 0 := by
    have hr : 0 ≤ R₀ := le_max_right _ _
    have hh := mul_nonpos_of_nonneg_of_nonpos hr hsign
    dsimp only [c]
    nlinarith only [hh]
  have hperiod := selected_period_floor S hS (Real.log_natCast_nonneg a) hlog hy hNv hpeak hcphase
  have hmass := (factorial_period_floor N hlog hy hNv hpeak (c := 0) (by simp)).2
  have hmass' : (∑ p ∈ D, w p) ≤ W/b := by
    have hm : (∑ p ∈ D, w p) ≤
        ∑ p ∈ D, amplitude N (Real.log p+Real.log a)*(p : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (selectedAmplitude_bounds S hS (Real.log_natCast_nonneg a) (hT p hp)).2
        (inv_nonneg.mpr (Nat.cast_nonneg p))
    exact hm.trans hmass
  have hw (p : ℕ) (hp : p ∈ D) : 0 ≤ w p :=
    mul_nonneg (selectedAmplitude_bounds S hS (Real.log_natCast_nonneg a) (hT p hp)).1
      (inv_nonneg.mpr (Nat.cast_nonneg p))
  have hg (p : ℕ) (hp : p ∈ D) : |g p| ≤ w p := by
    dsimp only [g]
    rw [abs_mul,abs_of_nonneg (hw p hp)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hw p hp)).trans_eq (mul_one _)
  have hR (p : ℕ) (hp : p ∈ D) : |R p-R₀| ≤ E := by
    have hpT := (hgeo p hp).2.2.2.2
    rw [hyabs] at hpT
    have hlogmul : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
      rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast (hgeo p hp).1.ne_zero)
        (by exact_mod_cast hd.1.ne_zero)]
    rw [hlogmul] at hpT
    have hdisp : |Real.log p+Real.log a-v| ≤ Real.pi/y :=
      abs_le.mpr ⟨by linarith [hpT.1],by linarith [hpT.2.1]⟩
    exact (((partResponse_variation he k L (Real.log p+Real.log a) v a).trans
      (cofactor_response_variation_quarter hk ha L _ _)).trans
        (mul_le_mul_of_nonneg_left hdisp (by positivity : (0 : ℝ) ≤ 2^k/4))).trans_eq
          (by dsimp [E]; ring)
  have herr : |e*(∑ p ∈ D, (R p-R₀)*g p)| ≤ E*(∑ p ∈ D, w p) := by
    rw [abs_mul,he,one_mul,Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun p hp => by
      rw [abs_mul]
      exact mul_le_mul (hR p hp) (hg p hp) (abs_nonneg _) hE)
  have hsplit : e*(∑ p ∈ D, R p*g p) =
      c*(∑ p ∈ D, g p)+e*(∑ p ∈ D, (R p-R₀)*g p) := by
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => by dsimp only [c]; ring)
  have hbound : -W*(B*jointPeriodCost N v y (Real.log a)+E/b) ≤
      e*(∑ p ∈ D, R p*g p) := by
    have hc' := mul_le_mul_of_nonneg_right hc (mul_nonneg hW hcost)
    have hm := mul_le_mul_of_nonneg_left hmass' hE
    have hs := hperiod
    have hh := (abs_le.mp herr).1
    change -2*|c| *amplitude N v*jointPeriodCost N v y (Real.log a) ≤ c*(∑ p ∈ D, g p) at hs
    rw [hsplit]
    dsimp only [W] at hc' hm ⊢
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hc',hm,hs,hh]
  have heq : (∑ p ∈ D,
      signedPart e (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L y N (p*a)) =
      (1/L/a)*(e*(∑ p ∈ D, R p*g p)) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [owner_signedPart_fibre_eq hk e A hv hy hL ha hp (hA p hp) N]
    dsimp only [R,g,w,S]
    ring
  change -(W/(L*a))*(B*jointPeriodCost N v y (Real.log a)+E/b) ≤ _
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 1/L/a by positivity)
  calc
    _ = (1/L/a)*(-W*(B*jointPeriodCost N v y (Real.log a)+E/b)) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ _ := hh

/-- Joining the allocation does not enlarge the coarse inverse-square
radial curvature/endpoint budget used by the current floor ledger. -/
theorem jointPeriodCost_le {N : ℕ} {v y b : ℝ} (hv : 100 ≤ v)
    (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y) (hb : b ≤ (197/200 : ℝ)*v) :
    jointPeriodCost N v y b ≤ 50000/v^2 := by
  have hv0 : 0 < v := by linarith
  have hy0 : 0 < y := by linarith
  have hπu : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have ha : v/100 ≤ v-Real.pi/y-b := by linarith
  have ha0 : 0 < v-Real.pi/y-b := (by positivity : 0 < v/100).trans_le ha
  have ht : v/2 ≤ v-Real.pi/y := by linarith
  have ht0 : 0 < v-Real.pi/y := (by positivity : 0 < v/2).trans_le ht
  have hhu : 2*Real.pi/y ≤ 1 :=
    (div_le_iff₀ hy0).mpr (by linarith [Real.pi_lt_four])
  have hnum : (2*Real.pi/y)*((N : ℝ)+1) ≤ v :=
    (mul_le_mul_of_nonneg_right hhu (by positivity)).trans (by linarith)
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ v/100) ha 2
  have hden : v^3/5000 ≤ (v-Real.pi/y)*(v-Real.pi/y-b)^2*y^2 := by
    calc
      _ = (v/2)*(v/100)^2*4 := by ring
      _ ≤ (v-Real.pi/y)*(v-Real.pi/y-b)^2*4 :=
        mul_le_mul_of_nonneg_right (mul_le_mul ht hsq (sq_nonneg _) ht0.le) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith : (4 : ℝ) ≤ y^2) (by positivity)
  have h₁ : (2*Real.pi/y)*((N : ℝ)+1)/((v-Real.pi/y)*(v-Real.pi/y-b)^2*y^2) ≤ 5000/v^2 := by
    calc
      _ ≤ v/((v-Real.pi/y)*(v-Real.pi/y-b)^2*y^2) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ v/(v^3/5000) := div_le_div_of_nonneg_left hv0.le (by positivity) hden
      _ = _ := by field_simp
  have h₂ : 4/(v-Real.pi/y-b)^2 ≤ 40000/v^2 := by
    calc
      _ ≤ 4/(v/100)^2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
      _ = _ := by ring
  unfold jointPeriodCost
  calc
    _ ≤ 5000/v^2+40000/v^2 := add_le_add h₁ h₂
    _ = 45000/v^2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg v)

/-- In the old radial ledger units, the allocation variation cost is
absent and the cutoff variation coefficient is 25/4 instead of 400. -/
theorem owner_signedPart_fibre_radial {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e| = 1)
    (A : Finset ℕ) {v y L : ℝ} (hv : 500000 ≤ v) (hNv : (N : ℝ)+2 ≤ v)
    (hy : 54 ≤ y) (hL : (67/100 : ℝ)*v ≤ L) {a : ℕ} (ha : a ∈ cofactors k v)
    (hA : ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : Real.sin (y*v) = 0) (hsign : e*Real.cos (y*v) ≤ 0) :
    -(amplitude N v/v)*
        ((200000*responseConstant k/v^2)*(Real.log a.minFac*(a : ℝ)⁻¹)+
          ((25/4 : ℝ)*(2 : ℝ)^k/v)*(a : ℝ)⁻¹) ≤
      ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
        signedPart e (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L y N (p*a) := by
  have hv100 : 100 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hy0 : 0 < y := by linarith
  have hd := cofactor_data ha
  have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero hd.1.ne_zero
  have hL0 : 0 < L := by linarith
  have hπ : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have ha' : v/100 ≤ v-Real.pi/y-Real.log a := by linarith [hd.2.2.2.2.1]
  have hlog : 5000 ≤ v-Real.pi/y-Real.log a := by linarith
  have hlog0 : 0 < v-Real.pi/y-Real.log a := by linarith
  have ht0 : 0 < v-Real.pi/y := by linarith [Real.log_natCast_nonneg a]
  let B := responseConstant k*Real.log a.minFac
  let E := (2 : ℝ)^k*Real.pi/(4*y)
  have hB : 0 ≤ B := mul_nonneg (responseConstant_pos k).le (Real.log_natCast_nonneg _)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hW : 0 ≤ amplitude N v := amplitude_nonneg N hv0.le
  have hC : 0 ≤ jointPeriodCost N v y (Real.log a) := by unfold jointPeriodCost; positivity
  have hpre : 2*amplitude N v/(L*a) ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹ := by
    have hh := div_le_div_of_nonneg_left (show 0 ≤ 2*amplitude N v by positivity)
      (show 0 < v/2 by positivity) (show v/2 ≤ L by linarith)
    have hm := mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr ha0.le)
    convert hm using 1 <;> first | rfl | (simp only [div_eq_mul_inv,mul_inv_rev]; ring)
  have hEbound : E ≤ (2 : ℝ)^k/64 := by
    have hh := mul_le_mul_of_nonneg_left (quarter_period_width_le hy)
      (by positivity : (0 : ℝ) ≤ 2^k)
    calc
      E = (2 : ℝ)^k*(Real.pi/(4*y)) := by dsimp [E]; ring
      _ ≤ (2 : ℝ)^k*(1/64) := hh
      _ = _ := by ring
  have hin : B*jointPeriodCost N v y (Real.log a)+E/(v-Real.pi/y-Real.log a) ≤
      B*(50000/v^2)+(25/16 : ℝ)*(2 : ℝ)^k/v := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (jointPeriodCost_le hv100 hNv hy hd.2.2.2.2.1) hB
    · calc
        _ ≤ E/(v/100) := div_le_div_of_nonneg_left hE (by positivity) ha'
        _ ≤ ((2 : ℝ)^k/64)/(v/100) := div_le_div_of_nonneg_right hEbound (by positivity)
        _ = _ := by ring
  have hpay := mul_le_mul hpre hin
    (by positivity : 0 ≤ B*jointPeriodCost N v y (Real.log a)+E/(v-Real.pi/y-Real.log a))
    (by positivity : 0 ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹)
  have heq : 4*(amplitude N v/v)*(a : ℝ)⁻¹*(B*(50000/v^2)+(25/16 : ℝ)*(2 : ℝ)^k/v) =
      (amplitude N v/v)*
        ((200000*responseConstant k/v^2)*(Real.log a.minFac*(a : ℝ)⁻¹)+
          ((25/4 : ℝ)*(2 : ℝ)^k/v)*(a : ℝ)⁻¹) := by dsimp [B]; ring
  rw [heq] at hpay
  have hfloor := owner_signedPart_fibre_floor hk he A hv100 hNv hy hL ha hlog hA hpeak hsign
  change -(2*amplitude N v/(L*a))*(B*jointPeriodCost N v y (Real.log a)+E/(v-Real.pi/y-Real.log a)) ≤ _ at hfloor
  rw [neg_mul] at hfloor
  simpa only [neg_mul] using (neg_le_neg hpay).trans hfloor

/-- All selected cofactor rows are joined before the bound. The exact
new population cost keeps the faster curvature term separate from the
remaining cutoff-variation term, with no order square-root charge. -/
theorem owner_signedPart_population_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e| = 1)
    (A S : Finset ℕ) {v y L : ℝ} (hv : 500000 ≤ v) (hNv : (N : ℝ)+2 ≤ v)
    (hy : 54 ≤ y) (hL : (67/100 : ℝ)*v ≤ L) (hS : S ⊆ cofactors k v)
    (hA : ∀ a ∈ S, ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : Real.sin (y*v) = 0) (hsign : e*Real.cos (y*v) ≤ 0) :
    -(amplitude N v/v)*
        (200000*responseConstant k*ZetaRieszCofactorMass.logMassConstant k/v+
          (25/4 : ℝ)*(2 : ℝ)^k*ZetaRieszCofactorMass.variationConstant k*v^(-(1/2 : ℝ))) ≤
      ∑ a ∈ S, ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
        signedPart e (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L y N (p*a) := by
  have hv0 : 0 < v := by linarith
  have hk0 : 0 < k := by omega
  have hC := ZetaRieszCofactorMass.constants_pos hk0
  have hB := responseConstant_pos k
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  let F := 200000*responseConstant k/v^2
  let G := (25/4 : ℝ)*(2 : ℝ)^k/v
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hrow := Finset.sum_le_sum (fun a (ha : a ∈ S) =>
    owner_signedPart_fibre_radial hk he A hv hNv hy hL (hS ha) (hA a ha) hpeak hsign)
  rw [← Finset.mul_sum] at hrow
  have hset : S ⊆ ZetaRieszCofactorMass.products k v := hS.trans (Finset.filter_subset _ _)
  have hmass : (∑ a ∈ S, (F*(Real.log a.minFac*(a : ℝ)⁻¹)+G*(a : ℝ)⁻¹)) ≤
      F*(ZetaRieszCofactorMass.logMassConstant k*v)+
        G*(ZetaRieszCofactorMass.variationConstant k*v^(1/2 : ℝ)) := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (ZetaRieszCofactorMass.log_mass hk0 hv0 S hset) hF)
      (mul_le_mul_of_nonneg_left (ZetaRieszCofactorMass.reciprocal_mass hk0 hv0 S hset) hG)
  have hrat : v^(1/2 : ℝ)/v = v^(-(1/2 : ℝ)) := by
    have hh := Real.rpow_sub hv0 (1/2 : ℝ) 1
    norm_num at hh
    exact hh.symm
  have heq : F*(ZetaRieszCofactorMass.logMassConstant k*v)+
      G*(ZetaRieszCofactorMass.variationConstant k*v^(1/2 : ℝ)) =
      200000*responseConstant k*ZetaRieszCofactorMass.logMassConstant k/v+
        (25/4 : ℝ)*(2 : ℝ)^k*ZetaRieszCofactorMass.variationConstant k*v^(-(1/2 : ℝ)) := by
    rw [← hrat]
    dsimp [F,G]
    field_simp
  have hpay := mul_le_mul_of_nonpos_left (hmass.trans_eq heq) (neg_nonpos.mpr hbase)
  exact hpay.trans hrow

private theorem signedPart_eq_indicator {e : ℝ} (he : |e| = 1)
    (A : Finset ℕ) (L y : ℝ) (N n : ℕ) :
    signedPart e A L y N n =
      ((if 0 ≤ e*(SquarefreeVaughanLogSource.coefficient L n).re then (1 : ℂ) else 0)*
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have heSq : e*e = 1 := by
    have hh := sq_abs e
    rw [he] at hh
    nlinarith only [hh]
  by_cases h : 0 ≤ e*(SquarefreeVaughanLogSource.coefficient L n).re
  · simp only [signedPart,if_pos h,one_mul,max_eq_left h,
      ZetaRieszOneSidedArithmetic.re_residual_atom]
    calc
      _ = ZetaRieszOneSidedArithmetic.weight A N n*
        ((SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n))*(e*e) := by ring
      _ = _ := by rw [heSq,mul_one]
  · simp only [signedPart,if_neg h,zero_mul,Complex.zero_re,
      max_eq_right (le_of_not_ge h),mul_zero]

/-- A single source-geometric payment transfers ANY literal signed part
from all allocation incidences to the owner. The coefficient-sign mask is
bounded and unchanged, so errors are not repeated per prime period. -/
theorem signedPart_owner_difference_bound {e : ℝ} (he : |e| = 1)
    (A : ℕ → Finset ℕ) (D : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ) (N : ℕ)
    (hD : D ⊆ literalWindow N) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    |u^(N+1)*((∑ n ∈ D, signedPart e (A n) L y N n)-
      ∑ n ∈ D, signedPart e (A n ∩ {ZetaRieszPrimeEndpoint.largestPrime n}) L y N n)| ≤
      (4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
        ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) := by
  let w : ℕ → ℂ := fun n =>
    if 0 ≤ e*(SquarefreeVaughanLogSource.coefficient L n).re then 1 else 0
  have hw n (_hn : n ∈ D) : ‖w n‖ ≤ 1 := by dsimp [w]; split_ifs <;> simp
  have hb := ZetaRieszNonownerAllocation.residual_sub_owner_bound A D w hL N hD hw y hu
    (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)
  have hh := (Complex.abs_re_le_norm _).trans hb
  have heq : ((u : ℂ)^(N+1)*∑ n ∈ D,
      w n*(residualCoefficient (A n) L N n-
        residualCoefficient (A n ∩ {ZetaRieszPrimeEndpoint.largestPrime n}) L N n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re =
      u^(N+1)*((∑ n ∈ D, signedPart e (A n) L y N n)-
        ∑ n ∈ D, signedPart e (A n ∩ {ZetaRieszPrimeEndpoint.largestPrime n}) L y N n) := by
    rw [← Complex.ofReal_pow,Complex.re_ofReal_mul]
    congr 1
    simp only [mul_sub,sub_mul,Finset.sum_sub_distrib,Complex.sub_re,Complex.re_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun n _ => (signedPart_eq_indicator he (A n) L y N n).symm)
    · exact Finset.sum_congr rfl (fun n _ =>
        (signedPart_eq_indicator he (A n ∩ {ZetaRieszPrimeEndpoint.largestPrime n}) L y N n).symm)
  rwa [heq] at hh

/-- The improved owner-population floor transfers to the ORIGINAL
literal allocation. Its single global nonowner error has a geometric
rate below 124/125, independently of counts and prime periods. -/
theorem literal_signedPart_population_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e| = 1)
    (A S : Finset ℕ) {v y L u : ℝ} (hv : 500000 ≤ v) (hNv : (N : ℝ)+2 ≤ v)
    (hy : 54 ≤ y) (hL : (67/100 : ℝ)*v ≤ L) (hS : S ⊆ cofactors k v)
    (hA : ∀ a ∈ S, ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : Real.sin (y*v) = 0) (hsign : e*Real.cos (y*v) ≤ 0)
    (hwindow : S.biUnion (fun a =>
      (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p)) ⊆
        literalWindow N)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    -u^(N+1)*(amplitude N v/v)*
        (200000*responseConstant k*ZetaRieszCofactorMass.logMassConstant k/v+
          (25/4 : ℝ)*(2 : ℝ)^k*ZetaRieszCofactorMass.variationConstant k*v^(-(1/2 : ℝ)))-
      (4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
        ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) ≤
      u^(N+1)*∑ a ∈ S, ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
        signedPart e A L y N (p*a) := by
  have hv100 : 100 ≤ v := by linarith
  have hL0 : 0 < L := by linarith
  let D := S.biUnion (fun a =>
    (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p))
  have hb := signedPart_owner_difference_bound he (fun _ => A) D hL0 y N hwindow hu hU
  have hlo := (abs_le.mp hb).1
  have hsum := sum_owned_real hv100 hy S hS (fun n => signedPart e A L y N n)
  have howner := sum_owned_real hv100 hy S hS (fun n =>
    signedPart e (A ∩ {ZetaRieszPrimeEndpoint.largestPrime n}) L y N n)
  rw [hsum,howner] at hlo
  have hrow := owner_signedPart_population_floor hk he A S hv hNv hy hL hS hA hpeak hsign
  have hscaled := mul_le_mul_of_nonneg_left hrow (pow_nonneg hu (N+1))
  nlinarith only [hlo,hscaled]

/-- On the actual linear radial core the moving Riesz length, ordinary
prime support and literal-window error hypotheses are discharged. The
sharper signed cost stays explicit; it is not replaced by a fixed epsilon
fraction of supply or claimed to decay after source normalization. -/
theorem eventually_core_signedPart_floor {k : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e| = 1)
    {u y : ℝ} (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) :
    ∀ᶠ N : ℕ in atTop, ∀ (v : ℝ) (S : Finset ℕ),
      (39/20 : ℝ)*N ≤ v-Real.pi/y → v+Real.pi/y ≤ (203/100 : ℝ)*N →
      S ⊆ cofactors k v → Real.sin (y*v) = 0 → e*Real.cos (y*v) ≤ 0 →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let P := S.biUnion (fun a =>
        (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p));
      -u^(N+1)*(amplitude N v/v)*
          (200000*responseConstant k*ZetaRieszCofactorMass.logMassConstant k/v+
            (25/4 : ℝ)*(2 : ℝ)^k*ZetaRieszCofactorMass.variationConstant k*v^(-(1/2 : ℝ)))-
        (4*((N : ℝ)+1)/3)*(ZetaRieszNonownerAllocation.nonownerRate^N*
          ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) ≤
        u^(N+1)*∑ n ∈ P, signedPart e A L y N n := by
  have hy0 : 0 < y := by linarith
  have hyabs : |y| = y := abs_of_pos hy0
  have hpi : 0 ≤ Real.pi/y := by positivity
  filter_upwards [eventually_core_geometry k hu hU hy,eventually_ge_atTop (1000000 : ℕ)]
    with N hgeo hN v S hlo hhi hS hpeak hsign
  have hNR : (1000000 : ℝ) ≤ N := by exact_mod_cast hN
  have hv100 : 100 ≤ v := by linarith
  have hvbig : 500000 ≤ v := by linarith
  have hNv : (N : ℝ)+2 ≤ v := by linarith
  have hvg := hgeo v (by linarith) (by linarith)
  have hwindow : S.biUnion (fun a =>
      (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p)) ⊆
      literalWindow N := by
    intro n hn
    obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    have hg := fibre_geometry hv100 (by rwa [hyabs]) (hS ha)
      (by simpa only [hyabs] using hp)
    rw [Nat.mul_comm a p]
    apply (mem_literalWindow N (p*a)).mpr
    rw [hyabs] at hg
    constructor <;> nlinarith [hg.2.2.2.2.1,hg.2.2.2.2.2.1]
  dsimp only
  rw [sum_owned_real hv100 hy S hS]
  exact literal_signedPart_population_floor hk he _ S hvbig hNv hy hvg.1 hS
    (fun a ha p hp => hvg.2 a (hS ha) p hp) hpeak hsign hwindow (by linarith) hU

end RiemannGaussian.ZetaRieszJointOwnerFibreFloor

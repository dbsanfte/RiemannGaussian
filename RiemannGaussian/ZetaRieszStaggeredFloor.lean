/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSignedPeriodFloor
import RiemannGaussian.ZetaRieszGammaJoint

/-!
# Staggered signed prime-period floors

Split the arithmetic coefficient, retaining the whole prime phase. Each
part is summed over a complete period with the opposite cosine extremum.
Taking a positive part does not increase the cofactor variation, so the
floor no longer selects cofactors by their frozen sign. Grid boundaries
and previously spent credits are not deleted by this estimate.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszStaggeredFloor
open ZetaRieszSignedPeriodFloor ZetaRieszFixedCountPeriod
open ZetaRieszQuantitativePrimePeriod
open ZetaRieszAllowancePrimeBoxes

/-- An exact arithmetic-sign part of the original real atom. The prime
phase is unchanged and is not replaced by its positive part. -/
def signedPart (e : ℝ) (A : Finset ℕ) (L y : ℝ) (N n : ℕ) : ℝ :=
  e*ZetaRieszOneSidedArithmetic.weight A N n*
    max (e*(SquarefreeVaughanLogSource.coefficient L n).re) 0*
      Real.cos (y*Real.log n)

/-- Both arithmetic signs recover the literal allocated atom exactly. -/
theorem signedPart_add (A : Finset ℕ) (L y : ℝ) (N n : ℕ) :
    signedPart 1 A L y N n+signedPart (-1) A L y N n =
      (ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  rw [ZetaRieszOneSidedArithmetic.re_residual_atom]
  unfold signedPart
  simp only [one_mul,neg_one_mul]
  by_cases h : 0 ≤ (SquarefreeVaughanLogSource.coefficient L n).re
  · rw [max_eq_left h,max_eq_right (by linarith :
      -(SquarefreeVaughanLogSource.coefficient L n).re ≤ 0)]
    ring
  · rw [max_eq_right (le_of_not_ge h),max_eq_left (by linarith :
      0 ≤ -(SquarefreeVaughanLogSource.coefficient L n).re)]
    ring

/-- Positive response before multiplying by the chosen arithmetic sign. -/
def partResponse (e : ℝ) (k : ℕ) (L T : ℝ) (a : ℕ) : ℝ :=
  max (e*(-(-1 : ℝ)^(k+1))*response L T a) 0

/-- Clipping arithmetic signs does not enlarge the response. -/
theorem partResponse_bound {e : ℝ} (he : |e| = 1) (k : ℕ) (L T : ℝ) (a : ℕ) :
    |partResponse e k L T a| ≤ |response L T a| := by
  rw [abs_of_nonneg (le_max_right _ _)]
  apply max_le _ (abs_nonneg _)
  calc
    _ ≤ |e*(-(-1 : ℝ)^(k+1))*response L T a| := le_abs_self _
    _ = _ := by rw [abs_mul,abs_mul,he]; simp

/-- Sign changes inside the period need no additional variation constant. -/
theorem partResponse_variation {e : ℝ} (he : |e| = 1) (k : ℕ) (L D E : ℝ) (a : ℕ) :
    |partResponse e k L D a-partResponse e k L E a| ≤
      |response L D a-response L E a| := by
  apply (abs_max_sub_max_le_abs _ _ 0).trans_eq
  rw [← mul_sub,abs_mul,abs_mul,he]
  simp

/-- The sign part is a literal original atom, including both Riesz hinges
and the original unassigned fraction. -/
theorem signedPart_fibre_eq {k : ℕ} (hk : 2 ≤ k) (e : ℝ) (A : Finset ℕ)
    {v y L : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y)
    (hL : (67/100 : ℝ)*v ≤ L) {a p : ℕ} (ha : a ∈ cofactors k v)
    (hp : p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)) (N : ℕ) :
    signedPart e A L y N (p*a) =
      (1/L/a)*(e*((1-ZetaRieszJointAllocation.boundedShare A N (p*a))*
        partResponse e k L (Real.log p+Real.log a) a*
        (amplitude N (Real.log p+Real.log a)*(p : ℝ)⁻¹*
          Real.cos (y*(Real.log p+Real.log a))))) := by
  have hyabs : |y| = y := abs_of_pos (by linarith)
  have hy' : 54 ≤ |y| := by rwa [hyabs]
  have hp' : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|) := by
    simpa only [hyabs] using hp
  have hg := fibre_geometry hv hy' ha hp'
  have hd := cofactor_data ha
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hg.1.ne_zero)
      (by exact_mod_cast hd.1.ne_zero)]
  have hL0 : 0 < L := by linarith
  have hT : 0 ≤ Real.log (p*a : ℕ)/L := div_nonneg (Real.log_natCast_nonneg _) hL0.le
  have hm : max (e*((-1 : ℝ)^(k+1)*(-(Real.log (p*a : ℕ)/L)*
        response L (Real.log (p*a : ℕ)) a))) 0 =
      (Real.log (p*a : ℕ)/L)*partResponse e k L (Real.log (p*a : ℕ)) a := by
    unfold partResponse
    rw [mul_max_of_nonneg _ _ hT,mul_zero]
    congr 1
    ring
  have hex : Real.exp (-(3/2 : ℝ)*Real.log (p*a : ℕ)) =
      Real.exp (-Real.log (p*a : ℕ)/2)*(p : ℝ)⁻¹*(a : ℝ)⁻¹ := by
    rw [show -(3/2 : ℝ)*Real.log (p*a : ℕ) =
      -Real.log (p*a : ℕ)/2-Real.log (p*a : ℕ) by ring,
      Real.exp_sub,Real.exp_log (by exact_mod_cast Nat.mul_pos hg.1.pos (Nat.pos_of_ne_zero hd.1.ne_zero)),Nat.cast_mul]
    ring
  rw [signedPart,ZetaRieszOneSidedArithmetic.weight,ZetaRieszOneSidedArithmetic.amplitude,
    coefficient_eq_response hk hv hy' hL ha hp',Complex.ofReal_re,hm,hex,hlog]
  unfold amplitude
  rw [pow_succ]
  ring

/-- Every cofactor is allowed. Only the orientation of the complete prime
period is chosen; no frozen cofactor-sign selection remains. -/
theorem signedPart_fibre_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e| = 1) (A : Finset ℕ)
    {v y L : ℝ} (hv : 100 ≤ v) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y)
    (hL : (67/100 : ℝ)*v ≤ L) {a : ℕ} (ha : a ∈ cofactors k v)
    (hlog : 5000 ≤ v-Real.pi/y-Real.log a)
    (hA : ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : Real.sin (y*v) = 0)
    (hsign : e*Real.cos (y*v) ≤ 0) :
    let E := (2 : ℝ)^k+3*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v*Real.log a.minFac;
    -(2*amplitude N v/(L*a))*
        (responseConstant k*Real.log a.minFac*periodCost N v y (Real.log a)+
          E/(v-Real.pi/y-Real.log a)) ≤
      ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
        signedPart e A L y N (p*a) := by
  let D := logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)
  let R := fun p : ℕ => (1-ZetaRieszJointAllocation.boundedShare A N (p*a))*
    partResponse e k L (Real.log p+Real.log a) a
  let w := fun p : ℕ => amplitude N (Real.log p+Real.log a)*(p : ℝ)⁻¹
  let g := fun p => w p*Real.cos (y*(Real.log p+Real.log a))
  let E := (2 : ℝ)^k+3*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v*Real.log a.minFac
  let B := responseConstant k*Real.log a.minFac
  let W := 2*amplitude N v
  let σ : ℝ := e
  let b := v-Real.pi/y-Real.log a
  have hy0 : 0 < y := by linarith
  have hyabs : |y| = y := abs_of_pos hy0
  have hy' : 54 ≤ |y| := by rwa [hyabs]
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := by linarith
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hd := cofactor_data ha
  have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero hd.1.ne_zero
  have hB : 0 ≤ B := mul_nonneg (responseConstant_pos k).le (Real.log_natCast_nonneg _)
  have hE : 0 ≤ E := by dsimp [E]; positivity [responseConstant_pos k,Real.log_natCast_nonneg a.minFac]
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (amplitude_nonneg N hv0.le)
  have hπ : 0 ≤ Real.pi/y := by positivity
  have hπu : Real.pi/y ≤ 1/16 := (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hcost : 0 ≤ periodCost N v y (Real.log a) := by
    have hb' : 0 < v-Real.pi/y-Real.log a := hb0
    unfold periodCost
    positivity
  change -(W/(L*a))*(B*periodCost N v y (Real.log a)+E/b) ≤ _
  by_cases hDn : D.Nonempty
  swap
  · have he : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hDn
    change -(W/(L*a))*(B*periodCost N v y (Real.log a)+E/b) ≤
      ∑ p ∈ D, signedPart e A L y N (p*a)
    rw [he,Finset.sum_empty]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
  obtain ⟨p₀,hp₀⟩ := hDn
  let R₀ := (1-ZetaRieszJointAllocation.boundedShare A N (p₀*a))*partResponse e k L v a
  let c := σ*R₀
  have hgeo (p : ℕ) (hp : p ∈ D) := fibre_geometry hv hy' ha (by simpa only [hyabs] using hp)
  have hlogmul (p : ℕ) (hp : p ∈ D) : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast (hgeo p hp).1.ne_zero)
      (by exact_mod_cast hd.1.ne_zero)]
  have hnot (p : ℕ) (hp : p ∈ D) : ¬p ∣ a := by
    intro hh
    exact ((hgeo p hp).2.1 p ((hgeo p hp).1.mem_primeFactors hh hd.1.ne_zero)).false
  have hθ (p : ℕ) : 0 ≤ 1-ZetaRieszJointAllocation.boundedShare A N (p*a) ∧
      1-ZetaRieszJointAllocation.boundedShare A N (p*a) ≤ 1 := by
    have hh := ZetaRieszJointAllocation.boundedShare_bounds A N (p*a)
    constructor <;> linarith
  have hσ : |σ| = 1 := he
  have hc : |c| ≤ B := by
    dsimp only [c,R₀]
    rw [abs_mul,hσ,one_mul,abs_mul,abs_of_nonneg (hθ p₀).1]
    exact (mul_le_mul (hθ p₀).2 ((partResponse_bound he k L v a).trans (cofactor_response_bound hk ha L v))
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
  have hcphase : c*Real.cos (y*v) ≤ 0 := by
    have hr : 0 ≤ partResponse e k L v a := le_max_right _ _
    have hh := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hθ p₀).1 hr) hsign
    dsimp [c,σ,R₀]
    nlinarith only [hh]
  have hperiod := factorial_period_floor N hlog hy hNv hpeak hcphase
  have hw (p : ℕ) (hp : p ∈ D) : 0 ≤ w p := by
    have hb := (logPrimes_bounds hp).2
    have ht : 0 ≤ Real.log p+Real.log a := by linarith [hb.1,Nat.cast_nonneg (α := ℝ) N]
    exact mul_nonneg (amplitude_nonneg N ht) (inv_nonneg.mpr (Nat.cast_nonneg p))
  have hg (p : ℕ) (hp : p ∈ D) : |g p| ≤ w p := by
    dsimp only [g]
    rw [abs_mul,abs_of_nonneg (hw p hp)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hw p hp)).trans_eq (mul_one _)
  have hR (p : ℕ) (hp : p ∈ D) : |R p-R₀| ≤ E := by
    have hpT := (hgeo p hp).2.2.2.2
    have hqT := (hgeo p₀ hp₀).2.2.2.2
    rw [hyabs] at hpT hqT
    have hdif : |Real.log (p*a : ℕ)-Real.log (p₀*a : ℕ)| ≤ 1/8 :=
      abs_le.mpr ⟨by linarith [hpT.1,hqT.2.1],by linarith [hpT.2.1,hqT.1]⟩
    have hs := ZetaRieszAllocationVariation.boundedShare_fibre_variation_985 A N hd.1 (by omega)
      (hgeo p hp).1 (hnot p hp) (hA p hp) (hgeo p₀ hp₀).1 (hnot p₀ hp₀) (hA p₀ hp₀)
      hv hπ hπu hd.2.2.2.2.1 ⟨hpT.1.le,hpT.2.1⟩ ⟨hqT.1.le,hqT.2.1⟩
    rw [hd.2.1] at hs
    have hshare : |ZetaRieszJointAllocation.boundedShare A N (p*a)-
        ZetaRieszJointAllocation.boundedShare A N (p₀*a)| ≤ 3*((k : ℝ)+1)*Real.sqrt (N+1)/v := by
      apply hs.trans
      have hh := mul_le_mul_of_nonneg_left hdif
        (show 0 ≤ 20*((k : ℝ)+1)*Real.sqrt (N+1)/v by positivity)
      have hz : 0 ≤ ((k : ℝ)+1)*Real.sqrt (N+1)/v := by positivity
      ring_nf at hh hz ⊢
      linarith only [hh,hz]
    have hdifv : |Real.log p+Real.log a-v| ≤ 1 := by
      rw [hlogmul p hp] at hpT
      exact abs_le.mpr ⟨by linarith [hpT.1],by linarith [hpT.2.1]⟩
    have hresp : |partResponse e k L (Real.log p+Real.log a) a-partResponse e k L v a| ≤ (2 : ℝ)^k :=
      ((partResponse_variation he k L (Real.log p+Real.log a) v a).trans
        (cofactor_response_variation hk ha L (Real.log p+Real.log a) v)).trans
        ((mul_le_mul_of_nonneg_left hdifv (by positivity : 0 ≤ (2 : ℝ)^k)).trans_eq (mul_one _))
    have hdecomp : R p-R₀ = (1-ZetaRieszJointAllocation.boundedShare A N (p*a))*
        (partResponse e k L (Real.log p+Real.log a) a-partResponse e k L v a)+
        (ZetaRieszJointAllocation.boundedShare A N (p₀*a)-
          ZetaRieszJointAllocation.boundedShare A N (p*a))*partResponse e k L v a := by dsimp [R,R₀]; ring
    rw [hdecomp]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg (hθ p).1,
      abs_sub_comm (ZetaRieszJointAllocation.boundedShare A N (p₀*a))]
    have h₁ := mul_le_mul (hθ p).2 hresp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have h₂ := mul_le_mul hshare ((partResponse_bound he k L v a).trans (cofactor_response_bound hk ha L v)) (abs_nonneg _)
      (by positivity : 0 ≤ 3*((k : ℝ)+1)*Real.sqrt (N+1)/v)
    dsimp only [E]
    ring_nf at h₁ h₂ ⊢
    linarith only [h₁,h₂]
  have herr : |σ*(∑ p ∈ D, (R p-R₀)*g p)| ≤ E*(∑ p ∈ D, w p) := by
    rw [abs_mul,hσ,one_mul,Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun p hp => by
      rw [abs_mul]
      exact mul_le_mul (hR p hp) (hg p hp) (abs_nonneg _) hE)
  have hsplit : σ*(∑ p ∈ D, R p*g p) =
      c*(∑ p ∈ D, g p)+σ*(∑ p ∈ D, (R p-R₀)*g p) := by
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [c]
    ring
  have hbound : -W*(B*periodCost N v y (Real.log a)+E/b) ≤ σ*(∑ p ∈ D, R p*g p) := by
    have hc' := mul_le_mul_of_nonneg_right hc (mul_nonneg hW hcost)
    have hm := mul_le_mul_of_nonneg_left hperiod.2 hE
    have hs := hperiod.1
    have he := (abs_le.mp herr).1
    change -2*|c| *amplitude N v*periodCost N v y (Real.log a) ≤ c*(∑ p ∈ D, g p) at hs
    change E*(∑ p ∈ D, w p) ≤ E*(W/b) at hm
    rw [hsplit]
    dsimp only [W] at hc' hm ⊢
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hc',hm,hs,he]
  have heq : (∑ p ∈ D, signedPart e A L y N (p*a)) =
      (1/L/a)*(σ*(∑ p ∈ D, R p*g p)) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [signedPart_fibre_eq hk e A hv hy hL ha hp]
  change _ ≤ ∑ p ∈ D, signedPart e A L y N (p*a)
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 1/L/a by positivity)
  calc
    _ = (1/L/a)*(-W*(B*periodCost N v y (Real.log a)+E/b)) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ _ := hh



/-- The complete literal fibre debit, in the radial units used by the
existing positive supply. The cutoff and allocation errors are included. -/
theorem signedPart_fibre_radial {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e| = 1) (A : Finset ℕ)
    {v y L : ℝ} (hv : 500000 ≤ v) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y)
    (hL : (67/100 : ℝ)*v ≤ L) {a : ℕ} (ha : a ∈ cofactors k v)
    (hA : ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : Real.sin (y*v) = 0)
    (hsign : e*Real.cos (y*v) ≤ 0) :
    -(amplitude N v/v)*
      ((200000*responseConstant k/v^2+
          1200*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v^2)*
          (Real.log a.minFac*(a : ℝ)⁻¹)+
        (400*(2 : ℝ)^k/v)*(a : ℝ)⁻¹) ≤
      ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), signedPart e A L y N (p*a) := by
  have hv100 : 100 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hy0 : 0 < y := by linarith
  have hd := cofactor_data ha
  have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero hd.1.ne_zero
  have hL0 : 0 < L := by linarith
  have hπ : Real.pi/y ≤ 1/16 := (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have ha' : v/100 ≤ v-Real.pi/y-Real.log a := by linarith [hd.2.2.2.2.1]
  have hlog : 5000 ≤ v-Real.pi/y-Real.log a := by linarith
  have hlog0 : 0 < v-Real.pi/y-Real.log a := by linarith
  let E := (2 : ℝ)^k+3*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v*Real.log a.minFac
  let B := responseConstant k*Real.log a.minFac
  have hE : 0 ≤ E := by dsimp [E]; positivity [responseConstant_pos k,Real.log_natCast_nonneg a.minFac]
  have hB : 0 ≤ B := mul_nonneg (responseConstant_pos k).le (Real.log_natCast_nonneg _)
  have hW : 0 ≤ amplitude N v := amplitude_nonneg N hv0.le
  have hC : 0 ≤ periodCost N v y (Real.log a) := by unfold periodCost; positivity
  have hpre : 2*amplitude N v/(L*a) ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹ := by
    have hh := div_le_div_of_nonneg_left (show 0 ≤ 2*amplitude N v by positivity)
      (show 0 < v/2 by positivity) (show v/2 ≤ L by linarith)
    have hm := mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr ha0.le)
    convert hm using 1 <;> first | rfl | (simp only [div_eq_mul_inv,mul_inv_rev]; ring)
  have hin : B*periodCost N v y (Real.log a)+E/(v-Real.pi/y-Real.log a) ≤
      B*(50000/v^2)+100*E/v := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (periodCost_le hv100 hNv hy hd.2.2.2.2.1) hB
    · exact (div_le_div_of_nonneg_left hE (by positivity : 0 < v/100) ha').trans_eq (by ring)
  have hpay := mul_le_mul hpre hin (by positivity : 0 ≤ B*periodCost N v y (Real.log a)+E/(v-Real.pi/y-Real.log a))
    (by positivity : 0 ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹)
  have hcosteq : 4*(amplitude N v/v)*(a : ℝ)⁻¹*(B*(50000/v^2)+100*E/v) =
      (amplitude N v/v)*
        ((200000*responseConstant k/v^2+1200*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v^2)*
          (Real.log a.minFac*(a : ℝ)⁻¹)+(400*(2 : ℝ)^k/v)*(a : ℝ)⁻¹) := by
    dsimp [B,E]
    ring
  rw [hcosteq] at hpay
  have hb := signedPart_fibre_floor hk he A hv100 hNv hy hL ha hlog hA hpeak hsign
  change -(2*amplitude N v/(L*a))*(B*periodCost N v y (Real.log a)+E/(v-Real.pi/y-Real.log a)) ≤ _ at hb
  have hh := neg_le_neg hpay
  rw [neg_mul] at hb
  simpa only [neg_mul] using hh.trans hb

/-- Summing the exact cofactor population preserves the signed saving.
At every fixed count the complete allocated debit is at most a constant
times `v^(-1/2)` of one radial supply unit, throughout the linear radial
range. Every arithmetic sign is allowed; clipped prime periods are not included. -/
theorem signedPart_population_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e| = 1) (A S : Finset ℕ)
    {v y L : ℝ} (hv : 500000 ≤ v) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y)
    (hL : (67/100 : ℝ)*v ≤ L) (hS : S ⊆ cofactors k v)
    (hA : ∀ a ∈ S, ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A)
    (hpeak : Real.sin (y*v) = 0)
    (hsign : e*Real.cos (y*v) ≤ 0) :
    -(populationConstant k*v^(-(1/2 : ℝ)))*(amplitude N v/v) ≤
      ∑ a ∈ S, ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
        signedPart e A L y N (p*a) := by
  have hv0 : 0 < v := by linarith
  have hk0 : 0 < k := by omega
  have hC := ZetaRieszCofactorMass.constants_pos hk0
  have hCl := hC.1
  have hB := responseConstant_pos k
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  let F := 200000*responseConstant k/v^2+
    1200*((k : ℝ)+1)*responseConstant k*Real.sqrt (N+1)/v^2
  let G := 400*(2 : ℝ)^k/v
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hrow := Finset.sum_le_sum (fun a (ha : a ∈ S) =>
    signedPart_fibre_radial hk he A hv hNv hy hL (hS ha) (hA a ha) hpeak hsign)
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
  have hsqrt : Real.sqrt (N+1)/v ≤ v^(-(1/2 : ℝ)) := by
    have hh := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (show (N : ℝ)+1 ≤ v by linarith)) hv0.le
    rwa [Real.sqrt_eq_rpow v,hrat] at hh
  have hinv : 1/v ≤ v^(-(1/2 : ℝ)) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ v by linarith)
      (show (-1 : ℝ) ≤ -(1/2 : ℝ) by norm_num)
    simpa only [Real.rpow_neg_one,one_div] using hh
  have hcosteq : F*(ZetaRieszCofactorMass.logMassConstant k*v)+
      G*(ZetaRieszCofactorMass.variationConstant k*v^(1/2 : ℝ)) =
      200000*responseConstant k*ZetaRieszCofactorMass.logMassConstant k*(1/v)+
        1200*((k : ℝ)+1)*responseConstant k*ZetaRieszCofactorMass.logMassConstant k*(Real.sqrt (N+1)/v)+
        400*(2 : ℝ)^k*ZetaRieszCofactorMass.variationConstant k*(v^(1/2 : ℝ)/v) := by
    dsimp [F,G]
    field_simp
  have hpay : F*(ZetaRieszCofactorMass.logMassConstant k*v)+
      G*(ZetaRieszCofactorMass.variationConstant k*v^(1/2 : ℝ)) ≤
      populationConstant k*v^(-(1/2 : ℝ)) := by
    rw [hcosteq,hrat]
    have h₁ := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ 200000*responseConstant k*ZetaRieszCofactorMass.logMassConstant k by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hsqrt
      (show 0 ≤ 1200*((k : ℝ)+1)*responseConstant k*ZetaRieszCofactorMass.logMassConstant k by positivity)
    unfold populationConstant
    nlinarith only [h₁,h₂]
  have hh := mul_le_mul_of_nonpos_left (hmass.trans hpay) (neg_nonpos.mpr hbase)
  calc
    _ = -(amplitude N v/v)*(populationConstant k*v^(-(1/2 : ℝ))) := by ring
    _ ≤ _ := hh.trans hrow

/-- The literal signed population costs arbitrarily little of a radial
supply unit eventually, uniformly in its radial center and selected
cofactors. This does NOT claim source-scale decay or cover clipped periods. -/
theorem eventually_signedPart_population_floor {k : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e| = 1) {y ε : ℝ}
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A S : Finset ℕ) (v L : ℝ),
      (N : ℝ)+2 ≤ v → (67/100 : ℝ)*v ≤ L → S ⊆ cofactors k v →
      (∀ a ∈ S, ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), p ∈ A) →
      Real.sin (y*v) = 0 →
      (e*Real.cos (y*v) ≤ 0) →
      -ε*(Real.exp (-v/2)*v^N/N.factorial) ≤
        ∑ a ∈ S, ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
          signedPart e A L y N (p*a) := by
  have ht : Tendsto (fun v : ℝ => populationConstant k*v^(-(1/2 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 1/2)).const_mul (populationConstant k)
  obtain ⟨v₀,hv₀⟩ := eventually_atTop.mp (ht.eventually_lt_const hε)
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop v₀,
    eventually_ge_atTop (500000 : ℕ)] with N hNv₀ hN A S v L hv hL hS hA hpeak hsign
  have hNR : (500000 : ℝ) ≤ N := by exact_mod_cast hN
  have hvbig : 500000 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hb := signedPart_population_floor hk he A S hvbig hv hy hL hS hA hpeak hsign
  have hs := (hv₀ v (by linarith)).le
  have hnon : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have he : amplitude N v/v = Real.exp (-v/2)*v^N/N.factorial := by
    unfold amplitude
    rw [pow_succ]
    field_simp
  have hh := mul_le_mul_of_nonneg_right (neg_le_neg hs) hnon
  rw [he] at hh hb
  exact hh.trans hb



/-- Real-valued reindexing retains unique largest-prime ownership. -/
theorem sum_owned_real {k : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y)
    (S : Finset ℕ) (hS : S ⊆ cofactors k v) (f : ℕ → ℝ) :
    (∑ n ∈ S.biUnion (fun a =>
      (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p)), f n) =
      ∑ a ∈ S, ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), f (p*a) := by
  have hh := congrArg Complex.re (sum_owned_subset hv hy S hS (fun n => (f n : ℂ)))
  simpa only [Complex.re_sum,Complex.ofReal_re] using hh

/-- The original physical prime mask and moving length are discharged on
the whole linear core. There is no frozen cofactor-sign filter. -/
theorem eventually_core_part_floor {k : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e| = 1)
    {u y ε : ℝ} (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (v : ℝ) (S : Finset ℕ),
      (39/20 : ℝ)*N ≤ v-Real.pi/y → v+Real.pi/y ≤ (203/100 : ℝ)*N →
      S ⊆ cofactors k v → Real.sin (y*v) = 0 → e*Real.cos (y*v) ≤ 0 →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let P := S.biUnion (fun a =>
        (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p));
      -ε*(Real.exp (-v/2)*v^N/N.factorial) ≤ ∑ n ∈ P, signedPart e A L y N n := by
  have hy0 : 0 < y := by linarith
  have hpi : 0 ≤ Real.pi/y := by positivity
  filter_upwards [eventually_signedPart_population_floor hk he hy hε,
    eventually_core_geometry k hu hU hy,eventually_ge_atTop (1000 : ℕ)] with N hN hgeo hlarge v S hv hvu hS hpeak hsign
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hvg := hgeo v (by linarith) (by linarith)
  dsimp only
  rw [sum_owned_real (by linarith : 100 ≤ v) hy S hS]
  exact hN _ _ v _ (by linarith) hvg.1 hS
    (fun a ha p hp => hvg.2 a (hS ha) p hp) hpeak hsign

/-- The arithmetic parts recombine before estimating. The two covers may
overlap: they pay different parts of the same atom, not two copies of it. -/
theorem two_cover_ledger (A S P Q : Finset ℕ) (L y : ℝ) (N : ℕ)
    (hP : P ⊆ S) (hQ : Q ⊆ S) :
    (∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re =
      (∑ n ∈ P, signedPart 1 A L y N n)+(∑ n ∈ Q, signedPart (-1) A L y N n)+
      (∑ n ∈ S\P, signedPart 1 A L y N n)+(∑ n ∈ S\Q, signedPart (-1) A L y N n) := by
  rw [Complex.re_sum]
  simp_rw [← signedPart_add]
  rw [Finset.sum_add_distrib]
  have hp := Finset.sum_sdiff hP (f := signedPart 1 A L y N)
  have hq := Finset.sum_sdiff hQ (f := signedPart (-1) A L y N)
  linarith only [hp,hq]

/-- Complete periods of the two orientations contribute their signed
payments, while every unmatched arithmetic part remains literal. Choosing
`S` as the unpaid set protects credits already used elsewhere. -/
theorem two_cover_floor (A S I J : Finset ℕ) (P Q : ℕ → Finset ℕ)
    (L y : ℝ) (N : ℕ) (d e : ℕ → ℝ)
    (hP : ∀ i ∈ I, P i ⊆ S) (hQ : ∀ i ∈ J, Q i ⊆ S)
    (hPd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (P i) (P j))
    (hQd : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (Q i) (Q j))
    (hpayP : ∀ i ∈ I, -d i ≤ ∑ n ∈ P i, signedPart 1 A L y N n)
    (hpayQ : ∀ i ∈ J, -e i ≤ ∑ n ∈ Q i, signedPart (-1) A L y N n) :
    (∑ n ∈ S\I.biUnion P, signedPart 1 A L y N n)+
      (∑ n ∈ S\J.biUnion Q, signedPart (-1) A L y N n)-
      ((∑ i ∈ I, d i)+(∑ i ∈ J, e i)) ≤
        (∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hp : I.biUnion P ⊆ S := by
    intro n hn
    obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
    exact hP i hi hn
  have hq : J.biUnion Q ⊆ S := by
    intro n hn
    obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
    exact hQ i hi hn
  rw [two_cover_ledger A S _ _ L y N hp hq,
    Finset.sum_biUnion hPd,Finset.sum_biUnion hQd]
  have h₁ := Finset.sum_le_sum hpayP
  have h₂ := Finset.sum_le_sum hpayQ
  simp only [Finset.sum_neg_distrib] at h₁ h₂
  linarith only [h₁,h₂]


/-- The ordinary half-open prime periods retain their total-log support. -/
theorem owned_log_support {k : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y)
    (S : Finset ℕ) (hS : S ⊆ cofactors k v) {n : ℕ}
    (hn : n ∈ S.biUnion (fun a =>
      (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p))) :
    v-Real.pi/y < Real.log n ∧ Real.log n ≤ v+Real.pi/y := by
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hyabs : |y| = y := abs_of_pos (by linarith)
  have hy' : 54 ≤ |y| := by rwa [hyabs]
  have hg := fibre_geometry hv hy' (hS ha) (by simpa only [hyabs] using hp)
  rw [hyabs] at hg
  simpa only [Nat.mul_comm a p] using ⟨hg.2.2.2.2.1,hg.2.2.2.2.2.1⟩

/-- Ordered nonoverlapping period interiors cannot reuse an integer. -/
theorem owned_disjoint_of_separated {k : ℕ} {v w y : ℝ}
    (hv : 100 ≤ v) (hw : 100 ≤ w) (hy : 54 ≤ y)
    (S T : Finset ℕ) (hS : S ⊆ cofactors k v) (hT : T ⊆ cofactors k w)
    (hgap : v+Real.pi/y ≤ w-Real.pi/y) :
    Disjoint (S.biUnion (fun a =>
      (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p)))
      (T.biUnion (fun a =>
        (logPrimes (w-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p))) := by
  apply Finset.disjoint_left.mpr
  intro n hn hm
  have h₁ := owned_log_support hv hy S hS hn
  have h₂ := owned_log_support hw hy T hT hm
  linarith only [h₁.2,h₂.1,hgap]

open ZetaRieszMultiPeriodSix (center)

/-- The two arithmetic orientations have exact staggered period peaks. -/
theorem staggered_peaks {v y : ℝ} (hy : 0 < y)
    (hv : Real.cos (y*v) = -1) (i : ℕ) :
    (Real.sin (y*center v y i) = 0 ∧ Real.cos (y*center v y i) = -1) ∧
    (Real.sin (y*center (v+Real.pi/y) y i) = 0 ∧
      Real.cos (y*center (v+Real.pi/y) y i) = 1) := by
  have h₁ : Real.cos (y*center v y i) = -1 :=
    (ZetaRieszMultiPeriodSix.center_phase hy.ne' i).trans hv
  have hb : Real.cos (y*(v+Real.pi/y)) = 1 := by
    rw [show y*(v+Real.pi/y) = y*v+Real.pi by field_simp,
      Real.cos_add_pi,hv]
    norm_num
  have h₂ : Real.cos (y*center (v+Real.pi/y) y i) = 1 :=
    (ZetaRieszMultiPeriodSix.center_phase hy.ne' i).trans hb
  exact ⟨⟨Real.sin_eq_zero_iff_cos_eq.mpr (Or.inr h₁),h₁⟩,
    ⟨Real.sin_eq_zero_iff_cos_eq.mpr (Or.inl h₂),h₂⟩⟩

/-- A growing finite collection of complete periods has one total signed
cost. No relation between the two grids' label sets is needed: opposite
arithmetic parts are exactly recombined, and the two unmatched parts remain.
This is an inequality on the original real carrier, not a completed model. -/
theorem eventually_staggered_floor {k : ℕ} (hk : 2 ≤ k) {u y ε : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (S I J : Finset ℕ) (v : ℝ) (C D : ℕ → Finset ℕ),
      Real.cos (y*v) = -1 →
      (∀ i ∈ I, (39/20 : ℝ)*N ≤ center v y i-Real.pi/y ∧
        center v y i+Real.pi/y ≤ (203/100 : ℝ)*N) →
      (∀ i ∈ J, (39/20 : ℝ)*N ≤ center (v+Real.pi/y) y i-Real.pi/y ∧
        center (v+Real.pi/y) y i+Real.pi/y ≤ (203/100 : ℝ)*N) →
      (∀ i ∈ I, C i ⊆ cofactors k (center v y i)) →
      (∀ i ∈ J, D i ⊆ cofactors k (center (v+Real.pi/y) y i)) →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let P := fun i => (C i).biUnion (fun a =>
        (logPrimes (center v y i-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p))
      let Q := fun i => (D i).biUnion (fun a =>
        (logPrimes (center (v+Real.pi/y) y i-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p));
      (∀ i ∈ I, P i ⊆ S) → (∀ i ∈ J, Q i ⊆ S) →
      (∑ n ∈ S\I.biUnion P, signedPart 1 A L y N n)+
        (∑ n ∈ S\J.biUnion Q, signedPart (-1) A L y N n)-
        ε*((∑ i ∈ I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
          (∑ i ∈ J, Real.exp (-center (v+Real.pi/y) y i/2)*
            (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
        (∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hy0 : 0 < y := by linarith
  have hyabs : |y| = y := abs_of_pos hy0
  have hpi : 0 ≤ Real.pi/y := by positivity
  have hstep : 0 ≤ 2*Real.pi/y := by positivity
  have hsep (b : ℝ) {i j : ℕ} (hij : i < j) :
      center b y i+Real.pi/y ≤ center b y j-Real.pi/y := by
    have hh : (i : ℝ)+1 ≤ j := by exact_mod_cast hij
    have hm := mul_le_mul_of_nonneg_right hh hstep
    dsimp only [center]
    rw [hyabs]
    ring_nf at hm ⊢
    linarith only [hm]
  filter_upwards [eventually_core_part_floor hk (e := 1) (by norm_num) hu hU hy hε,
    eventually_core_part_floor hk (e := -1) (by norm_num) hu hU hy hε,
    eventually_ge_atTop (1000 : ℕ)] with N hpos hneg hlarge S I J v C D hpeak hI hJ hC hD
  dsimp only
  intro hP hQ
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hvI i (hi : i ∈ I) : 100 ≤ center v y i := by linarith [(hI i hi).1]
  have hvJ i (hi : i ∈ J) : 100 ≤ center (v+Real.pi/y) y i := by linarith [(hJ i hi).1]
  have hpaid := two_cover_floor _ S I J _ _ _ y N
    (fun i => ε*(Real.exp (-center v y i/2)*(center v y i)^N/N.factorial))
    (fun i => ε*(Real.exp (-center (v+Real.pi/y) y i/2)*
      (center (v+Real.pi/y) y i)^N/N.factorial)) hP hQ
    (by
      intro i hi j hj hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact owned_disjoint_of_separated (hvI i hi) (hvI j hj) hy _ _ (hC i hi) (hC j hj) (hsep v h)
      · exact (owned_disjoint_of_separated (hvI j hj) (hvI i hi) hy _ _ (hC j hj) (hC i hi) (hsep v h)).symm)
    (by
      intro i hi j hj hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact owned_disjoint_of_separated (hvJ i hi) (hvJ j hj) hy _ _ (hD i hi) (hD j hj) (hsep _ h)
      · exact (owned_disjoint_of_separated (hvJ j hj) (hvJ i hi) hy _ _ (hD j hj) (hD i hi) (hsep _ h)).symm)
    (by
      intro i hi
      have hp := (staggered_peaks hy0 hpeak i).1
      simpa only [neg_mul] using hpos _ (C i) (hI i hi).1 (hI i hi).2 (hC i hi) hp.1
        (by rw [hp.2]; norm_num))
    (by
      intro i hi
      have hp := (staggered_peaks hy0 hpeak i).2
      simpa only [neg_mul] using hneg _ (D i) (hJ i hi).1 (hJ i hi).2 (hD i hi) hp.1
        (by rw [hp.2]; norm_num))
  simpa only [← Finset.mul_sum,← mul_add] using hpaid


/-- Through total count 55, an interior owner label belongs to every
complete period containing its logarithm provided its owner is separated
by 1/8 and its cofactor has the stated lower-share margin. There is no
coefficient-sign condition and no new upper cofactor-share restriction. -/
theorem mem_population_of_owner_margin {k a p : ℕ} (hk : k ≤ 54)
    {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y) (ha : Squarefree a)
    (hc : a.primeFactors.card = k) (hp : p.Prime)
    (hT : v-Real.pi/y < Real.log (p*a : ℕ) ∧ Real.log (p*a : ℕ) ≤ v+Real.pi/y)
    (hshare : (203/500 : ℝ)*(Real.log (p*a : ℕ)+1/16) < Real.log a)
    (hgap : ∀ q ∈ a.primeFactors, Real.log q ≤ Real.log p-1/8) :
    p*a ∈ ZetaRieszFixedCountPeriod.population k v y := by
  have hy0 : 0 < y := by linarith
  have hyabs : |y| = y := abs_of_pos hy0
  have hπ : Real.pi/y ≤ 1/16 := (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha.ne_zero)]
  have ham : a ∈ cofactors k v := (mem_cofactors_iff_of_count_le hk (by linarith)).mpr
    ⟨ha,hc,by linarith [hT.1],by
      intro q hq
      have hg := hgap q hq
      rw [hlog] at hT
      linarith [hT.2]⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨a,ham,Finset.mem_image.mpr ⟨p,?_,Nat.mul_comm a p⟩⟩
  rw [hyabs,ZetaRieszMacroPrimeWindows.mem_logPrimes_iff]
  rw [hlog] at hT
  refine ⟨hp,by linarith [hT.1],?_⟩
  rw [show v-Real.pi/y-Real.log a+2*Real.pi/y = v+Real.pi/y-Real.log a by ring]
  linarith [hT.2]

/-- Inside a complete period, the low-count geometric omissions have two
explicit causes: the lower cofactor-share edge or two largest primes with
logarithms less than 1/8 apart. Sign changes are not an omission. -/
theorem missing_population_boundary {k a p : ℕ} (hk : k ≤ 54)
    {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y) (ha : Squarefree a)
    (hc : a.primeFactors.card = k) (hp : p.Prime)
    (hT : v-Real.pi/y < Real.log (p*a : ℕ) ∧ Real.log (p*a : ℕ) ≤ v+Real.pi/y)
    (hmiss : p*a ∉ ZetaRieszFixedCountPeriod.population k v y) :
    Real.log a ≤ (203/500 : ℝ)*(Real.log (p*a : ℕ)+1/16) ∨
      ∃ q ∈ a.primeFactors, Real.log p-1/8 < Real.log q := by
  by_contra h
  push Not at h
  exact hmiss (mem_population_of_owner_margin hk hv hy ha hc hp hT h.1 h.2)


/-- The two signed covers bound the current endgame carrier itself.
Only its previously paid geometric core/joined error is used. The two
unmatched sign parts remain explicit; this is not the numerical -79/1000
floor until those parts and the accumulated period cost are controlled. -/
theorem joined_two_cover_floor {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (N K : ℕ)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N)
    (I J : Finset ℕ) (P Q : ℕ → Finset ℕ) (d e : ℕ → ℝ) :
    let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let S := ZetaRieszParityPacket.coreBand u N K;
    (∀ i ∈ I, P i ⊆ S) → (∀ i ∈ J, Q i ⊆ S) →
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (P i) (P j)) →
    (∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (Q i) (Q j)) →
    (∀ i ∈ I, -d i ≤ ∑ n ∈ P i, signedPart 1 A L y N n) →
    (∀ i ∈ J, -e i ≤ ∑ n ∈ Q i, signedPart (-1) A L y N n) →
    u^(N+1)*((∑ n ∈ S\I.biUnion P, signedPart 1 A L y N n)+
      (∑ n ∈ S\J.biUnion Q, signedPart (-1) A L y N n)-
        ((∑ i ∈ I, d i)+(∑ i ∈ J, e i)))-
      2*(19/20 : ℝ)^N*zetaMoebiusLogMajorantMass (1+1/256) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  dsimp only
  intro hP hQ hPd hQd hpayP hpayQ
  have hf := two_cover_floor _ _ I J P Q _ y N d e hP hQ hPd hQd hpayP hpayQ
  have hs := mul_le_mul_of_nonneg_left hf (pow_nonneg hu (N+1))
  have hb := (Complex.re_le_norm ((u : ℂ)^(N+1)*
    (ZetaRieszParityPacket.coreResponse u y N K-ZetaRieszGammaJoint.joinedPhysical u y N K))).trans
      (ZetaRieszGammaJoint.core_joined_bound hu hU N K y hL)
  rw [mul_sub,Complex.sub_re] at hb
  have hc : ((u : ℂ)^(N+1)*ZetaRieszParityPacket.coreResponse u y N K).re =
      u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re := by
    rw [← Complex.ofReal_pow,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hc] at hb
  change _ ≤ u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re at hs
  linarith only [hs,hb]

end RiemannGaussian.ZetaRieszStaggeredFloor

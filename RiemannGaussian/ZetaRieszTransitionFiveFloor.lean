/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRoughFiveJoinedFloor

set_option autoImplicit false

/-!
# A signed period floor through the unpaid cofactor-share transition

The literal largest-prime period estimate extends below 0.406 to 0.398,
which overlaps the already-paid dominant-allocation region ending at 0.399.
The slightly larger owner share still lies inside every original core mask.
The exact two hinges, coefficient, unassigned allocation and prime phase
remain coupled. The same count-dependent radial cost, and therefore the
same global positive supply selection, pay the enlarged rough five-prime
cover; no extra credit is assumed.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszTransitionFiveFloor
open ZetaRieszFixedCountPeriod ZetaRieszSignedPeriodFloor ZetaRieszStaggeredFloor
open ZetaRieszQuantitativePrimePeriod ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaRieszMultiPeriodSix
open ZetaRieszRoughFivePeriodFloor ZetaRieszRoughFiveJoinedFloor
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszSmallPrimeCompensation ZetaRieszFourPrimeHead
open ZetaRieszFivePositiveHead ZetaRieszFiveNegativeHead
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime
open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket ZetaRieszJointAllocation
open ZetaRieszOneSidedArithmetic (weight weight_nonneg)
open ZetaRieszSevenCountTail

/-- The physical cofactor selector with its lower share extended to 199/500.
This is a literal support enlargement, not a replacement carrier. -/
def cofactors (k : ℕ) (v : ℝ) : Finset ℕ :=
  (ZetaRieszCofactorMass.products k v).filter (fun a =>
    Squarefree a ∧ a.primeFactors.card = k ∧ (199/500 : ℝ)*v < Real.log a ∧
    Real.log a ≤ (197/200 : ℝ)*v ∧
    ∀ p ∈ a.primeFactors, Real.log p ≤ v-1/16-Real.log a)

theorem cofactor_data {k : ℕ} {v : ℝ} {a : ℕ} (ha : a ∈ cofactors k v) :
    Squarefree a ∧ a.primeFactors.card = k ∧ Real.log a.minFac ≤ v ∧
      (199/500 : ℝ)*v < Real.log a ∧ Real.log a ≤ (197/200 : ℝ)*v ∧
      (∀ p ∈ a.primeFactors, Real.log p ≤ v-1/16-Real.log a) := by
  obtain ⟨_,hs,hc,hl,hu,hm⟩ := Finset.mem_filter.mp ha
  have hv : 0 ≤ v := by nlinarith [Real.log_natCast_nonneg a]
  have hmin : Real.log a.minFac ≤ Real.log a := Real.log_le_log
    (by exact_mod_cast Nat.minFac_pos a) (by exact_mod_cast Nat.minFac_le (Nat.pos_of_ne_zero hs.ne_zero))
  exact ⟨hs,hc,by linarith,hl,hu,hm⟩

/-- The enlarged selector contains every original complete-period cofactor.
The preceding estimates remain available with their original definitions. -/
theorem original_cofactors_subset {k : ℕ} {v : ℝ} (_hv : 0 ≤ v) :
    ZetaRieszFixedCountPeriod.cofactors k v ⊆ cofactors k v := by
  intro a ha
  obtain ⟨hb,hs,hc,hl,hu,ho⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨hb,hs,hc,by linarith,hu,ho⟩

/-- Through count fifty-four the same owner inequality gives the original
upper cap. The enlarged lower endpoint adds no extra condition. -/
theorem mem_cofactors_iff_of_count_le {k a : ℕ} (hk : k ≤ 54) {v : ℝ} (hv : 0 ≤ v) :
    a ∈ cofactors k v ↔ Squarefree a ∧ a.primeFactors.card = k ∧
      (199/500 : ℝ)*v < Real.log a ∧
      (∀ p ∈ a.primeFactors, Real.log p ≤ v-1/16-Real.log a) := by
  constructor
  · intro ha
    have hd := cofactor_data ha
    exact ⟨hd.1,hd.2.1,hd.2.2.2.1,hd.2.2.2.2.2⟩
  · rintro ⟨hs,hc,hl,ho⟩
    have hcap := ZetaRieszFixedCountPeriod.cofactor_cap_of_owner hv hs hc hk ho
    apply Finset.mem_filter.mpr
    refine ⟨ZetaRieszCofactorMass.mem_products_of_squarefree hs hc ?_,hs,hc,hl,by linarith,ho⟩
    intro p hp
    linarith [ho p hp,Real.log_natCast_nonneg a]

theorem fibre_geometry {k : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ |y|)
    {a p : ℕ} (ha : a ∈ cofactors k v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) :
    p.Prime ∧ (∀ q ∈ a.primeFactors, q < p) ∧ Squarefree (p*a) ∧
      (p*a).primeFactors.card = k+1 ∧
      v-Real.pi/|y| < Real.log (p*a : ℕ) ∧ Real.log (p*a : ℕ) ≤ v+Real.pi/|y| ∧
      (∀ q ∈ (p*a).primeFactors, Real.log q ≤ (1209/2000 : ℝ)*Real.log (p*a : ℕ)) := by
  obtain ⟨hs,hc,hr,hal,hau,ham⟩ := cofactor_data ha
  have hb := logPrimes_bounds hp
  have hπ : 0 < Real.pi/|y| := div_pos Real.pi_pos (by linarith)
  have hπu : Real.pi/|y| ≤ 1/16 :=
    (div_le_iff₀ (by linarith : 0 < |y|)).mpr (by nlinarith [Real.pi_lt_d4])
  have hl : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hb.1.ne_zero) (by exact_mod_cast hs.ne_zero)]
  have hbu := hb.2.2
  rw [mul_div_assoc] at hbu
  have howner (q : ℕ) (hq : q ∈ a.primeFactors) : q < p := by
    exact_mod_cast (Real.log_lt_log_iff
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos : (0 : ℝ) < q)
      (by exact_mod_cast hb.1.pos : (0 : ℝ) < p)).mp (by linarith [ham q hq,hb.2.1])
  have hpd : ¬p ∣ a := by
    intro hd
    exact (howner p (hb.1.mem_primeFactors hd hs.ne_zero)).false
  have hsf := Nat.squarefree_mul_iff.mpr ⟨hb.1.coprime_iff_not_dvd.mpr hpd,hb.1.squarefree,hs⟩
  have hpf : (p*a).primeFactors = insert p a.primeFactors := by
    rw [Nat.primeFactors_mul hb.1.ne_zero hs.ne_zero,hb.1.primeFactors,Finset.singleton_union]
  have hpm : p ∉ a.primeFactors := fun h => hpd (Nat.dvd_of_mem_primeFactors h)
  have hpmax : Real.log p ≤ (1209/2000 : ℝ)*Real.log (p*a : ℕ) := by
    rw [hl]; linarith
  refine ⟨hb.1,howner,hsf,by rw [hpf,Finset.card_insert_of_notMem hpm,hc],
    by rw [hl]; linarith [hb.2.1],by rw [hl]; linarith,?_⟩
  intro q hq
  rw [hpf] at hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact hpmax
  · exact (Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
      (by exact_mod_cast (howner q hq).le)).trans hpmax

theorem coefficient_eq_response {k : ℕ} (hk : 2 ≤ k) {v y L : ℝ}
    (hv : 100 ≤ v) (hy : 54 ≤ |y|) (_hLl : (67/100 : ℝ)*v ≤ L)
    {a p : ℕ} (ha : a ∈ cofactors k v)
    (hp : p ∈ logPrimes (v-Real.pi/|y|-Real.log a) (2*Real.pi/|y|)) :
    SquarefreeVaughanLogSource.coefficient L (p*a) =
      (((-1 : ℝ)^(k+1)*(-(Real.log (p*a : ℕ)/L)*
        response L (Real.log (p*a : ℕ)) a) : ℝ) : ℂ) := by
  obtain ⟨hpp,howner,hs,hc,_,_,_⟩ := fibre_geometry hv hy ha hp
  have hd := cofactor_data ha
  have hpd : ¬p ∣ a := by
    intro h
    exact (howner p (hpp.mem_primeFactors h hd.1.ne_zero)).false
  have hn1 : p*a ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬(p*a).Prime := by intro h; simp [h.primeFactors] at hc; omega
  have hl : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast hd.1.ne_zero)]
  have href := VaughanLogAverage.riesz_reflection (Real.log (p*a : ℕ)-L) hs hn1 hnp
  rw [sub_sub_cancel,ZetaRieszReflectedLinear.moebius_eq_primeCount hs,hc,
    Int.cast_pow,Int.cast_neg,Int.cast_one,
    riesz_prime_mul (Real.log (p*a : ℕ)-L) hpp hpd] at href
  rw [show Real.log (p*a : ℕ)-L-Real.log p = Real.log a-L by rw [hl]; ring] at href
  rw [SquarefreeVaughanLogSource.coefficient,if_pos ⟨hs,hnp⟩,href]
  congr 1
  dsimp only [response]
  ring

private theorem cofactor_kernel_bound {k : ℕ} (hk : 2 ≤ k) {v : ℝ} {a : ℕ}
    (ha : a ∈ cofactors k v) (D : ℝ) :
    |VaughanLogAverage.riesz D a| ≤
      (1+ZetaRieszSignedSperner.parityCapacity (k-2) 0+
        ZetaRieszSignedSperner.parityCapacity (k-2) 1)*Real.log a.minFac := by
  have hd := cofactor_data ha
  have hh := ZetaRieszSignedSperner.riesz_bounds_minFac D hd.1 (by omega)
  rw [hd.2.1] at hh
  have h0 : (0 : ℝ) ≤ ZetaRieszSignedSperner.parityCapacity (k-2) 0 := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ ZetaRieszSignedSperner.parityCapacity (k-2) 1 := Nat.cast_nonneg _
  have hr := Real.log_natCast_nonneg a.minFac
  apply abs_le.mpr
  constructor <;> nlinarith only [hh.1,hh.2,hr,mul_nonneg h0 hr,mul_nonneg h1 hr]

/-- Both retained cutoffs cost at most twice the same least-prime bound.
No saturation or coefficient-sign assumption is used. -/
theorem cofactor_response_bound {k : ℕ} (hk : 2 ≤ k) {v : ℝ} {a : ℕ}
    (ha : a ∈ cofactors k v) (L T : ℝ) :
    |response L T a| ≤ responseConstant k*Real.log a.minFac := by
  have ht : |VaughanLogAverage.riesz (T-L) a-VaughanLogAverage.riesz (Real.log a-L) a| ≤
      |VaughanLogAverage.riesz (T-L) a|+|VaughanLogAverage.riesz (Real.log a-L) a| := by
    simpa only [sub_eq_add_neg,abs_neg] using
      abs_add_le (VaughanLogAverage.riesz (T-L) a) (-VaughanLogAverage.riesz (Real.log a-L) a)
  have h := ht.trans (add_le_add (cofactor_kernel_bound hk ha (T-L))
      (cofactor_kernel_bound hk ha (Real.log a-L)))
  convert h using 1 <;> first | rfl | (dsimp only [responseConstant]; ring)

/-- The unsaturated correction is constant on the prime fibre, so it adds
no cutoff-variation cost at all. -/
theorem cofactor_response_variation {k : ℕ} (hk : 2 ≤ k) {v : ℝ} {a : ℕ}
    (ha : a ∈ cofactors k v) (L D E : ℝ) :
    |response L D a-response L E a| ≤ (2 : ℝ)^k*|D-E| := by
  have hd := cofactor_data ha
  have hh := ZetaRieszTentSlope.riesz_cutoff_lipschitz_quarter (D-L) (E-L) hd.1 (by omega)
  rw [ZetaRieszTentSlope.absolute_divisor_mass_eq_card hd.1,
    ZetaRieszSmoothHead.card_divisors_of_squarefree hd.1,hd.2.1,Nat.cast_pow,Nat.cast_ofNat] at hh
  simp only [sub_sub_sub_cancel_right] at hh
  simp only [response,sub_sub_sub_cancel_right]
  nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ)^k by positivity) (abs_nonneg (D-E))]

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

theorem eventually_core_geometry (k : ℕ) {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ,
      (39/20 : ℝ)*N ≤ v → v ≤ (203/100 : ℝ)*N →
      (67/100 : ℝ)*v ≤ SquarefreeVaughanLogSource.length u N ∧
      ∀ a ∈ cofactors k v, ∀ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y),
        p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N := by
  have hy0 : 0 < y := by linarith
  have hyabs : |y| = y := abs_of_pos hy0
  have hy' : 54 ≤ |y| := by rwa [hyabs]
  have hroom : u < Real.exp (-(137/200 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans (Real.exp_lt_exp.mpr (by norm_num)))
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)/(N : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,pow_one,one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hl.eventually_lt_const (by norm_num : (0 : ℝ) < 1/100),
    ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
      (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200) hroom,
    eventually_ge_atTop (1000 : ℕ)] with N hlog hL hN v hv hvu
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  refine ⟨by linarith,?_⟩
  intro a ha p hp
  have hgeo := fibre_geometry (by linarith : 100 ≤ v) hy' ha (by simpa only [hyabs] using hp)
  have hd := (cofactor_data ha).2.2.2.2.1
  have hpb := logPrimes_bounds hp
  have hpi : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  apply (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mpr
  refine ⟨hgeo.1,?_,?_⟩
  · have hlg : 2*Real.log (N : ℝ) < (N : ℝ)/50 := by
      have hh := (div_lt_iff₀ hN0).mp hlog
      linarith only [hh]
    have hh : Real.log ((N^2 : ℕ) : ℝ) < Real.log p := by
      rw [Nat.cast_pow,Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [hpb.2.1,hd]
    exact_mod_cast (Real.log_lt_log_iff (by positivity : (0 : ℝ) < (N^2 : ℕ))
      (by exact_mod_cast hgeo.1.pos)).mp hh
  · have hpp : p ∈ (p*a).primeFactors := hgeo.1.mem_primeFactors (dvd_mul_right p a) hgeo.2.2.1.ne_zero
    have hm := hgeo.2.2.2.2.2.2 p hpp
    have htop : Real.log p < SquarefreeVaughanLogSource.length u N := by
      have hrad := hgeo.2.2.2.2.2.1
      rw [hyabs] at hrad
      nlinarith
    have he : Real.log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ) =
        SquarefreeVaughanLogSource.length u N := by
      simp only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hgeo.1.pos) (by positivity)).mp (he ▸ htop)

/-- Unique largest-prime ownership makes the cofactor estimate a bound for
a literal set of integer labels. No incidence multiplicity is added. -/
theorem sum_owned_subset {k : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y)
    (S : Finset ℕ) (hS : S ⊆ cofactors k v) (f : ℕ → ℂ) :
    (∑ n ∈ S.biUnion (fun a =>
      (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p)), f n) =
      ∑ a ∈ S, ∑ p ∈ logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y), f (p*a) := by
  have hyabs : |y| = y := abs_of_pos (by linarith)
  have hy' : 54 ≤ |y| := by rwa [hyabs]
  rw [ZetaRieszCoupledWindow.sum_owned_products _ _ f
    (fun a ha => (cofactor_data (hS ha)).1.ne_zero) (by
      intro a ha p hp
      have hg := fibre_geometry hv hy' (hS ha) (by simpa only [hyabs] using hp)
      exact ⟨hg.1,fun q hq hd => hg.2.1 q
        (hq.mem_primeFactors hd (cofactor_data (hS ha)).1.ne_zero)⟩)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.mul_comm]

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

theorem mem_core_of_prime_share_le (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (5/4 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    {n : ℕ} (hs : Squarefree n) (hc : 3 ≤ n.primeFactors.card)
    (hK : n.primeFactors.card < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
    (hlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j < Real.log n)
    (hhi : Real.log n ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ (1209/2000 : ℝ)*Real.log n) :
    n ∈ ZetaRieszParityPacket.coreBand u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
      (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  have hN : (0 : ℝ) < N := by
    dsimp [N,ZetaRieszPrimeCountFrequency.dyadicMomentOrder,
      ZetaRieszPrimeCountFrequency.dyadicPrimeCount]
    positivity
  have ht : 0 < Real.log n := by change (39/20 : ℝ)*N < _ at hlo; linarith
  have hW : n ∈ ZetaRieszJointAllocation.literalWindow N := (ZetaRieszJointAllocation.mem_literalWindow N n).mpr
    (by constructor <;> dsimp [N] at * <;> nlinarith)
  have hpX : ∀ p ∈ n.primeFactors,
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 := by
    intro p hp
    have hplog : Real.log p < SquarefreeVaughanLogSource.length u N := by
      have hm := hmax p hp
      change Real.log n ≤ (203/100 : ℝ)*N at hhi
      change (5/4 : ℝ)*N ≤ _ at hL
      nlinarith
    have he : Real.log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 : ℕ) : ℝ) =
        SquarefreeVaughanLogSource.length u N := by
      simp only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      (by positivity)).mp (he ▸ hplog)
  have hm := ZetaRieszMaskSupport.window_mem_originalMask j hj hu
    (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le) hL hW hs hc hK hpX
  have hdom (p : ℕ) (hp : p ∈ n.primeFactors) :
      Real.log p < (13/20 : ℝ)*Real.log n := by linarith [hmax p hp]
  have hcancel : n ∉ ZetaRieszJointAllocation.cancellingSector u N K := by
    intro hh
    obtain ⟨_,_,_,_,_,p,hp,_,_,_,hshare⟩ := Finset.mem_filter.mp hh
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd : Real.log (n/p : ℕ) = Real.log n-Real.log p := by
      rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp) (by exact_mod_cast hpp.ne_zero),
        Real.log_div (by exact_mod_cast hs.ne_zero) (by exact_mod_cast hpp.ne_zero)]
    have hh := (div_le_iff₀ ht).mp hshare
    rw [hd] at hh
    nlinarith [hdom p hp]
  have hret : n ∈ ZetaRieszMaskSupport.retainedBand u N K :=
    Finset.mem_sdiff.mpr ⟨hm,hcancel⟩
  have hnd : n ∈ ZetaRieszDominantAllocation.nondominantBand u N K := by
    refine Finset.mem_sdiff.mpr ⟨hret,?_⟩
    intro hd
    obtain ⟨_,_,_,_,p,hp,_,_,hl⟩ := Finset.mem_filter.mp hd
    exact (hdom p hp).not_ge hl
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨hnd,by constructor <;> dsimp [N] at * <;> nlinarith⟩,hlo,hhi⟩

/-- Every selected physical label satisfies the original core masks;
only the numerical owner cap differs from the earlier period selector. -/
theorem owned_subset_core {k : ℕ} (hk : 2 ≤ k) (j : ℕ) (hj : 32 ≤ j)
    (hcount : k+1 < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) {u v y : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hv : 100 ≤ v)
    (hL : (5/4 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
    (hlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ v-Real.pi/y)
    (hhi : v+Real.pi/y ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
    (S : Finset ℕ) (hS : S ⊆ cofactors k v) :
    S.biUnion (fun a => (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p)) ⊆
      ZetaRieszParityPacket.coreBand u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
        (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) := by
  have hyabs : |y| = y := abs_of_pos (by linarith)
  have hy' : 54 ≤ |y| := by rwa [hyabs]
  intro n hn
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hg := fibre_geometry hv hy' (hS ha) (by simpa only [hyabs] using hp)
  have htl : v-Real.pi/y < Real.log (p*a : ℕ) := by
    simpa only [hyabs] using hg.2.2.2.2.1
  have htu : Real.log (p*a : ℕ) ≤ v+Real.pi/y := by
    simpa only [hyabs] using hg.2.2.2.2.2.1
  rw [Nat.mul_comm a p]
  apply mem_core_of_prime_share_le j hj hu hU hL hg.2.2.1
    (by omega) (by simpa only [hg.2.2.2.1] using hcount)
    (hlo.trans_lt htl) (htu.trans hhi) hg.2.2.2.2.2.2

/-- The enlarged four-prime cofactor cover with its literal roughness mask. -/
def roughCofactors (B : ℕ) (v : ℝ) : Finset ℕ :=
  (cofactors 4 v).filter (fun a => ∀ r ∈ a.primeFactors, B < r)

/-- Complete ordinary-prime periods with the original cofactor geometry. -/
def roughPeriod (B : ℕ) (v y : ℝ) : Finset ℕ :=
  (roughCofactors B v).biUnion (fun a =>
    (logPrimes (v-Real.pi/y-Real.log a) (2*Real.pi/y)).image (fun p => a*p))

/-- Every previously paid rough period is included in this enlarged cover.
The period is still summed only once, using unique largest-prime ownership. -/
theorem original_roughPeriod_subset (B : ℕ) {v y : ℝ} (hv : 0 ≤ v) :
    ZetaRieszRoughFivePeriodFloor.roughPeriod B v y ⊆ roughPeriod B v y := by
  intro n hn
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨ha,hrough⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_biUnion.mpr ⟨a,
    Finset.mem_filter.mpr ⟨original_cofactors_subset hv ha,hrough⟩,hn⟩

/-- Every sufficiently separated owner beyond the paid dominant cutoff
belongs to the enlarged complete fibre, with no upper cofactor-share
restriction. The running prime and roughness masks remain literal. -/
theorem owner_gap_mem_roughPeriod {B a p : ℕ} {v y : ℝ}
    (hv : 100 ≤ v) (hy : 54 ≤ y) (ha : Squarefree a)
    (hc : a.primeFactors.card = 4) (hp : p.Prime)
    (hT : v-Real.pi/y < Real.log (p*a : ℕ) ∧
      Real.log (p*a : ℕ) ≤ v+Real.pi/y)
    (hlo : (399/1000 : ℝ)*Real.log (p*a : ℕ) ≤ Real.log a)
    (hgap : ∀ q ∈ a.primeFactors, Real.log q ≤ Real.log p-1/8)
    (hrough : ∀ q ∈ a.primeFactors, B < q) :
    p*a ∈ roughPeriod B v y := by
  have hy0 : 0 < y := by linarith
  have hpi : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast ha.ne_zero)]
  have hla : (199/500 : ℝ)*v < Real.log a := by
    linarith only [hv,hpi,hT.1,hlo]
  have ho (q : ℕ) (hq : q ∈ a.primeFactors) :
      Real.log q ≤ v-1/16-Real.log a := by
    have hg := hgap q hq
    rw [hlog] at hT
    linarith only [hg,hpi,hT.2]
  have ham : a ∈ cofactors 4 v :=
    (mem_cofactors_iff_of_count_le (by norm_num) (by linarith)).mpr ⟨ha,hc,hla,ho⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨a,Finset.mem_filter.mpr ⟨ham,hrough⟩,
    Finset.mem_image.mpr ⟨p,?_,Nat.mul_comm a p⟩⟩
  apply (ZetaRieszMacroPrimeWindows.mem_logPrimes_iff _ _ _).mpr
  rw [hlog] at hT
  refine ⟨hp,by linarith only [hT.1],?_⟩
  rw [show v-Real.pi/y-Real.log a+2*Real.pi/y = v+Real.pi/y-Real.log a by ring]
  linarith only [hT.2]

/-- The entire rough five-prime share transition belongs to every complete
period containing its total logarithm. At these shares the owner margin is
automatic, so no close-owner or coefficient-sign assumption is required. -/
theorem transition_mem_roughPeriod {B a p : ℕ} {v y : ℝ}
    (hv : 100 ≤ v) (hy : 54 ≤ y) (ha : Squarefree a)
    (hc : a.primeFactors.card = 4) (hp : p.Prime)
    (hT : v-Real.pi/y < Real.log (p*a : ℕ) ∧
      Real.log (p*a : ℕ) ≤ v+Real.pi/y)
    (hlo : (399/1000 : ℝ)*Real.log (p*a : ℕ) ≤ Real.log a)
    (hhi : Real.log a ≤ (407/1000 : ℝ)*Real.log (p*a : ℕ))
    (hrough : ∀ q ∈ a.primeFactors, B < q) :
    p*a ∈ roughPeriod B v y := by
  have hy0 : 0 < y := by linarith
  have hpi : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hlog : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast ha.ne_zero)]
  have hla : (199/500 : ℝ)*v < Real.log a := by linarith only [hv,hpi,hT.1,hlo]
  have ho (q : ℕ) (hq : q ∈ a.primeFactors) :
      Real.log q ≤ v-1/16-Real.log a := by
    have hqlog : Real.log q ≤ Real.log a := Real.log_le_log
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos)
      (by exact_mod_cast (Nat.le_of_dvd (Nat.pos_of_ne_zero ha.ne_zero)
        (Nat.dvd_of_mem_primeFactors hq)))
    linarith only [hqlog,hv,hpi,hT.2,hhi]
  have ham : a ∈ cofactors 4 v :=
    (mem_cofactors_iff_of_count_le (by norm_num) (by linarith)).mpr ⟨ha,hc,hla,ho⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨a,Finset.mem_filter.mpr ⟨ham,hrough⟩,
    Finset.mem_image.mpr ⟨p,?_,Nat.mul_comm a p⟩⟩
  apply (ZetaRieszMacroPrimeWindows.mem_logPrimes_iff _ _ _).mpr
  rw [hlog] at hT
  refine ⟨hp,by linarith only [hT.1],?_⟩
  rw [show v-Real.pi/y-Real.log a+2*Real.pi/y = v+Real.pi/y-Real.log a by ring]
  linarith only [hT.2]

/-- Every complete fibre is exactly five-prime and rough, including the
running owner prime. The roughness mask creates no prime-period hole. -/
theorem roughPeriod_data {B n : ℕ} {v y : ℝ} (hv : 100 ≤ v) (hy : 54 ≤ y)
    (hn : n ∈ roughPeriod B v y) :
    Squarefree n ∧ n.primeFactors.card = 5 ∧ ∀ r ∈ n.primeFactors, B < r := by
  obtain ⟨a,ha,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨ha,hrough⟩ := Finset.mem_filter.mp ha
  have hyabs : |y| = y := abs_of_pos (by linarith)
  have hg := fibre_geometry hv (by rwa [hyabs]) ha (by simpa only [hyabs] using hp)
  have hd := cofactor_data ha
  rw [Nat.mul_comm a p]
  refine ⟨hg.2.2.1,by simpa using hg.2.2.2.1,?_⟩
  have hpf : (p*a).primeFactors = insert p a.primeFactors := by
    rw [Nat.primeFactors_mul hg.1.ne_zero hd.1.ne_zero,hg.1.primeFactors,Finset.singleton_union]
  have hne : a.primeFactors.Nonempty := Finset.card_pos.mp (by rw [hd.2.1]; norm_num)
  obtain ⟨q,hq⟩ := hne
  have hpB : B < p := (hrough q hq).trans (hg.2.1 q hq)
  intro r hr
  rw [hpf] at hr
  rcases Finset.mem_insert.mp hr with rfl | hr
  · exact hpB
  · exact hrough r hr

theorem roughPeriod_subset_unpaid (S : Finset ℕ) {N Q P V R B : ℕ}
    (hN : 1000 ≤ N) (η : ℝ) {h L v y : ℝ} (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hQ : Q ≤ B) (hV : V ≤ B) (hv : 100 ≤ v) (hy : 54 ≤ y)
    (hcore : roughPeriod B v y ⊆ S) :
    roughPeriod B v y ⊆ S\spent S N Q P V R η h L w := by
  intro n hn
  have hd := roughPeriod_data hv hy hn
  exact Finset.mem_sdiff.mpr ⟨hcore hn,
    rough_five_not_spent S hN η hh hhu w hw hQ hV hd.2.1 hd.2.2⟩

/-- The signed five-prime complete-period floor applies to the actual
rough mask, with both Riesz hinges and the full original allocation. -/
theorem eventually_roughPeriod_part_floor {e u y ε : ℝ} (he : |e| = 1)
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (B : ℕ) (v : ℝ),
      (39/20 : ℝ)*N ≤ v-Real.pi/y → v+Real.pi/y ≤ (203/100 : ℝ)*N →
      Real.sin (y*v) = 0 → e*Real.cos (y*v) ≤ 0 →
      -ε*(Real.exp (-v/2)*v^N/N.factorial) ≤
        ∑ n ∈ roughPeriod B v y, signedPart e
          (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) y N n := by
  filter_upwards [eventually_core_part_floor (k := 4) (by norm_num) he hu hU hy hε]
    with N hN B v hlo hhi hpeak hsign
  exact hN v (roughCofactors B v) hlo hhi (Finset.filter_subset _ _) hpeak hsign

/-- Complete rough five-prime periods act directly on the five-prime part
of the CURRENT unpaid remainder. Core inclusion and all previously spent
label exclusions are proved, rather than assumed as cancellation premises.
Both arithmetic signs, both grids and the exact unmatched parts are retained.
The debit is relative to the radial units, not yet a source-scale bound. -/
theorem eventually_unpaid_rough_five_floor {u y ε : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ y) (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ (Q P V R B : ℕ) (η h : ℝ) (w : ℕ → ℝ)
      (I J : Finset ℕ) (v : ℝ),
      0 < h → h ≤ 1/20 →
      (∀ M ∈ radialIndices (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j),
        0 ≤ w M ∧ w M ≤ 1/2) → Q ≤ B → V ≤ B →
      Real.cos (y*v) = -1 →
      (∀ i ∈ I, (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
          center v y i-Real.pi/y ∧ center v y i+Real.pi/y ≤
            (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) →
      (∀ i ∈ J, (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤
          center (v+Real.pi/y) y i-Real.pi/y ∧ center (v+Real.pi/y) y i+Real.pi/y ≤
            (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) →
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let S := ZetaRieszParityPacket.coreBand u N (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
      let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 5)
      let X := fun i => roughPeriod B (center v y i) y
      let Y := fun i => roughPeriod B (center (v+Real.pi/y) y i) y;
      (∑ n ∈ E\I.biUnion X, signedPart 1 A L y N n)+
        (∑ n ∈ E\J.biUnion Y, signedPart (-1) A L y N n)-
        ε*((∑ i ∈ I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
          (∑ i ∈ J, Real.exp (-center (v+Real.pi/y) y i/2)*
            (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
        (∑ n ∈ E, ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hroom : u < Real.exp (-(11/16 : ℝ)) :=
    hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_staggered_floor (k := 4) (by norm_num) hu hU hy hε),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
        (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 11/16) hroom),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1000 : ℕ)),
    eventually_ge_atTop (32 : ℕ)]
      with j hperiod hL hlarge hj Q P V R B η h w I J v hh hhu hw hQ hV hpeak hI hJ
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let S := ZetaRieszParityPacket.coreBand u N (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
  let E := (S\spent S N Q P V R η h L w).filter (fun n => n.primeFactors.card = 5)
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  have hpi : 0 ≤ Real.pi/y := by positivity
  have hcount : 4+1 < ZetaRieszPrimeCountFrequency.dyadicPrimeCount j := by
    dsimp [ZetaRieszPrimeCountFrequency.dyadicPrimeCount]
    have hp : 0 < (2 : ℕ)^j := by positivity
    rw [pow_add]
    norm_num
    omega
  have howned {c : ℝ}
      (hlo : (39/20 : ℝ)*N ≤ c-Real.pi/y)
      (hhi : c+Real.pi/y ≤ (203/100 : ℝ)*N) : roughPeriod B c y ⊆ E := by
    have hc : 100 ≤ c := by linarith only [hlo,hNR,hpi]
    have hcore : roughPeriod B c y ⊆ S :=
      owned_subset_core (k := 4) (by norm_num) j hj hcount hu hU hy hc
        (by change 2*(11/16 : ℝ)*N ≤ L at hL; change (5/4 : ℝ)*N ≤ L; linarith)
        hlo hhi (roughCofactors B c) (Finset.filter_subset _ _)
    have hunpaid := roughPeriod_subset_unpaid (P := P) (R := R) (L := L)
      S hlarge η hh hhu w hw hQ hV hc hy hcore
    intro n hn
    exact Finset.mem_filter.mpr ⟨hunpaid hn,(roughPeriod_data hc hy hn).2.1⟩
  have hb := hperiod E I J v
    (fun i => roughCofactors B (center v y i))
    (fun i => roughCofactors B (center (v+Real.pi/y) y i))
    hpeak hI hJ (fun _ _ => Finset.filter_subset _ _) (fun _ _ => Finset.filter_subset _ _)
  dsimp only at hb ⊢
  exact hb (fun i hi => howned (hI i hi).1 (hI i hi).2)
    (fun i hi => howned (hJ i hi).1 (hJ i hi).2)

theorem eventually_joined_floor_with_rough_periods {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ η h δ ε ζ θ : ℝ, ∃ err : ℕ → ℝ,
      0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧
      0 < θ ∧ θ ≤ 1/128 ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P := ⌊Real.exp (ε*N)⌋₊
        let V := ⌊Real.exp (ζ*N)⌋₊
        let R := ⌊Real.exp (θ*N)⌋₊
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
        let Gs := radialHeads S N P V L
        let Ts := radialTail S N R
        let Ys := radialSupply N h w
        let E := S\spent S N Q P V R η h L w
        let E5 := E.filter (fun n : ℕ => n.primeFactors.card = 5)
        let Eo := E\E5
        let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
          max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
        let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
            ZetaRieszPairChamberFloor.pairSaving L y n)
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          ∀ (B : ℕ) (H : Finset ℕ) (I J : ℕ → Finset ℕ) (v : ℝ),
            Q ≤ B → V ≤ B → H ⊆ radialIndices N →
            Real.cos (y*v) = -1 →
            (∀ M ∈ H, ∀ i ∈ I M, 2*(M : ℝ) ≤ center v y i ∧
              center v y i < 2*M+2) →
            (∀ M ∈ H, ∀ i ∈ J M,
              2*(M : ℝ) ≤ center (v+Real.pi/y) y i ∧
              center (v+Real.pi/y) y i < 2*M+2) →
            (∀ i ∈ H.biUnion I, (39/20 : ℝ)*N ≤ center v y i-Real.pi/y ∧
              center v y i+Real.pi/y ≤ (203/100 : ℝ)*N) →
            (∀ i ∈ H.biUnion J,
              (39/20 : ℝ)*N ≤ center (v+Real.pi/y) y i-Real.pi/y ∧
              center (v+Real.pi/y) y i+Real.pi/y ≤ (203/100 : ℝ)*N) →
            let X := (H.biUnion I).biUnion (fun i => roughPeriod B (center v y i) y)
            let Y := (H.biUnion J).biUnion (fun i => roughPeriod B (center (v+Real.pi/y) y i) y)
            let U := (∑ n ∈ E5\X, signedPart 1 A L y N n)+
              (∑ n ∈ E5\Y, signedPart (-1) A L y N n);
            u^(N+1)*(U+W+G+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
              max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
              max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+
              (∑ n ∈ Ys, f n).re/128)-err j ≤
                ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,c,κ,r,C,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
      hc,hκ,hκeq,hr,hr1,hC,hbase⟩ := eventually_core_full_floor_with_scale hu hU hy
  let e := fun j => ‖(u : ℂ)^(dyadicMomentOrder j+1)*
    (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j))‖
  have he0 (j : ℕ) : 0 ≤ e j := norm_nonneg _
  have heLim : Tendsto e atTop (𝓝 0) := by
    have ht := (ZetaRieszGammaJoint.tendsto_core_sub_joined (by linarith : 0 < u)
      hU (fun _ => y) dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder).norm
    simpa only [norm_zero] using ht
  let err := fun j => r^(dyadicMomentOrder j)*C+e j
  have hevent : Tendsto err atTop (𝓝 0) := by
    have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const C).comp
      tendsto_dyadicMomentOrder).add heLim
    simpa only [err,Function.comp_def,zero_mul,zero_add] using ht
  refine ⟨η,h,δ,ε,ζ,θ,err,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
    (fun j => add_nonneg (mul_nonneg (pow_nonneg hr _) hC) (he0 j)),hevent,?_⟩
  filter_upwards [hbase,
    eventually_unpaid_rough_five_floor hu hU hy hκ,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszPairChamberFloor.eventually_core_subset_floor hu hU),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1 : ℕ))]
      with j hj hrough hbound hN
  obtain ⟨w,hw,hY,hscale,hcore⟩ := hj
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let P := ⌊Real.exp (ε*N)⌋₊
  let V := ⌊Real.exp (ζ*N)⌋₊
  let R := ⌊Real.exp (θ*N)⌋₊
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialHeads S N P V L
  let Ts := radialTail S N R
  let Ys := radialSupply N h w
  let E := S\spent S N Q P V R η h L w
  let E5 := E.filter (fun n : ℕ => n.primeFactors.card = 5)
  let Eo := E\E5
  let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
    max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
  let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
    weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
      ZetaRieszPairChamberFloor.pairSaving L y n)
  have hG : 0 ≤ G := Finset.sum_nonneg (fun n _ => mul_nonneg (weight_nonneg A N n)
    (add_nonneg (ZetaRieszJoinedPrefixFloor.cutoffSaving_nonneg L y n)
      (ZetaRieszPairChamberFloor.pairSaving_nonneg L y n)))
  refine ⟨w,hw,hY,hG,?_⟩
  intro B H I J v hQ hV hH hpeak hI hJ hiCore hjCore
  have hp := hrough Q P V R B η h w (H.biUnion I) (H.biUnion J) v
    hh hhu hw hQ hV hpeak hiCore hjCore
  have hd := period_grids_cost_paid hN hc hy hhu hκeq w f H I J
    hw hscale hH hI hJ
  let X := (H.biUnion I).biUnion (fun i => roughPeriod B (center v y i) y)
  let Y := (H.biUnion J).biUnion (fun i => roughPeriod B (center (v+Real.pi/y) y i) y)
  let U := (∑ n ∈ E5\X, signedPart 1 A L y N n)+
    (∑ n ∈ E5\Y, signedPart (-1) A L y N n)
  have hpaid : U ≤ (∑ n ∈ E5, f n).re+(∑ n ∈ Ys, f n).re/128 := by
    change U-κ*((∑ i ∈ H.biUnion I,
      Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
      (∑ i ∈ H.biUnion J, Real.exp (-center (v+Real.pi/y) y i/2)*
        (center (v+Real.pi/y) y i)^N/N.factorial)) ≤ (∑ n ∈ E5, f n).re at hp
    change _ ≤ (1/128 : ℝ)*(∑ n ∈ Ys, f n).re at hd
    linarith only [hp,hd]
  have hb := hbound (dyadicPrimeCount j) y Eo
    (Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset)
  change u^(N+1)*(W+G) ≤ ((u : ℂ)^(N+1)*∑ n ∈ Eo, f n).re at hb
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hb
  have hs := congrArg Complex.re (Finset.sum_sdiff (Finset.filter_subset
    (fun n : ℕ => n.primeFactors.card = 5) E) (f := f))
  change (∑ n ∈ Eo, f n).re+(∑ n ∈ E5, f n).re = (∑ n ∈ E, f n).re at hs
  let credits := max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
    max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0
  change u^(N+1)*((∑ n ∈ E, f n).re+max (∑ n ∈ Xs, f n).re 0+
    max (∑ n ∈ Zs, f n).re 0+max (∑ n ∈ Hs, f n).re 0+
    max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+
    max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-r^N*C ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hcore
  have hcore' : u^(N+1)*((∑ n ∈ E, f n).re+credits+(∑ n ∈ Ys, f n).re/64)-r^N*C ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
    convert hcore using 1
    dsimp only [credits]
    ring
  have hscaled := mul_le_mul_of_nonneg_left hpaid (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have hbridge := Complex.re_le_norm ((u : ℂ)^(N+1)*
    (coreResponse u y N (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)))
  rw [mul_sub,Complex.sub_re] at hbridge
  conv at hbridge => rhs; rw [← mul_sub]
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re-
    ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re ≤ e j at hbridge
  have hscaledLedger := congrArg (fun x : ℝ => u^(N+1)*x) hs
  have hfinal : u^(N+1)*(U+W+G+credits+(∑ n ∈ Ys, f n).re/128)-(r^N*C+e j) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
    nlinarith only [hcore',hscaled,hb,hbridge,hscaledLedger]
  convert hfinal using 1
  dsimp only [credits]
  ring

end RiemannGaussian.ZetaRieszTransitionFiveFloor

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLogShellPeriodFloor
import RiemannGaussian.ZetaRieszJointOwnerFibreFloor
import RiemannGaussian.ZetaRieszGlobalPrimePeriod
import RiemannGaussian.ZetaRieszRoughFiveJoinedFloor

/-!
# Original signed owner periods without a fixed cofactor cap

Only genuine squarefreeness, count, unique-owner geometry and the actual
lowest prime logarithm enter the floor. The old `log a <= .985 v` cap
is absent. All owner factorial orders are summed before the signed phase
bound; both Riesz hinges remain. The remaining count cost is summable on
comparable-log shells, including tiny owners at growing counts.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszTinyOwnerPeriodFloor
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaRieszFixedCountPeriod ZetaRieszSignedPeriodFloor ZetaRieszStaggeredFloor
open ZetaRieszOwnerCurvatureFloor ZetaRieszJointOwnerFibreFloor
open ZetaRieszLogShellPeriodFloor
open ZetaRieszShortDivisorCancellation
open ZetaRieszRadialCompensation ZetaRieszBandCompensation ZetaRieszMultiPeriodSix

/-- The literal whole prime fibre needs only its actual ownership gap,
not an upper cofactor share or an upper count. -/
theorem owner_fibre_geometry {a : ℕ} (ha : Squarefree a) {v y : ℝ}
    (howner : ∀ q ∈ a.primeFactors, log q ≤ v-Real.pi/y-log a)
    {p : ℕ} (hp : p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y)) :
    p.Prime ∧ (∀ q ∈ a.primeFactors, q < p) ∧ ¬p ∣ a ∧
      v-Real.pi/y < log p+log a ∧ log p+log a ≤ v+Real.pi/y := by
  have hb := logPrimes_bounds hp
  have hmax (q : ℕ) (hq : q ∈ a.primeFactors) : q < p := by
    exact_mod_cast (log_lt_log_iff
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos : (0 : ℝ) < q)
      (by exact_mod_cast hb.1.pos : (0 : ℝ) < p)).mp
      ((howner q hq).trans_lt hb.2.1)
  have hnot : ¬p ∣ a := by
    intro hh
    exact (hmax p (hb.1.mem_primeFactors hh ha.ne_zero)).false
  refine ⟨hb.1,hmax,hnot,by linarith [hb.2.1],?_⟩
  have hu := hb.2.2
  simp only [mul_div_assoc] at hu
  linarith

private theorem riesz_bound {a k : ℕ} (ha : Squarefree a)
    (hc : a.primeFactors.card=k) (hk : 2 ≤ k) (D : ℝ) :
    |VaughanLogAverage.riesz D a| ≤
      (responseConstant k/2)*log a.minFac := by
  have hh := ZetaRieszSignedSperner.riesz_bounds_minFac D ha (by omega)
  rw [hc] at hh
  have h0 : (0 : ℝ) ≤ ZetaRieszSignedSperner.parityCapacity (k-2) 0 := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ ZetaRieszSignedSperner.parityCapacity (k-2) 1 := Nat.cast_nonneg _
  have hr := log_natCast_nonneg a.minFac
  unfold responseConstant
  apply abs_le.mpr
  constructor <;> nlinarith only [hh.1,hh.2,hr,mul_nonneg h0 hr,mul_nonneg h1 hr]

/-- Both hinges have the same signed cofactor bound at every geometry. -/
theorem response_bound {a k : ℕ} (ha : Squarefree a)
    (hc : a.primeFactors.card=k) (hk : 2 ≤ k) (L T : ℝ) :
    |response L T a| ≤ responseConstant k*log a.minFac := by
  have hh := abs_sub (VaughanLogAverage.riesz (T-L) a)
    (VaughanLogAverage.riesz (log a-L) a)
  have h₁ := riesz_bound ha hc hk (T-L)
  have h₂ := riesz_bound ha hc hk (log a-L)
  dsimp only [response]
  nlinarith only [hh,h₁,h₂]

/-- The cofactor hinge is constant on this prime fibre. No saturation
condition or artificial cofactor cap enters its actual variation. -/
theorem response_variation {a k : ℕ} (ha : Squarefree a)
    (hc : a.primeFactors.card=k) (hk : 2 ≤ k) (L D E : ℝ) :
    |response L D a-response L E a| ≤ (2 : ℝ)^k/4*|D-E| := by
  have hh := ZetaRieszTentSlope.riesz_cutoff_lipschitz_quarter (D-L) (E-L) ha (by omega)
  rw [ZetaRieszTentSlope.absolute_divisor_mass_eq_card ha,
    ZetaRieszSmoothHead.card_divisors_of_squarefree ha,hc,Nat.cast_pow,Nat.cast_ofNat] at hh
  simp only [response,sub_sub_sub_cancel_right]
  exact hh.trans_eq (by ring)

/-- Pointwise identity for the SAME original owner atom, now without
the old fixed cofactor share restriction. -/
theorem owner_atom_eq {a k p : ℕ} (ha : Squarefree a) (hc : a.primeFactors.card=k)
    (hk : 2 ≤ k) (hp : p.Prime) (hmax : ∀ q ∈ a.primeFactors, q < p)
    (A : Finset ℕ) (hpA : p ∈ A) {L : ℝ} (hL : 0 < L) (e y : ℝ) (N : ℕ) :
    signedPart e (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L y N (p*a) =
      (1/L/a)*(e*partResponse e k L (log p+log a) a*
        (selectedAmplitude N (Finset.range (N+2)\ZetaRieszWingHighOrders.unpaidOrders N)
          (log a) (log p+log a)*(p : ℝ)⁻¹*cos (y*(log p+log a)))) := by
  have hpd : ¬p ∣ a := by
    intro hd
    exact (hmax p (hp.mem_primeFactors hd ha.ne_zero)).false
  have hlog : log (p*a : ℕ)=log p+log a := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha.ne_zero)]
  have hscale : 0 ≤ log (p*a : ℕ)/L := div_nonneg (log_natCast_nonneg _) hL.le
  have hm : max (e*((-1 : ℝ)^(k+1)*(-(log (p*a : ℕ)/L)*
      response L (log (p*a : ℕ)) a))) 0 =
      (log (p*a : ℕ)/L)*partResponse e k L (log (p*a : ℕ)) a := by
    unfold partResponse
    rw [mul_max_of_nonneg _ _ hscale,mul_zero]
    congr 1
    ring
  have hex : exp (-(3/2 : ℝ)*log (p*a : ℕ)) =
      exp (-log (p*a : ℕ)/2)*(p : ℝ)⁻¹*(a : ℝ)⁻¹ := by
    rw [show -(3/2 : ℝ)*log (p*a : ℕ) = -log (p*a : ℕ)/2-log (p*a : ℕ) by ring,
      exp_sub,exp_log (by exact_mod_cast Nat.mul_pos hp.pos (Nat.pos_of_ne_zero ha.ne_zero)),
      Nat.cast_mul]
    ring
  have he := selectedAmplitude_eq_fibre A N ha (by omega) hp hmax hpA
  rw [hlog] at he
  rw [signedPart,ZetaRieszOneSidedArithmetic.weight,ZetaRieszOneSidedArithmetic.amplitude,
    ZetaRieszGlobalPrimePeriod.coefficient_eq_response ha (by omega) hp hpd,
    hc,Complex.ofReal_re,hm,hex,hlog]
  rw [he]
  unfold amplitude
  rw [pow_succ]
  ring

/-- The current signed owner-fibre floor, with the artificial cofactor
cap removed. All factorial orders, both Riesz hinges and the complete
original prime support remain; this is an independent arithmetic bound. -/
theorem owner_fibre_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e| = 1)
    (A : Finset ℕ) {v y L : ℝ} (hv : 100 ≤ v) (hNv : (N : ℝ)+2 ≤ v)
    (hy : 54 ≤ y) (hL : 0 < L) {a : ℕ} (ha : Squarefree a)
    (hcnt : a.primeFactors.card=k)
    (howner : ∀ q ∈ a.primeFactors, Real.log q ≤ v-Real.pi/y-Real.log a)
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
  have hL0 : 0 < L := hL
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hd : Squarefree a ∧ a.primeFactors.card=k := ⟨ha,hcnt⟩
  have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero hd.1.ne_zero
  have hB : 0 ≤ B := mul_nonneg (responseConstant_pos k).le (Real.log_natCast_nonneg _)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (amplitude_nonneg N hv0.le)
  have hcost : 0 ≤ jointPeriodCost N v y (Real.log a) := by
    have ht : 0 < v-Real.pi/y := by dsimp [b] at hb0; linarith [Real.log_natCast_nonneg a]
    unfold jointPeriodCost
    positivity
  have hgeo (p : ℕ) (hp : p ∈ D) := owner_fibre_geometry ha howner hp
  have hT (p : ℕ) (hp : p ∈ D) : Real.log a < Real.log p+Real.log a := by
    have hp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast (hgeo p hp).1.one_lt)
    linarith
  have hc : |c| ≤ B := by
    dsimp only [c,R₀]
    rw [abs_mul,he,one_mul]
    exact (partResponse_bound he k L v a).trans (response_bound ha hcnt hk L v)
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
    have hpT := (hgeo p hp).2.2.2
    have hdisp : |Real.log p+Real.log a-v| ≤ Real.pi/y :=
      abs_le.mpr ⟨by linarith [hpT.1],by linarith [hpT.2]⟩
    exact (((partResponse_variation he k L (Real.log p+Real.log a) v a).trans
      (response_variation ha hcnt hk L _ _)).trans
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
    rw [owner_atom_eq ha hcnt hk (hgeo p hp).1 (hgeo p hp).2.1 A (hA p hp) hL e y N]
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

/-- Negative curvature and actual prime endpoints depend on the lowest
owner logarithm. They do not require it to be proportional to `v`. -/
theorem jointPeriodCost_shell_le {N : ℕ} {v y b H : ℝ}
    (hy : 54 ≤ y) (hNv : (N : ℝ)+2 ≤ v) (hH : 0 < H)
    (hP : H ≤ v-Real.pi/y-b) :
    jointPeriodCost N v y b ≤ 5/H^2 := by
  have hy0 : 0 < y := by linarith
  have hπ : Real.pi/y ≤ 1/16 := (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hπ0 : 0 ≤ Real.pi/y := by positivity
  have hV : 0 < v-Real.pi/y := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hP0 : 0 < v-Real.pi/y-b := hH.trans_le hP
  have hratio : ((N : ℝ)+1)/(v-Real.pi/y) ≤ 1 :=
    (div_le_one hV).mpr (by linarith)
  have hwidth : 2*Real.pi/y ≤ 1 := by
    calc
      _ = 2*(Real.pi/y) := by ring
      _ ≤ 2*(1/16) := mul_le_mul_of_nonneg_left hπ (by norm_num)
      _ ≤ _ := by norm_num
  have hy2 : 1 ≤ y^2 := by nlinarith
  have hinvy : (y^2)⁻¹ ≤ 1 := (inv_le_one₀ (sq_pos_of_pos hy0)).mpr hy2
  have hfirst : (2*Real.pi/y)*(((N : ℝ)+1)/(v-Real.pi/y)) ≤ 1 :=
    mul_le_one₀ hwidth (by positivity) hratio
  have hfactor : ((2*Real.pi/y)*(((N : ℝ)+1)/(v-Real.pi/y)))*(y^2)⁻¹ ≤ 1 :=
    mul_le_one₀ hfirst (by positivity) hinvy
  have heq : jointPeriodCost N v y b =
      (((2*Real.pi/y)*(((N : ℝ)+1)/(v-Real.pi/y)))*(y^2)⁻¹+4)/
        (v-Real.pi/y-b)^2 := by
    unfold jointPeriodCost
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [heq]
  calc
    _ ≤ 5/(v-Real.pi/y-b)^2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hH)
      (pow_le_pow_left₀ hH.le hP 2)

private theorem responseConstant_le (k : ℕ) : responseConstant k ≤ 6*(2 : ℝ)^k := by
  have hp (b : ℕ) : (ZetaRieszSignedSperner.parityCapacity (k-2) b : ℝ) ≤ (2 : ℝ)^k := by
    have hh := (ZetaRieszSignedSperner.parityCapacity_le_middle (k-2) b).trans
      (Nat.choose_le_two_pow (k-2) ((k-2)/2))
    have ht : (2 : ℕ)^(k-2) ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast hh.trans ht
  have h0 := hp 0
  have h1 := hp 1
  have hpow : (1 : ℝ) ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
  unfold responseConstant
  nlinarith only [h0,h1,hpow]

/-- One independent signed original fibre price, including arbitrarily
small owner shares. Only its actual prime logarithm is bounded below. -/
theorem owner_shell_row_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e|=1)
    (A : Finset ℕ) {v y L H : ℝ} (hH : 5000 ≤ H) (hNv : (N : ℝ)+2 ≤ v)
    (hy : 54 ≤ y) (hL : v/2 ≤ L) {a : ℕ} (ha : Squarefree a)
    (hc : a.primeFactors.card=k) (hshell : a.primeFactors ⊆ shellPrimes H)
    (howner : ∀ q ∈ a.primeFactors, log q ≤ v-Real.pi/y-log a)
    (hA : ∀ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y), p ∈ A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0) :
    -(amplitude N v/v)*(481*(2 : ℝ)^k/H)*(a : ℝ)⁻¹ ≤
      ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L y N (p*a) := by
  have ha1 : a ≠ 1 := by intro hh; simp [hh] at hc; omega
  have hmin := (Nat.minFac_prime ha1).mem_primeFactors (Nat.minFac_dvd a) ha.ne_zero
  have hminshell := (shellPrimes_data (hshell hmin)).2
  have hH0 : 0 < H := by linarith
  have hP : H ≤ v-Real.pi/y-log a := hminshell.1.trans (howner _ hmin)
  have hπ0 : 0 ≤ Real.pi/y := by positivity
  have hv100 : 100 ≤ v := by linarith [log_natCast_nonneg a]
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := by linarith
  have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha.ne_zero
  have hP0 : 0 < v-Real.pi/y-log a := hH0.trans_le hP
  let B := responseConstant k*log a.minFac
  let E := (2 : ℝ)^k*Real.pi/(4*y)
  have hB : 0 ≤ B := by dsimp [B]; positivity [responseConstant_pos k,log_natCast_nonneg a.minFac]
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hV0 : 0 < v-Real.pi/y := by linarith [log_natCast_nonneg a]
  have hCb : 0 ≤ jointPeriodCost N v y (log a) := by
    unfold jointPeriodCost
    positivity
  have hBbound : B ≤ responseConstant k*(4*H) :=
    mul_le_mul_of_nonneg_left hminshell.2 (responseConstant_pos k).le
  have hEbound : E ≤ (2 : ℝ)^k/64 := by
    have hh := mul_le_mul_of_nonneg_left (quarter_period_width_le hy)
      (by positivity : (0 : ℝ) ≤ 2^k)
    exact (show E=(2 : ℝ)^k*(Real.pi/(4*y)) by dsimp [E]; ring) ▸
      hh.trans_eq (by ring)
  have hinner : B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a) ≤
      (20*responseConstant k+(2 : ℝ)^k/64)/H := by
    have hbc := mul_le_mul hBbound (jointPeriodCost_shell_le hy hNv hH0 hP)
      hCb (by positivity [responseConstant_pos k])
    have hec := (div_le_div_of_nonneg_left hE hH0 hP).trans
      (div_le_div_of_nonneg_right hEbound hH0.le)
    have heq : (responseConstant k*(4*H))*(5/H^2)+((2 : ℝ)^k/64)/H =
        (20*responseConstant k+(2 : ℝ)^k/64)/H := by
      field_simp
      ring
    exact (add_le_add hbc hec).trans_eq heq
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have hpre : 2*amplitude N v/(L*a) ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹ := by
    have hh := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by positivity [amplitude_nonneg N hv0.le] :
        0 ≤ 2*amplitude N v) (by positivity : 0 < v/2) hL)
      (inv_nonneg.mpr ha0.le)
    convert hh using 1 <;> first | rfl | (simp only [div_eq_mul_inv,mul_inv_rev]; ring)
  have htotal := mul_le_mul hpre hinner (by positivity :
      0 ≤ B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a))
      (by positivity : 0 ≤ 4*(amplitude N v/v)*(a : ℝ)⁻¹)
  have hcoeff : 4*(20*responseConstant k+(2 : ℝ)^k/64) ≤ 481*(2 : ℝ)^k := by
    nlinarith only [responseConstant_le k,(show 0 ≤ (2 : ℝ)^k by positivity)]
  have hcost := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hcoeff hH0.le)
    (mul_nonneg hbase (inv_nonneg.mpr ha0.le))
  have hfloor := owner_fibre_floor hk he A hv100 hNv hy hL0 ha hc howner
    (by linarith : 5000 ≤ v-Real.pi/y-log a) hA hpeak hsign
  change -(2*amplitude N v/(L*a))*(B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a)) ≤ _ at hfloor
  have hpaid : (2*amplitude N v/(L*a))*(B*jointPeriodCost N v y (log a)+E/(v-Real.pi/y-log a)) ≤
      (amplitude N v/v)*(481*(2 : ℝ)^k/H)*(a : ℝ)⁻¹ := by
    exact htotal.trans (by convert hcost using 1 <;> ring)
  rw [neg_mul] at hfloor
  simpa only [neg_mul] using (neg_le_neg hpaid).trans hfloor

/-- The all-count constant after owner allocation is joined. -/
def ownerCountCost (k : ℕ) : ℝ := 481*(2*shellMass)^k/(k.factorial : ℝ)

/-- A fixed count-independent cost, not a new carrier. -/
def ownerAllCountCost : ℝ := 481*exp (2*shellMass)

theorem ownerAllCountCost_pos : 0 < ownerAllCountCost := by unfold ownerAllCountCost; positivity

theorem ownerAllCountCost_eq : ownerAllCountCost = 504365056 := by
  have he : exp (2*shellMass) = (4 : ℝ)^10 := by
    calc
      _ = exp (log ((4 : ℝ)^10)) := by
        congr 1
        rw [log_pow]
        unfold shellMass
        norm_num
        ring
      _ = _ := exp_log (by positivity)
  unfold ownerAllCountCost
  rw [he]
  norm_num

theorem sum_ownerCountCost_le (I : Finset ℕ) :
    (∑ k ∈ I, ownerCountCost k) ≤ ownerAllCountCost := by
  have he := NormedSpace.expSeries_div_hasSum_exp (2*shellMass)
  have hh := he.summable.sum_le_tsum I (by intro k _; positivity [shellMass_pos])
  rw [he.tsum_eq,← Real.exp_eq_exp_ℝ] at hh
  have hb := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 481)
  simpa only [ownerCountCost,ownerAllCountCost,← Finset.mul_sum,mul_div_assoc] using hb

/-- The price covers the WHOLE actual selected cofactor population with
no fixed upper cofactor share. The prime phase is summed before pricing. -/
theorem owner_shell_population_floor {k N : ℕ} (hk : 2 ≤ k) {e : ℝ} (he : |e|=1)
    (A S : Finset ℕ) {v y L H : ℝ} (hH : 5000 ≤ H) (hNv : (N : ℝ)+2 ≤ v)
    (hy : 54 ≤ y) (hL : v/2 ≤ L)
    (hS : ∀ a ∈ S, Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors ⊆ shellPrimes H)
    (howner : ∀ a ∈ S, ∀ q ∈ a.primeFactors, log q ≤ v-Real.pi/y-log a)
    (hA : ∀ a ∈ S, ∀ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y), p ∈ A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0) :
    -(ownerCountCost k/H)*(amplitude N v/v) ≤
      ∑ a ∈ S, ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L y N (p*a) := by
  have hv0 : 0 < v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have hrow := Finset.sum_le_sum (fun a (ha : a ∈ S) =>
    owner_shell_row_floor hk he A hH hNv hy hL (hS a ha).1 (hS a ha).2.1
      (hS a ha).2.2 (howner a ha) (hA a ha) hpeak hsign)
  rw [← Finset.mul_sum] at hrow
  have hmass := shell_cofactor_mass_le S k (by linarith : 1 ≤ H) hS
  have hconst : 0 ≤ 481*(2 : ℝ)^k/H :=
    div_nonneg (by positivity) (by linarith)
  have hprice := mul_le_mul_of_nonpos_left hmass
    (show -(amplitude N v/v)*(481*(2 : ℝ)^k/H) ≤ 0 from
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbase) hconst)
  calc
    _ = (-(amplitude N v/v)*(481*(2 : ℝ)^k/H))*(shellMass^k/(k.factorial : ℝ)) := by
      unfold ownerCountCost
      rw [mul_pow]
      ring
    _ ≤ _ := hprice.trans hrow

/-- All cofactor counts are priced once, including growing counts with
owner share tending to zero. The old numerical cofactor cap is absent. -/
theorem owner_all_counts_floor (I : Finset ℕ) (N : ℕ) (e : ℝ) (A : Finset ℕ)
    (S : ℕ → Finset ℕ) {v y L H : ℝ} (hI : ∀ k ∈ I, 2 ≤ k) (he : |e|=1)
    (hH : 5000 ≤ H) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y) (hL : v/2 ≤ L)
    (hS : ∀ k ∈ I, ∀ a ∈ S k, Squarefree a ∧ a.primeFactors.card=k ∧
      a.primeFactors ⊆ shellPrimes H)
    (howner : ∀ k ∈ I, ∀ a ∈ S k, ∀ q ∈ a.primeFactors, log q ≤ v-Real.pi/y-log a)
    (hA : ∀ k ∈ I, ∀ a ∈ S k,
      ∀ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y), p ∈ A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0) :
    -(ownerAllCountCost/H)*(amplitude N v/v) ≤
      ∑ k ∈ I, ∑ a ∈ S k, ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
        signedPart e (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L y N (p*a) := by
  have hrow := Finset.sum_le_sum (fun k hk => owner_shell_population_floor (hI k hk)
    he A (S k) hH hNv hy hL (hS k hk) (howner k hk) (hA k hk) hpeak hsign)
  have hv0 : 0 < v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hcost := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (sum_ownerCountCost_le I) (by linarith : 0 ≤ H))
    (div_nonneg (amplitude_nonneg N hv0.le) hv0.le)
  have hb := neg_le_neg hcost
  simpa only [neg_mul] using hb.trans (by simpa only [neg_mul,Finset.sum_neg_distrib,
    ← Finset.sum_mul,← Finset.sum_div] using hrow)

/-- Inverse owner-log prices are summable over all dyadic shells. A
growing number of shells is not an extra loss. -/
theorem sum_inverse_dyadic_shells_le (J : Finset ℕ) {H : ℝ} (hH : 0 < H) :
    (∑ j ∈ J, 1/(H*(2 : ℝ)^j)) ≤ 2/H := by
  have hg := (summable_geometric_of_norm_lt_one (x := (1/2 : ℝ))
    (by norm_num)).sum_le_tsum J (by intro j _; positivity)
  have he : ∑' j : ℕ, (1/2 : ℝ)^j = 2 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)]
    norm_num
  rw [he] at hg
  have hterm (j : ℕ) : 1/(H*(2 : ℝ)^j) = (1/H)*(1/2 : ℝ)^j := by
    simp only [one_div,mul_inv_rev,inv_pow]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ 1/H)).trans_eq (by ring)

/-- The current complete single-layer orbit places ALL cofactor primes,
including the base, in the matching dyadic owner-log shell. -/
theorem single_layer_shell {a p e : ℕ} (ha : Squarefree a)
    (hc : 2 ≤ a.primeFactors.card) (he : e ∣ a/leastPairBlock a) {L H : ℝ}
    (hD : 0 ≤ log (a/e : ℕ)-L)
    (hprime : ∀ q ∈ (a/e).primeFactors,
      (log p+(log (a/e : ℕ)-L))/2 ≤ log q)
    (howner : ∀ q ∈ a.primeFactors, log q ≤ log p)
    (hcell : 2*H ≤ log p ∧ log p ≤ 4*H) :
    a.primeFactors ⊆ shellPrimes H := by
  have hh := single_layer_all_cofactor_logs ha hc he hD hprime howner
  intro q hq
  exact mem_shellPrimes (Nat.prime_of_mem_primeFactors hq)
    (by linarith only [hcell.1,(hh q hq).1]) ((hh q hq).2.trans hcell.2)

/-- No extra comparable-log hypothesis is added on the current retained
single-layer geometry. Every sufficiently large owner belongs to a
dyadic cell whose shell contains its WHOLE cofactor support. -/
theorem retained_single_layer_shell_exists {u H : ℝ} {N K n e : ℕ}
    (hH : 0 < H) (hn : n ∈ ZetaRieszParityPacket.coreBand u N K)
    (hs : Squarefree n) (hd : ZetaRieszHigherRankHingeFloor.HigherRankData u N n e)
    (hp : 2*H ≤ log (ZetaRieszPrimeEndpoint.largestPrime n)) :
    ∃ j : ℕ, 2*(H*(2 : ℝ)^j) ≤ log (ZetaRieszPrimeEndpoint.largestPrime n) ∧
      log (ZetaRieszPrimeEndpoint.largestPrime n) < 4*(H*(2 : ℝ)^j) ∧
      (n/ZetaRieszPrimeEndpoint.largestPrime n).primeFactors ⊆ shellPrimes (H*(2 : ℝ)^j) := by
  have hratio : 1 ≤ log (ZetaRieszPrimeEndpoint.largestPrime n)/(2*H) :=
    (le_div_iff₀ (by positivity : 0 < 2*H)).mpr (by simpa using hp)
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hl : 2*(H*(2 : ℝ)^j) ≤ log (ZetaRieszPrimeEndpoint.largestPrime n) := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*H)).mp hlo
    nlinarith only [hh]
  have hh : log (ZetaRieszPrimeEndpoint.largestPrime n) < 4*(H*(2 : ℝ)^j) := by
    have hc := (div_lt_iff₀ (by positivity : 0 < 2*H)).mp hhi
    rw [pow_succ] at hc
    nlinarith only [hc]
  refine ⟨j,hl,hh,?_⟩
  have hlogs := retained_single_layer_logs hn hs hd
  intro q hq
  exact mem_shellPrimes (Nat.prime_of_mem_primeFactors hq)
    (by linarith only [hl,(hlogs q hq).1]) ((hlogs q hq).2.trans hh.le)

/-- Counts and arbitrarily many dyadic owner-log geometries are joined
BEFORE their signed cost is charged. No fixed owner-share or count bound
is present. Whole literal owner fibres are still explicit hypotheses. -/
theorem dyadic_shells_floor (J : Finset ℕ) (I : ℕ → Finset ℕ) (N : ℕ)
    (e : ℝ) (A : Finset ℕ) (S : ℕ → ℕ → Finset ℕ) {v y L H : ℝ}
    (hI : ∀ j ∈ J, ∀ k ∈ I j, 2 ≤ k) (he : |e|=1)
    (hH : 5000 ≤ H) (hNv : (N : ℝ)+2 ≤ v) (hy : 54 ≤ y) (hL : v/2 ≤ L)
    (hS : ∀ j ∈ J, ∀ k ∈ I j, ∀ a ∈ S j k, Squarefree a ∧
      a.primeFactors.card=k ∧ a.primeFactors ⊆ shellPrimes (H*(2 : ℝ)^j))
    (howner : ∀ j ∈ J, ∀ k ∈ I j, ∀ a ∈ S j k, ∀ q ∈ a.primeFactors,
      log q ≤ v-Real.pi/y-log a)
    (hA : ∀ j ∈ J, ∀ k ∈ I j, ∀ a ∈ S j k,
      ∀ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y), p ∈ A)
    (hpeak : sin (y*v)=0) (hsign : e*cos (y*v) ≤ 0) :
    -(2*ownerAllCountCost/H)*(amplitude N v/v) ≤
      ∑ j ∈ J, ∑ k ∈ I j, ∑ a ∈ S j k,
        ∑ p ∈ logPrimes (v-Real.pi/y-log a) (2*Real.pi/y),
          signedPart e (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L y N (p*a) := by
  have hH0 : 0 < H := by linarith
  have hv0 : 0 < v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hbase : 0 ≤ amplitude N v/v := div_nonneg (amplitude_nonneg N hv0.le) hv0.le
  have hheight (j : ℕ) : 5000 ≤ H*(2 : ℝ)^j := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) :
      (1 : ℝ) ≤ 2^j) hH0.le
    exact hH.trans (by simpa only [mul_one] using hh)
  have hrows := Finset.sum_le_sum (fun j hj => owner_all_counts_floor (I j) N e A (S j)
    (hI j hj) he (hheight j) hNv hy hL (hS j hj) (howner j hj) (hA j hj) hpeak hsign)
  have hcost := mul_le_mul_of_nonneg_left (sum_inverse_dyadic_shells_le J hH0)
    ownerAllCountCost_pos.le
  have hterm (j : ℕ) : ownerAllCountCost/(H*(2 : ℝ)^j) =
      ownerAllCountCost*(1/(H*(2 : ℝ)^j)) := by ring
  have htotal : (∑ j ∈ J, ownerAllCountCost/(H*(2 : ℝ)^j)) ≤ 2*ownerAllCountCost/H := by
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    exact hcost.trans_eq (by ring)
  have hpaid := neg_le_neg (mul_le_mul_of_nonneg_right htotal hbase)
  simpa only [neg_mul] using hpaid.trans (by
    simpa only [neg_mul,Finset.sum_neg_distrib,← Finset.sum_mul] using hrows)

/-- Join every selected radial prime period with every cofactor count
and dyadic owner shell. The debit uses one shared radial supply sum,
not a separate price for each count, shell, or individual prime. -/
theorem radial_dyadic_shells_floor (V : Finset ℕ) (J : ℕ → Finset ℕ)
    (I : ℕ → ℕ → Finset ℕ) (N : ℕ) (e v : ℕ → ℝ) (A : Finset ℕ)
    (S : ℕ → ℕ → ℕ → Finset ℕ) {y L H : ℝ} (hH : 5000 ≤ H) (hy : 54 ≤ y)
    (hI : ∀ i ∈ V, ∀ j ∈ J i, ∀ k ∈ I i j, 2 ≤ k)
    (he : ∀ i ∈ V, |e i|=1) (hNv : ∀ i ∈ V, (N : ℝ)+2 ≤ v i)
    (hL : ∀ i ∈ V, v i/2 ≤ L)
    (hS : ∀ i ∈ V, ∀ j ∈ J i, ∀ k ∈ I i j, ∀ a ∈ S i j k,
      Squarefree a ∧ a.primeFactors.card=k ∧ a.primeFactors ⊆ shellPrimes (H*(2 : ℝ)^j))
    (howner : ∀ i ∈ V, ∀ j ∈ J i, ∀ k ∈ I i j, ∀ a ∈ S i j k,
      ∀ q ∈ a.primeFactors, log q ≤ v i-Real.pi/y-log a)
    (hA : ∀ i ∈ V, ∀ j ∈ J i, ∀ k ∈ I i j, ∀ a ∈ S i j k,
      ∀ p ∈ logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y), p ∈ A)
    (hpeak : ∀ i ∈ V, sin (y*v i)=0)
    (hsign : ∀ i ∈ V, e i*cos (y*v i) ≤ 0) :
    -(2*ownerAllCountCost/H)*(∑ i ∈ V, amplitude N (v i)/(v i)) ≤
      ∑ i ∈ V, ∑ j ∈ J i, ∑ k ∈ I i j, ∑ a ∈ S i j k,
        ∑ p ∈ logPrimes (v i-Real.pi/y-log a) (2*Real.pi/y),
          signedPart (e i) (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L y N (p*a) := by
  have hh := Finset.sum_le_sum (fun i hi => dyadic_shells_floor (J i) (I i) N
    (e i) A (S i) (hI i hi) (he i hi) hH (hNv i hi) hy (hL i hi)
      (hS i hi) (howner i hi) (hA i hi) (hpeak i hi) (hsign i hi))
  simpa only [← Finset.mul_sum] using hh

/-- The signed all-count, all-shell PRICE tends to zero relative to the
same radial units when the owner logarithm tends to infinity. This does
not assert absolute source-scale decay of those units. -/
theorem tendsto_logarithmic_shell_price :
    Tendsto (fun N : ℕ => 2*ownerAllCountCost/(8*log ((N : ℝ)+1))) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl := tendsto_log_atTop.comp hn
  have hh := hl.const_mul_atTop (by norm_num : (0 : ℝ) < 8)
  simpa only [Function.comp_def] using (tendsto_const_nhds.div_atTop hh :
    Tendsto (fun N : ℕ => 2*ownerAllCountCost/(8*log ((N : ℝ)+1))) atTop (𝓝 0))

/-- The new all-count/all-shell price can be paid by only `1/256` of the
SAME already-selected arithmetic supply. Its original phase window and
scale hypotheses are retained, not replaced by a new supply selection.
Applying this price to a literal disjoint population still requires its
whole-fibre cover; this theorem does not fill prime holes. -/
theorem eventually_period_shell_cost_paid {c κ h y v : ℝ}
    (hc : 0 < c) (hy : 54 ≤ y) (hhu : h ≤ 1/20)
    (hκ : κ = c/(512*((⌊2*y⌋₊ : ℝ)+1)*exp 2)) :
    ∀ᶠ N : ℕ in atTop, ∀ (w : ℕ → ℝ) (f : ℕ → ℂ) (V : Finset ℕ)
      (I J : ℕ → Finset ℕ),
      (∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2) →
      (∀ M ∈ radialIndices N,
        c*(M : ℝ)*exp (2*(M : ℝ))/((M : ℝ)+1)*
          radialEnvelope N M ≤
            (∑ n ∈ supply M h (w M), f n).re) →
      V ⊆ radialIndices N →
      (∀ M ∈ V, ∀ i ∈ I M, 2*(M : ℝ) ≤ center v y i ∧
        center v y i < 2*M+2) →
      (∀ M ∈ V, ∀ i ∈ J M,
        2*(M : ℝ) ≤ center (v+Real.pi/y) y i ∧
        center (v+Real.pi/y) y i < 2*M+2) →
      (2*ownerAllCountCost/(8*log ((N : ℝ)+1)))*
        ((∑ i ∈ V.biUnion I, exp (-center v y i/2)*(center v y i)^N/N.factorial)+
          (∑ i ∈ V.biUnion J, exp (-center (v+Real.pi/y) y i/2)*
            (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
        (1/256 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re := by
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hsmall := tendsto_logarithmic_shell_price.eventually
    (gt_mem_nhds (by linarith : (0 : ℝ) < κ/2))
  filter_upwards [hsmall,eventually_ge_atTop (1 : ℕ)]
    with N hprice hN w f V I J hw hscale hV hI hJ
  have hp := ZetaRieszRoughFiveJoinedFloor.period_grids_cost_paid
    hN hc hy hhu hκ w f V I J hw hscale hV hI hJ
  let U : ℝ :=
      (∑ i ∈ V.biUnion I, exp (-center v y i/2)*(center v y i)^N/N.factorial)+
      (∑ i ∈ V.biUnion J, exp (-center (v+Real.pi/y) y i/2)*
        (center (v+Real.pi/y) y i)^N/N.factorial)
  have hnonneg : 0 ≤ U := by
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro i hi
      obtain ⟨M,hM,hii⟩ := Finset.mem_biUnion.mp hi
      have hcenter : 0 ≤ center v y i :=
        (show (0 : ℝ) ≤ 2*(M : ℝ) by positivity).trans (hI M hM i hii).1
      positivity
    · apply Finset.sum_nonneg
      intro i hi
      obtain ⟨M,hM,hii⟩ := Finset.mem_biUnion.mp hi
      have hcenter : 0 ≤ center (v+Real.pi/y) y i :=
        (show (0 : ℝ) ≤ 2*(M : ℝ) by positivity).trans (hJ M hM i hii).1
      positivity
  change κ*U ≤ (1/128 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re at hp
  change (2*ownerAllCountCost/(8*log ((N : ℝ)+1)))*U ≤ _
  calc
    _ ≤ (κ/2)*U := mul_le_mul_of_nonneg_right hprice.le hnonneg
    _ = (1/2 : ℝ)*(κ*U) := by ring
    _ ≤ (1/2 : ℝ)*((1/128 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

end RiemannGaussian.ZetaRieszTinyOwnerPeriodFloor

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSignedPeriodFloor
import RiemannGaussian.ZetaRieszOwnerMaximal

set_option autoImplicit false

/-!
# Curvature after joining the owner allocation to the factorial kernel

The selected binomial orders are multiplied into the radial amplitude
before differentiation. Their first moment pays the negative curvature
directly. No separate square-root allocation variation is charged.
The result is a signed actual-prime period inequality, not a numerical
floor for the complete joined carrier.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators Classical ContDiff
namespace RiemannGaussian.ZetaRieszOwnerCurvatureFloor
open ZetaRieszJointAllocation ZetaRieszAllocationVariation
open ZetaRieszSignedPeriodFloor

private def monomial (j : ℕ) (b T : ℝ) : ℝ :=
  Real.exp (-T/2)*(T-b)^j

private theorem monomial_contDiff (j : ℕ) (b : ℝ) :
    ContDiff ℝ ∞ (monomial j b) := by unfold monomial; fun_prop

private theorem monomial_deriv (j : ℕ) (b : ℝ) {T : ℝ} (hT : b < T) :
    HasDerivAt (monomial j b) (((j : ℝ)/(T-b)-1/2)*monomial j b T) T := by
  have hg : T-b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hT)
  have hd := ((((hasDerivAt_id T).neg.div_const 2).exp).mul
    (((hasDerivAt_id T).sub_const b).pow j))
  apply hd.congr_deriv
  simp only [id_eq,Pi.neg_apply,Pi.pow_apply,mul_one]
  unfold monomial
  have hp : (j : ℝ)*(T-b)^(j-1)*(T-b) = (j : ℝ)*(T-b)^j := by
    cases j with
    | zero => simp
    | succ j => simp only [Nat.add_sub_cancel,pow_succ]; ring
  field_simp [hg]
  linear_combination 2*hp

private theorem monomial_second (j : ℕ) (b : ℝ) {T : ℝ} (hT : b < T) :
    HasDerivAt (deriv (monomial j b))
      (((((j : ℝ)/(T-b)-1/2)^2-(j : ℝ)/(T-b)^2))*monomial j b T) T := by
  have hg : T-b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hT)
  have he : deriv (monomial j b) =ᶠ[𝓝 T]
      (fun t => ((j : ℝ)/(t-b)-1/2)*monomial j b t) := by
    filter_upwards [eventually_gt_nhds hT] with t ht
    exact (monomial_deriv j b ht).deriv
  have hd := ((((hasDerivAt_const T (j : ℝ)).div
    ((hasDerivAt_id T).sub_const b) hg).sub_const (1/2 : ℝ)).mul
      (monomial_deriv j b hT))
  have hd' : HasDerivAt (fun t => ((j : ℝ)/(t-b)-1/2)*monomial j b t)
      (((((j : ℝ)/(T-b)-1/2)^2-(j : ℝ)/(T-b)^2))*monomial j b T) T := by
    apply hd.congr_deriv
    simp only [id_eq,Pi.div_apply,mul_one,zero_sub,zero_mul]
    ring
  exact hd'.congr_of_eventuallyEq he

/-- Exact selected factorial amplitude; orders zero and one are included
whenever selected. This is a polynomial times the original exponential. -/
def selectedAmplitude (N : ℕ) (S : Finset ℕ) (b T : ℝ) : ℝ :=
  ∑ k ∈ S, ((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*monomial (N+1-k) b T

theorem selectedAmplitude_contDiff (N : ℕ) (S : Finset ℕ) (b : ℝ) :
    ContDiff ℝ ∞ (selectedAmplitude N S b) := by
  unfold selectedAmplitude
  apply ContDiff.sum
  intro k _
  exact contDiff_const.mul (monomial_contDiff (N+1-k) b)

private theorem term_eq_mass {N k : ℕ} (hk : k ≤ N+1) (b T : ℝ) (hT : T ≠ 0) :
    ((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*monomial (N+1-k) b T =
      amplitude N T*mass (N+1) k (b/T) := by
  have he : (1-b/T) = (T-b)/T := by field_simp
  have hp : T^k*T^(N+1-k) = T^(N+1) := by
    rw [← pow_add,Nat.add_sub_of_le hk]
  unfold monomial amplitude mass
  rw [he,div_pow,div_pow,← mul_div_mul_comm,hp]
  field_simp

/-- Joining the two factors is exact, including every original order. -/
theorem selectedAmplitude_eq {N : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.range (N+2)) {b T : ℝ} (hT : T ≠ 0) :
    selectedAmplitude N S b T =
      amplitude N T*(∑ k ∈ S, mass (N+1) k (b/T)) := by
  rw [selectedAmplitude,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact term_eq_mass (by have := Finset.mem_range.mp (hS hk); omega) b T hT

private theorem remaining_order_mean (N : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (N+2), (((N+1 : ℕ) : ℝ) - (k : ℝ))*mass (N+1) k x) =
      ((N+1 : ℕ) : ℝ)*(1-x) := by
  rw [show N+2 = (N+1)+1 by omega,Finset.sum_range_succ]
  simp only [sub_self,zero_mul,add_zero]
  have he : (∑ k ∈ Finset.range (N+1),
      (((N+1 : ℕ) : ℝ)-(k : ℝ))*mass (N+1) k x) =
      ((N+1 : ℕ) : ℝ)*(1-x)*∑ k ∈ Finset.range (N+1), mass N k x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact ZetaRieszOwnerVariation.mass_degree_lower (by
      have := Finset.mem_range.mp hk; omega) x
  rw [he,mass_total,mul_one]

private theorem selected_mean_le {N : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.range (N+2)) {b T : ℝ} (hb : 0 ≤ b) (hT : b < T) :
    (∑ k ∈ S, ((N+1-k : ℕ) : ℝ)*
      (((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*monomial (N+1-k) b T)) ≤
      ((N+1 : ℕ) : ℝ)*(1-b/T)*amplitude N T := by
  have hT0 : 0 < T := hb.trans_lt hT
  have hx : 0 ≤ b/T := div_nonneg hb hT0.le
  have hx1 : b/T ≤ 1 := (div_le_one hT0).mpr hT.le
  have he k (hk : k ∈ S) :
      ((N+1-k : ℕ) : ℝ)*
        (((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*monomial (N+1-k) b T) =
      amplitude N T*((((N+1 : ℕ) : ℝ)-(k : ℝ))*mass (N+1) k (b/T)) := by
    have hk' : k ≤ N+1 := by have := Finset.mem_range.mp (hS hk); omega
    rw [Nat.cast_sub hk',term_eq_mass hk' b T hT0.ne']
    ring
  rw [Finset.sum_congr rfl he,← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg hS (fun k hk _ =>
      mul_nonneg (sub_nonneg.mpr (by
        have hh : k ≤ N+1 := by have := Finset.mem_range.mp hk; omega
        exact_mod_cast hh))
        (mass_nonneg _ _ hx hx1))) (amplitude_nonneg N hT0.le)).trans_eq
  rw [remaining_order_mean]
  ring

theorem selectedAmplitude_bounds {N : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.range (N+2)) {b T : ℝ} (hb : 0 ≤ b) (hT : b < T) :
    0 ≤ selectedAmplitude N S b T ∧ selectedAmplitude N S b T ≤ amplitude N T := by
  have hT0 : 0 < T := hb.trans_lt hT
  have hx : 0 ≤ b/T := div_nonneg hb hT0.le
  have hx1 : b/T ≤ 1 := (div_le_one hT0).mpr hT.le
  rw [selectedAmplitude_eq S hS hT0.ne']
  constructor
  · exact mul_nonneg (amplitude_nonneg N hT0.le)
      (Finset.sum_nonneg (fun k _ => mass_nonneg (N+1) k hx hx1))
  · exact (mul_le_mul_of_nonneg_left
      ((Finset.sum_le_sum_of_subset_of_nonneg hS
        (fun k _ _ => mass_nonneg _ k hx hx1)).trans_eq (mass_total (N+1) (b/T)))
      (amplitude_nonneg N hT0.le)).trans_eq (mul_one _)

private theorem selected_deriv_eq {N : ℕ} (S : Finset ℕ) {b T : ℝ} (hT : b < T) :
    deriv (selectedAmplitude N S b) T =
      ∑ k ∈ S, (((N+1-k : ℕ) : ℝ)/(T-b)-1/2)*
        (((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*monomial (N+1-k) b T) := by
  have hd := HasDerivAt.sum (fun k (_hk : k ∈ S) =>
    (monomial_deriv (N+1-k) b hT).const_mul
      (((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)))
  have he : (∑ k ∈ S, fun t =>
      ((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*monomial (N+1-k) b t) =
      selectedAmplitude N S b := by funext t; simp [selectedAmplitude]
  rw [he] at hd
  rw [hd.deriv]
  exact Finset.sum_congr rfl (fun k _ => by ring)

private theorem selected_second_eq {N : ℕ} (S : Finset ℕ) {b T : ℝ} (hT : b < T) :
    deriv (deriv (selectedAmplitude N S b)) T =
      ∑ k ∈ S, ((((N+1-k : ℕ) : ℝ)/(T-b)-1/2)^2-
          ((N+1-k : ℕ) : ℝ)/(T-b)^2)*
        (((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*monomial (N+1-k) b T) := by
  have he : deriv (selectedAmplitude N S b) =ᶠ[𝓝 T]
      (fun t => ∑ k ∈ S, ((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*
        deriv (monomial (N+1-k) b) t) := by
    filter_upwards [eventually_gt_nhds hT] with t ht
    rw [selected_deriv_eq S ht]
    exact Finset.sum_congr rfl (fun k _ => by rw [(monomial_deriv _ _ ht).deriv]; ring)
  have hd := HasDerivAt.sum (fun k (_hk : k ∈ S) =>
    (monomial_second (N+1-k) b hT).const_mul
      (((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)))
  have hdf : HasDerivAt (fun t => ∑ k ∈ S,
      ((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*deriv (monomial (N+1-k) b) t)
      (∑ k ∈ S, ((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*
        (((((N+1-k : ℕ) : ℝ)/(T-b)-1/2)^2-((N+1-k : ℕ) : ℝ)/(T-b)^2)*
          monomial (N+1-k) b T)) T := by
    have hfun : (∑ k ∈ S, fun t =>
        ((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*deriv (monomial (N+1-k) b) t) =
        (fun t => ∑ k ∈ S,
          ((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*deriv (monomial (N+1-k) b) t) := by
      funext t
      simp only [Finset.sum_apply]
    rw [hfun] at hd
    exact hd
  have hd' := hdf.congr_of_eventuallyEq he
  rw [hd'.deriv]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The joint derivative has no binomial score variation charge. -/
theorem selectedAmplitude_deriv_bound {N : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.range (N+2)) {b T : ℝ} (hb : 0 ≤ b) (hT : b < T) :
    |deriv (selectedAmplitude N S b) T| ≤
      (((N+1 : ℕ) : ℝ)/T+1/2)*amplitude N T := by
  have hg : 0 < T-b := sub_pos.mpr hT
  have hT0 : 0 < T := hb.trans_lt hT
  have hp k : 0 ≤ ((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*monomial (N+1-k) b T :=
    by unfold monomial; positivity
  rw [selected_deriv_eq S hT]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hscore k : |((N+1-k : ℕ) : ℝ)/(T-b)-1/2| ≤
      ((N+1-k : ℕ) : ℝ)/(T-b)+1/2 := by
    apply (abs_sub _ _).trans_eq
    rw [abs_of_nonneg (by positivity),abs_of_nonneg (by norm_num)]
  have hs := Finset.sum_le_sum (fun k (_hk : k ∈ S) =>
    mul_le_mul_of_nonneg_right (hscore k) (hp k))
  simp only [abs_mul,abs_of_nonneg (hp _)]
  apply hs.trans
  have hm := div_le_div_of_nonneg_right (selected_mean_le S hS hb hT) hg.le
  have hf := mul_le_mul_of_nonneg_left (selectedAmplitude_bounds S hS hb hT).2
    (by norm_num : (0 : ℝ) ≤ 1/2)
  have he : (((N+1 : ℕ) : ℝ)*(1-b/T)*amplitude N T)/(T-b) =
      ((N+1 : ℕ) : ℝ)/T*amplitude N T := by field_simp
  rw [he] at hm
  have he' : (∑ k ∈ S, (((N+1-k : ℕ) : ℝ)/(T-b)+1/2)*
      (((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*monomial (N+1-k) b T)) =
      (∑ k ∈ S, ((N+1-k : ℕ) : ℝ)*
        (((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*monomial (N+1-k) b T))/(T-b)+
        (1/2 : ℝ)*selectedAmplitude N S b T := by
    simp only [selectedAmplitude,Finset.mul_sum,Finset.sum_div,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [he']
  nlinarith only [hm,hf]

/-- Negative curvature is paid by the full first moment. This keeps the
selected factorial channels coupled and charges no allocation derivative. -/
theorem selectedAmplitude_curvature_floor {N : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.range (N+2)) {b T : ℝ} (hb : 0 ≤ b) (hT : b < T) :
    -(((N+1 : ℕ) : ℝ)/(T*(T-b)))*amplitude N T ≤
      deriv (deriv (selectedAmplitude N S b)) T := by
  have hg : 0 < T-b := sub_pos.mpr hT
  have hT0 : 0 < T := hb.trans_lt hT
  have hp k : 0 ≤ ((N+1).choose k : ℝ)*b^k/(N.factorial : ℝ)*monomial (N+1-k) b T :=
    by unfold monomial; positivity
  have hs := Finset.sum_le_sum (fun k (_hk : k ∈ S) =>
    mul_le_mul_of_nonneg_right
      (show -((N+1-k : ℕ) : ℝ)/(T-b)^2 ≤
        (((N+1-k : ℕ) : ℝ)/(T-b)-1/2)^2-((N+1-k : ℕ) : ℝ)/(T-b)^2 by
        rw [neg_div]
        linarith only [sq_nonneg (((N+1-k : ℕ) : ℝ)/(T-b)-1/2)]) (hp k))
  rw [selected_second_eq S hT]
  apply le_trans _ hs
  have hm := neg_le_neg (div_le_div_of_nonneg_right (selected_mean_le S hS hb hT)
    (sq_nonneg (T-b)))
  convert hm using 1
  · field_simp [hT0.ne',hg.ne']
  · simp only [Finset.sum_div,← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)

/-- Signed cancellation for the actual finite prime period with the
selected owner orders already joined to the radial kernel. The explicit
prime endpoint cost remains; no separate allocation variation is charged. -/
theorem selected_prime_period_upper {N : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.range (N+2)) {b v y W : ℝ} (hb : 0 ≤ b)
    (ha : 5000 ≤ v-Real.pi/y-b) (hy : 54 ≤ y) (hv : (N : ℝ)+2 ≤ v)
    (hW : 0 ≤ W)
    (hw : ∀ t ∈ Icc (v-Real.pi/y) (v+Real.pi/y), amplitude N t ≤ W) :
    (∑ p ∈ (Finset.Ioc ⌊Real.exp (v-Real.pi/y-b)⌋₊
        ⌊Real.exp (v-Real.pi/y-b+2*Real.pi/y)⌋₊).filter Nat.Prime,
      selectedAmplitude N S b (Real.log p+b)*
        Real.cos (y*(Real.log p+b-v))/(p : ℝ)) ≤
      W*((2*Real.pi/y)*((N : ℝ)+1)/
        ((v-Real.pi/y)*(v-Real.pi/y-b)^2*y^2)+4/(v-Real.pi/y-b)^2) := by
  let a := v-Real.pi/y-b
  have hy0 : 0 < y := by linarith
  have ha0 : 0 < a := by dsimp [a]; linarith
  have hv0 : 0 < v-Real.pi/y := by dsimp [a] at ha0; linarith
  have hπu : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have ht (t : ℝ) (ht : t ∈ Icc (v-Real.pi/y) (v+Real.pi/y)) :
      (N : ℝ)+1 ≤ t ∧ b < t ∧ 0 < t := by
    have hg : a ≤ t-b := by dsimp [a]; linarith [ht.1]
    constructor
    · linarith [ht.1]
    · constructor <;> linarith
  have hf := selectedAmplitude_contDiff N S b
  have hg := (contDiff_infty_iff_deriv.mp hf).2
  have hgc := (contDiff_infty_iff_deriv.mp hg).2.continuous
  have hder := (contDiff_infty_iff_deriv.mp hf).1
  have hder' := (contDiff_infty_iff_deriv.mp hg).1
  have hfirst (t : ℝ) (hmem : t ∈ Icc (v-Real.pi/y) (v+Real.pi/y)) :
      |deriv (selectedAmplitude N S b) t| ≤ (3/2 : ℝ)*W := by
    have hs : (((N+1 : ℕ) : ℝ)/t+1/2) ≤ 3/2 := by
      have hhi : (((N+1 : ℕ) : ℝ)/t) ≤ 1 :=
        (div_le_one (ht t hmem).2.2).mpr (by simpa only [Nat.cast_add,Nat.cast_one] using (ht t hmem).1)
      linarith
    exact (selectedAmplitude_deriv_bound S hS hb (ht t hmem).2.1).trans
      (mul_le_mul hs (hw t hmem) (amplitude_nonneg N (ht t hmem).2.2.le)
        (by norm_num : (0 : ℝ) ≤ 3/2))
  have hcurv (t : ℝ) (hmem : t ∈ Icc (v-Real.pi/y) (v+Real.pi/y)) :
      -(((N : ℝ)+1)*W/((v-Real.pi/y)*a)) ≤
        deriv (deriv (selectedAmplitude N S b)) t := by
    have hgap : a ≤ t-b := by dsimp [a]; linarith [hmem.1]
    have hden : (v-Real.pi/y)*a ≤ t*(t-b) :=
      mul_le_mul hmem.1 hgap ha0.le (ht t hmem).2.2.le
    have hratio : ((N : ℝ)+1)/(t*(t-b)) ≤ ((N : ℝ)+1)/((v-Real.pi/y)*a) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hv0 ha0) hden
    have hmul := mul_le_mul hratio (hw t hmem)
      (amplitude_nonneg N (ht t hmem).2.2.le)
      (div_nonneg (by positivity) (mul_pos hv0 ha0).le)
    calc
      _ = -(((N : ℝ)+1)/((v-Real.pi/y)*a)*W) := by ring
      _ ≤ -(((N : ℝ)+1)/(t*(t-b))*amplitude N t) := neg_le_neg hmul
      _ = -(((N+1 : ℕ) : ℝ)/(t*(t-b)))*amplitude N t := by push_cast; ring
      _ ≤ _ := selectedAmplitude_curvature_floor S hS hb (ht t hmem).2.1
  have hperiod := prime_period_upper (selectedAmplitude N S b)
    (deriv (selectedAmplitude N S b)) (deriv (deriv (selectedAmplitude N S b)))
    ha hy0 hW (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3/2) hW)
    (fun t => (hder t).hasDerivAt) (fun t => (hder' t).hasDerivAt) hgc
    (fun t hm => by
      rw [abs_of_nonneg (selectedAmplitude_bounds S hS hb (ht t hm).2.1).1]
      exact (selectedAmplitude_bounds S hS hb (ht t hm).2.1).2.trans (hw t hm))
    hfirst hcurv
  have hcost : W*(2*Real.pi/y)^2+
      (41/100 : ℝ)*(2*W+((3/2 : ℝ)*W+y*W+2*W)*(2*Real.pi/y)) ≤ 4*W := by
    have hh : 2*Real.pi/y ≤ 1/8 := by
      calc
        _ = 2*(Real.pi/y) := by ring
        _ ≤ _ := by linarith
    have hsq : (2*Real.pi/y)^2 ≤ (1/8 : ℝ)^2 :=
      pow_le_pow_left₀ (by positivity) hh 2
    have hprod : y*(2*Real.pi/y) = 2*Real.pi := by field_simp
    have hplain : (2*Real.pi/y)^2+
        (41/100 : ℝ)*(2+(3/2+y+2)*(2*Real.pi/y)) ≤ 4 := by
      nlinarith [Real.pi_lt_d4]
    have hm := mul_le_mul_of_nonneg_left hplain hW
    ring_nf at hm ⊢
    exact hm
  have harg p : Real.log p+v-Real.pi/y-(v-Real.pi/y-b) = Real.log p+b := by ring
  have harg' p : Real.log p-Real.pi/y-(v-Real.pi/y-b) = Real.log p+b-v := by ring
  simp_rw [harg,harg'] at hperiod
  apply hperiod.trans
  have he := div_le_div_of_nonneg_right hcost (sq_nonneg a)
  have hden : (2*Real.pi/y)*(((N : ℝ)+1)*W/((v-Real.pi/y)*a))/(a*y^2) =
      W*((2*Real.pi/y)*((N : ℝ)+1)/((v-Real.pi/y)*a^2*y^2)) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hden]
  calc
    _ ≤ W*((2*Real.pi/y)*((N : ℝ)+1)/((v-Real.pi/y)*a^2*y^2))+4*W/a^2 :=
      add_le_add le_rfl he
    _ = _ := by dsimp [a]; ring

/-- The joined selected orders are exactly the original owner weight,
not an approximate indicator of the owner share. -/
theorem selectedAmplitude_ownerWeight {N : ℕ} {b T : ℝ} (hT : T ≠ 0) :
    selectedAmplitude N (Finset.range (N+2)\ZetaRieszWingHighOrders.unpaidOrders N) b T =
      amplitude N T*ZetaRieszOwnerMaximal.ownerWeight N (b/T) := by
  have hsub : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+2) := by
    intro k hk
    have hk' := (ZetaRieszWingHighOrders.unpaidOrders_support hk).1
    have := ZetaRieszReflectedCompletion.lowerWing_bounds hk'
    simp only [Finset.mem_range]
    omega
  rw [selectedAmplitude_eq _ Finset.sdiff_subset hT]
  have hs := Finset.sum_sdiff hsub (f := fun k => mass (N+1) k (b/T))
  have htotal : (∑ k ∈ Finset.range (N+2), mass (N+1) k (b/T)) = 1 := by
    exact mass_total (N+1) (b/T)
  rw [htotal] at hs
  congr 1
  unfold ZetaRieszOwnerMaximal.ownerWeight
  linarith only [hs]

/-- Exact bridge to the literal largest-prime allocation in the carrier. -/
theorem selectedAmplitude_eq_fibre (A : Finset ℕ) (N : ℕ) {a p : ℕ}
    (ha : Squarefree a) (hc : 2 ≤ a.primeFactors.card) (hp : p.Prime)
    (hmax : ∀ q ∈ a.primeFactors, q < p) (hpA : p ∈ A) :
    selectedAmplitude N (Finset.range (N+2)\ZetaRieszWingHighOrders.unpaidOrders N)
        (Real.log a) (Real.log (p*a : ℕ)) =
      amplitude N (Real.log (p*a : ℕ))*
        (1-boundedShare (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) N (p*a)) := by
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (Squarefree.ne_zero ha)
  have hn : 1 < p*a := lt_of_lt_of_le hp.one_lt (Nat.le_mul_of_pos_right p ha1)
  have hlog : 0 < Real.log (p*a : ℕ) := Real.log_pos (by exact_mod_cast hn)
  rw [selectedAmplitude_ownerWeight hlog.ne',
    ZetaRieszOwnerMaximal.ownerWeight_eq_fibre A N ha hc hp hmax hpA]

open ZetaRieszAllowancePrimeBoxes

/-- An independent one-sided actual-prime floor for the full retained
factorial selection on a sign-aligned phase period. Only negative joint
curvature and the literal prime endpoint cost enter this bound. -/
theorem selected_period_floor {N : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.range (N+2)) {v y b c : ℝ} (hb : 0 ≤ b)
    (ha : 5000 ≤ v-Real.pi/y-b) (hy : 54 ≤ y) (hv : (N : ℝ)+2 ≤ v)
    (hpeak : Real.sin (y*v) = 0) (hsign : c*Real.cos (y*v) ≤ 0) :
    -2*|c| *amplitude N v*
        ((2*Real.pi/y)*((N : ℝ)+1)/
          ((v-Real.pi/y)*(v-Real.pi/y-b)^2*y^2)+4/(v-Real.pi/y-b)^2) ≤
      c*(∑ p ∈ logPrimes (v-Real.pi/y-b) (2*Real.pi/y),
        selectedAmplitude N S b (Real.log p+b)*(p : ℝ)⁻¹*
          Real.cos (y*(Real.log p+b))) := by
  let a := v-Real.pi/y-b
  let D := logPrimes a (2*Real.pi/y)
  let W := 2*amplitude N v
  let E := (2*Real.pi/y)*((N : ℝ)+1)/((v-Real.pi/y)*a^2*y^2)+4/a^2
  have hy0 : 0 < y := by linarith
  have hv0 : 0 < v := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have ha0 : 0 < a := by dsimp [a]; linarith
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (amplitude_nonneg N hv0.le)
  have hπu : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hweight (t : ℝ) (ht : t ∈ Icc (v-Real.pi/y) (v+Real.pi/y)) :
      amplitude N t ≤ W := amplitude_near N (by linarith)
        (by linarith [ht.1,Nat.cast_nonneg (α := ℝ) N])
        (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hset : D = (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/y)⌋₊).filter Nat.Prime := by
    dsimp [D,logPrimes,PrimeWindow.primesInWindow]
    rw [← Real.exp_add,add_comm (2*Real.pi/y) a]
  have hup := selected_prime_period_upper S hS hb ha hy hv hW hweight
  have hupper : (∑ p ∈ D,
      selectedAmplitude N S b (Real.log p+b)*(p : ℝ)⁻¹*
        Real.cos (y*(Real.log p+b-v))) ≤ W*E := by
    rw [← hset] at hup
    change _ ≤ W*E at hup
    convert hup using 1
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have hcost : 0 ≤ W*E := by
    have hvp : 0 < v-Real.pi/y := by dsimp [a] at ha0; linarith
    dsimp only [E]
    positivity
  have hphase (t : ℝ) : Real.cos (y*t) = Real.cos (y*v)*Real.cos (y*(t-v)) := by
    rw [show y*t = y*v+y*(t-v) by ring,Real.cos_add,hpeak]
    ring
  have he : c*(∑ p ∈ D,
      selectedAmplitude N S b (Real.log p+b)*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+b))) =
      (c*Real.cos (y*v))*(∑ p ∈ D,
        selectedAmplitude N S b (Real.log p+b)*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+b-v))) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by rw [hphase]; ring)
  have hc : -|c| ≤ c*Real.cos (y*v) := by
    have habs : |c*Real.cos (y*v)| ≤ |c| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg c)).trans_eq (mul_one _)
    exact (neg_le_neg habs).trans (neg_abs_le _)
  change -2*|c| *amplitude N v*E ≤ c*(∑ p ∈ D, _)
  rw [he]
  have h₁ := mul_le_mul_of_nonpos_left hupper hsign
  have h₂ := mul_le_mul_of_nonneg_right hc hcost
  dsimp only [W] at h₁ h₂
  nlinarith only [h₁,h₂]

end RiemannGaussian.ZetaRieszOwnerCurvatureFloor

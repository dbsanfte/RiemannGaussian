/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTaggedOwnerComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Signed owner phase across the complete physical log window

The original finite owner allocation is a polynomial after multiplication
by the full factorial kernel. Its damped primitive retains the phase until
the TWO exterior endpoints. Only those endpoint norms are estimated.
This file does not assert transport of arbitrary arithmetic masks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Real Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszOwnerPhasePrimitive
open ZetaRieszOwnerMaximal ZetaRieszJointAllocation
open ZetaRieszSmoothOwnerDiscrepancy ZetaRieszTaggedOwnerComparison

/-- The exact finite factorial primitive polynomial, including order zero. -/
def factorialTail : ℕ → ℂ → ℝ → ℂ
  | 0,z,_ => z⁻¹
  | n+1,z,t => ((t : ℂ)^(n+1)/((n+1).factorial : ℂ)+factorialTail n z t)/z

private theorem factorial_monomial_deriv (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ)^(n+1)/((n+1).factorial : ℂ))
      ((t : ℂ)^n/(n.factorial : ℂ)) t := by
  have h := (((hasDerivAt_id t).ofReal_comp).pow (n+1)).div_const
    ((n+1).factorial : ℂ)
  apply h.congr_deriv
  simp only [Nat.add_sub_cancel,id_eq,Complex.ofReal_one,mul_one]
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hn : (n : ℂ)+1≠0 := by exact_mod_cast (show n+1≠0 by omega)
  have hf : (n.factorial : ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

theorem factorialTail_deriv (n : ℕ) {z : ℂ} (hz : z≠0) (t : ℝ) :
    HasDerivAt (factorialTail n z)
      (z*factorialTail n z t-(t : ℂ)^n/(n.factorial : ℂ)) t := by
  induction n with
  | zero => simpa [factorialTail,hz] using hasDerivAt_const t z⁻¹
  | succ n ih =>
    have h := ((factorial_monomial_deriv n t).add ih).div_const z
    apply h.congr_deriv
    simp only [factorialTail]
    field_simp
    ring

/-- An exact primitive of the signed factorial phase, without any
frequency freezing or separate bounds for interior factorial orders. -/
def dampedPrimitive (n : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-z*t)*factorialTail n z t

theorem dampedPrimitive_deriv (n : ℕ) {z : ℂ} (hz : z≠0) (t : ℝ) :
    HasDerivAt (dampedPrimitive n z)
      (-Complex.exp (-z*t)*((t : ℂ)^n/(n.factorial : ℂ))) t := by
  have he := (((hasDerivAt_id t).ofReal_comp).const_mul (-z)).cexp
  apply (he.mul (factorialTail_deriv n hz t)).congr_deriv
  dsimp [dampedPrimitive]
  ring

theorem factorial_phase_integral (n : ℕ) {z : ℂ} (hz : z≠0) (a b : ℝ) :
    (∫ t : ℝ in a..b, Complex.exp (-z*t)*((t : ℂ)^n/(n.factorial : ℂ))) =
      dampedPrimitive n z a-dampedPrimitive n z b := by
  have hiNeg : IntervalIntegrable (fun t : ℝ =>
      -Complex.exp (-z*t)*((t : ℂ)^n/(n.factorial : ℂ))) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => dampedPrimitive_deriv n hz t) hiNeg
  simp only [neg_mul,intervalIntegral.integral_neg] at h
  simpa only [neg_neg,neg_sub,neg_mul] using congrArg Neg.neg h

private theorem real_monomial_norm (n : ℕ) {t : ℝ} (ht : 0≤t) :
    ‖(t : ℂ)^n/(n.factorial : ℂ)‖=t^n/(n.factorial : ℝ) := by
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]
  have he : (n.factorial : ℂ)=((n.factorial : ℝ) : ℂ) := by norm_cast
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]

/-- The full finite derivative tail is controlled at an endpoint when
the ACTUAL complex damping dominates its polynomial order. -/
theorem factorialTail_norm (n : ℕ) {z : ℂ} (hz : z≠0) {t : ℝ} (ht : 0<t)
    (hsep : 2*(n : ℝ)≤‖z‖*t) :
    ‖factorialTail n z t‖≤(2/‖z‖)*(t^n/(n.factorial : ℝ)) := by
  have hz0 : 0<‖z‖ := norm_pos_iff.mpr hz
  induction n with
  | zero =>
    simp only [factorialTail,norm_inv,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,mul_one]
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by norm_num : (1 : ℝ)≤2) hz0.le
  | succ n ih =>
    have hsep0 : 2*(n : ℝ)≤‖z‖*t := by
      simp only [Nat.cast_add,Nat.cast_one] at hsep
      linarith
    have ih := ih hsep0
    have hf : (n.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hn : (n : ℝ)+1≠0 := by positivity
    have he : t^n/(n.factorial : ℝ)=
        (((n : ℝ)+1)/t)*(t^(n+1)/((n+1).factorial : ℝ)) := by
      rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
      field_simp
    have hr : (2/‖z‖)*(((n : ℝ)+1)/t)≤1 := by
      rw [show (2/‖z‖)*(((n : ℝ)+1)/t)=
        (2*((n : ℝ)+1))/(‖z‖*t) by ring]
      apply (div_le_one (mul_pos hz0 ht)).mpr
      simpa only [Nat.cast_add,Nat.cast_one] using hsep
    have hb : (2/‖z‖)*(t^n/(n.factorial : ℝ))≤
        t^(n+1)/((n+1).factorial : ℝ) := by
      rw [he,← mul_assoc]
      exact mul_le_of_le_one_left (by positivity) hr
    simp only [factorialTail,norm_div]
    calc
      _ ≤ (‖(t : ℂ)^(n+1)/((n+1).factorial : ℂ)‖+
          ‖factorialTail n z t‖)/‖z‖ :=
        div_le_div_of_nonneg_right (norm_add_le _ _) hz0.le
      _ ≤ (t^(n+1)/((n+1).factorial : ℝ)+t^(n+1)/((n+1).factorial : ℝ))/‖z‖ := by
        rw [real_monomial_norm (n+1) ht.le]
        exact div_le_div_of_nonneg_right (add_le_add le_rfl (ih.trans hb)) hz0.le
      _ = _ := by ring

theorem dampedPrimitive_norm (n : ℕ) {z : ℂ} (hz : z≠0) {t : ℝ} (ht : 0<t)
    (hsep : 2*(n : ℝ)≤‖z‖*t) :
    ‖dampedPrimitive n z t‖≤(2/‖z‖)*exp (-z.re*t)*
      (t^n/(n.factorial : ℝ)) := by
  rw [dampedPrimitive,norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero]
  exact (mul_le_mul_of_nonneg_left (factorialTail_norm n hz ht hsep)
    (exp_pos _).le).trans_eq (by ring)

private theorem unpaid_le {N k : ℕ} (hk : k∈ZetaRieszWingHighOrders.unpaidOrders N) :
    k≤N+1 := by
  have hk' := (ZetaRieszWingHighOrders.unpaidOrders_support hk).1
  have h := ZetaRieszReflectedCompletion.lowerWing_bounds hk'
  omega

private theorem mass_scaled {n k : ℕ} (hk : k≤n) {c t : ℝ} (ht : t≠0) :
    mass n k ((t-c)/t)*t^n=(n.choose k : ℝ)*c^(n-k)*(t-c)^k := by
  have he : 1-(t-c)/t=c/t := by field_simp; ring
  rw [mass,he,div_pow,div_pow]
  have hp : t^k*t^(n-k)=t^n := by rw [← pow_add,Nat.add_sub_of_le hk]
  calc
    _ = ((t-c)^k*c^(n-k)*(n.choose k : ℝ))/(t^k*t^(n-k))*t^n := by ring
    _ = _ := by rw [hp]; field_simp

/-- The ACTUAL owner selector times its full successor factorial kernel.
It is a polynomial identity, not a limiting share mask. -/
def ownerPhase (N : ℕ) (c : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-z*t)/(N.factorial : ℂ)*
    ((t : ℂ)^(N+1)-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      ((N+1).choose k : ℂ)*(c : ℂ)^(N+1-k)*((t-c : ℝ) : ℂ)^k)

theorem ownerPhase_eq_weight (N : ℕ) (c : ℝ) (z : ℂ) {t : ℝ} (ht : t≠0) :
    ownerPhase N c z t = (ownerWeight N ((t-c)/t) : ℂ)*
      Complex.exp (-z*t)*(t : ℂ)^(N+1)/(N.factorial : ℂ) := by
  have hm k (hk : k∈ZetaRieszWingHighOrders.unpaidOrders N) :=
    mass_scaled (unpaid_le hk) (c := c) ht
  have he : (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      mass (N+1) k ((t-c)/t))*t^(N+1) =
      ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
        ((N+1).choose k : ℝ)*c^(N+1-k)*(t-c)^k := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl hm
  have hec := congrArg (fun v : ℝ => (v : ℂ)) he
  push_cast at hec
  unfold ownerPhase ownerWeight
  push_cast
  rw [← hec]
  ring

/-- A single marked factorial slot of the exact allocation primitive. -/
def slotPrimitive (N k : ℕ) (c : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (((N+1).choose k : ℂ)*(c : ℂ)^(N+1-k)*(k.factorial : ℂ)/(N.factorial : ℂ))*
    Complex.exp (-z*c)*dampedPrimitive k z (t-c)

theorem slotPrimitive_deriv (N k : ℕ) (c : ℝ) {z : ℂ} (hz : z≠0) (t : ℝ) :
    HasDerivAt (slotPrimitive N k c z)
      (-Complex.exp (-z*t)/(N.factorial : ℂ)*
        (((N+1).choose k : ℂ)*(c : ℂ)^(N+1-k)*((t-c : ℝ) : ℂ)^k)) t := by
  have h := (dampedPrimitive_deriv k hz (t-c)).scomp t ((hasDerivAt_id t).sub_const c)
  have he : Complex.exp (-z*c)*Complex.exp (-z*(t-c))=Complex.exp (-z*t) := by
    rw [← Complex.exp_add]; congr 1; ring
  apply (h.const_mul
    ((((N+1).choose k : ℂ)*(c : ℂ)^(N+1-k)*(k.factorial : ℂ)/(N.factorial : ℂ))*
      Complex.exp (-z*c))).congr_deriv
  dsimp [slotPrimitive]
  have hf : (k.factorial : ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [show -z*((t-c : ℝ) : ℂ)=-z*(t-c) by rw [Complex.ofReal_sub]]
  calc
    _ = -((((N+1).choose k : ℂ)*(c : ℂ)^(N+1-k)/(N.factorial : ℂ))*
      (Complex.exp (-z*c)*Complex.exp (-z*(t-c)))*((t-c : ℝ) : ℂ)^k) := by field_simp
    _ = _ := by rw [he]; ring

/-- All factorial orders are summed in the same primitive BEFORE norms. -/
def ownerPrimitive (N : ℕ) (c : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  ((N : ℂ)+1)*dampedPrimitive (N+1) z t-
    ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, slotPrimitive N k c z t

theorem ownerPrimitive_deriv (N : ℕ) (c : ℝ) {z : ℂ} (hz : z≠0) (t : ℝ) :
    HasDerivAt (ownerPrimitive N c z) (-ownerPhase N c z t) t := by
  have h := ((dampedPrimitive_deriv (N+1) hz t).const_mul ((N : ℂ)+1)).sub
    (HasDerivAt.fun_sum (fun k (_hk : k∈ZetaRieszWingHighOrders.unpaidOrders N) =>
      slotPrimitive_deriv N k c hz t))
  apply h.congr_deriv
  dsimp [ownerPhase,ownerPrimitive]
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hn : (N : ℂ)+1≠0 := by exact_mod_cast (show N+1≠0 by omega)
  have hf : (N.factorial : ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero N
  rw [← Finset.mul_sum]
  field_simp
  ring

/-- Exact signed integral with the full original owner allocation.
There is no interior norm cost and no period-by-period allowance. -/
theorem ownerPhase_integral (N : ℕ) (c : ℝ) {z : ℂ} (hz : z≠0) (a b : ℝ) :
    (∫ t : ℝ in a..b, ownerPhase N c z t)=
      ownerPrimitive N c z a-ownerPrimitive N c z b := by
  have hi : IntervalIntegrable (ownerPhase N c z) volume a b := by
    apply Continuous.intervalIntegrable
    unfold ownerPhase
    fun_prop
  have hiNeg : IntervalIntegrable (fun t => -ownerPhase N c z t) volume a b := hi.neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => ownerPrimitive_deriv N c hz t) hiNeg
  rw [intervalIntegral.integral_neg] at h
  simpa only [neg_neg,neg_sub] using congrArg Neg.neg h

private theorem allocated_monomials_le (N : ℕ) {c t : ℝ} (hc : 0≤c) (ht : c<t) :
    (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      ((N+1).choose k : ℝ)*c^(N+1-k)*(t-c)^k)≤t^(N+1) := by
  have ht0 : 0<t := hc.trans_lt ht
  have hx : 0≤(t-c)/t := div_nonneg (by linarith) ht0.le
  have hx1 : (t-c)/t≤1 := (div_le_one ht0).mpr (by linarith)
  have hm := (ownerWeight_bounds N hx hx1).1
  change 0≤1-(∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
    mass (N+1) k ((t-c)/t)) at hm
  have hs : (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      ((N+1).choose k : ℝ)*c^(N+1-k)*(t-c)^k) =
      (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
        mass (N+1) k ((t-c)/t))*t^(N+1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k hk => (mass_scaled (unpaid_le hk) ht0.ne').symm)
  rw [hs]
  exact mul_le_of_le_one_left (by positivity) (by linarith only [hm])

theorem slotPrimitive_norm (N k : ℕ) {c t : ℝ} (hc : 0≤c) (ht : c<t)
    {z : ℂ} (hz : z≠0) (hsep : 2*(k : ℝ)≤‖z‖*(t-c)) :
    ‖slotPrimitive N k c z t‖ ≤
      (2/‖z‖)*exp (-z.re*t)*
        (((N+1).choose k : ℝ)*c^(N+1-k)*(t-c)^k/(N.factorial : ℝ)) := by
  let A := (((N+1).choose k : ℂ)*(c : ℂ)^(N+1-k)*(k.factorial : ℂ)/(N.factorial : ℂ))
  have hA : ‖A‖=((N+1).choose k : ℝ)*c^(N+1-k)*(k.factorial : ℝ)/(N.factorial : ℝ) := by
    have he : A=((((N+1).choose k : ℝ)*c^(N+1-k)*(k.factorial : ℝ)/(N.factorial : ℝ) : ℝ) : ℂ) := by
      dsimp [A]; push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have he := dampedPrimitive_norm k hz (by linarith : 0<t-c) hsep
  have hb := mul_le_mul_of_nonneg_left he
    (norm_nonneg (A*Complex.exp (-z*c)))
  change ‖A*Complex.exp (-z*c)*dampedPrimitive k z (t-c)‖≤_
  rw [norm_mul]
  apply hb.trans_eq
  rw [norm_mul,hA,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero]
  have hx : exp (-z.re*c)*exp (-z.re*(t-c))=exp (-z.re*t) := by
    rw [← exp_add]; congr 1; ring
  have hf : (k.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  calc
    _ = (2/‖z‖)*(exp (-z.re*c)*exp (-z.re*(t-c)))*
        (((N+1).choose k : ℝ)*c^(N+1-k)*(t-c)^k/(N.factorial : ℝ))*
          ((k.factorial : ℝ)/(k.factorial : ℝ)) := by ring
    _ = _ := by rw [hx,div_self hf,mul_one]

/-- The joined primitive is norm-bounded ONLY at an exterior endpoint.
The bound retains the entire original factorial allocation. -/
theorem ownerPrimitive_norm (N : ℕ) {c t : ℝ} (hc : 0≤c) (ht : c<t)
    {z : ℂ} (hz : z≠0) (hsep : 2*((N : ℝ)+1)≤‖z‖*(t-c)) :
    ‖ownerPrimitive N c z t‖ ≤
      (4/‖z‖)*exp (-z.re*t)*t^(N+1)/(N.factorial : ℝ) := by
  have ht0 : 0<t := hc.trans_lt ht
  have hnz : 0<‖z‖ := norm_pos_iff.mpr hz
  have hs0 : 2*((N+1 : ℕ) : ℝ)≤‖z‖*t := by
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith [mul_nonneg (norm_nonneg z) hc]
  have hfull := mul_le_mul_of_nonneg_left (dampedPrimitive_norm (N+1) hz ht0 hs0)
    (show 0≤(N : ℝ)+1 by positivity)
  have hf : (N.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero N
  have hn : (N : ℝ)+1≠0 := by positivity
  have hfull : ‖((N : ℂ)+1)*dampedPrimitive (N+1) z t‖ ≤
      (2/‖z‖)*exp (-z.re*t)*t^(N+1)/(N.factorial : ℝ) := by
    rw [norm_mul]
    have he : ‖(N : ℂ)+1‖=(N : ℝ)+1 := by
      rw [← Complex.ofReal_natCast,← Complex.ofReal_one,← Complex.ofReal_add,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    rw [he]
    apply hfull.trans_eq
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    field_simp
  have hslots : ‖∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      slotPrimitive N k c z t‖ ≤
      (2/‖z‖)*exp (-z.re*t)*t^(N+1)/(N.factorial : ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
          (2/‖z‖)*exp (-z.re*t)*
            (((N+1).choose k : ℝ)*c^(N+1-k)*(t-c)^k/(N.factorial : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        apply slotPrimitive_norm N k hc ht hz
        have h := unpaid_le hk
        have h' : (k : ℝ)≤(N : ℝ)+1 := by exact_mod_cast h
        linarith only [hsep,h']
      _ = ((2/‖z‖)*exp (-z.re*t)/(N.factorial : ℝ))*
          (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
            ((N+1).choose k : ℝ)*c^(N+1-k)*(t-c)^k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ ≤ ((2/‖z‖)*exp (-z.re*t)/(N.factorial : ℝ))*t^(N+1) :=
        mul_le_mul_of_nonneg_left (allocated_monomials_le N hc ht) (by positivity)
      _ = _ := by ring
  exact ((norm_sub_le _ _).trans (add_le_add hfull hslots)).trans_eq (by ring)

/-- This is a signed bound for the WHOLE interval, with only TWO endpoint
costs. It is not a positive norm integral of the source-carrying interior. -/
theorem ownerPhase_interval_norm (N : ℕ) {c a b : ℝ} (hc : 0≤c) (ha : c<a) (hb : c<b)
    {z : ℂ} (hz : z≠0) (hre : z.re=1/2)
    (hsa : 2*((N : ℝ)+1)≤‖z‖*(a-c)) (hsb : 2*((N : ℝ)+1)≤‖z‖*(b-c)) :
    ‖∫ t : ℝ in a..b, ownerPhase N c z t‖ ≤
      (4/‖z‖)*(radial N a+radial N b) := by
  rw [ownerPhase_integral N c hz]
  have h := (norm_sub_le _ _).trans
    (add_le_add (ownerPrimitive_norm N hc ha hz hsa) (ownerPrimitive_norm N hc hb hz hsb))
  rw [hre] at h
  exact h.trans_eq (by unfold radial; ring)

/-- The full original complex product phase. -/
def phaseDamping (y : ℝ) : ℂ := (1/2 : ℂ)-Complex.I*y

theorem phaseDamping_re (y : ℝ) : (phaseDamping y).re=1/2 := by simp [phaseDamping]

theorem phaseDamping_norm {y : ℝ} (hy : 54≤|y|) : 54≤‖phaseDamping y‖ := by
  have h : |y|≤‖phaseDamping y‖ := by
    simpa [phaseDamping,abs_neg] using Complex.abs_im_le_norm (phaseDamping y)
  exact hy.trans h

private theorem core_endpoint_separation {N : ℕ} (hN : 1≤N)
    {c a : ℝ} (hc : c≤(4/3 : ℝ)*N) (ha : 39/20≤a)
    {y : ℝ} (hy : 54≤|y|) :
    c<a*N ∧ 2*((N : ℝ)+1)≤‖phaseDamping y‖*(a*N-c) := by
  have hn : (1 : ℝ)≤N := by exact_mod_cast hN
  have hT := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg (α := ℝ) N)
  have hv : (37/60 : ℝ)*N≤a*N-c := by linarith only [hc,hT]
  have hpos : 0<a*N-c := by linarith only [hv,hn]
  have hz := mul_le_mul_of_nonneg_right (phaseDamping_norm hy) hpos.le
  exact ⟨by linarith only [hpos],by nlinarith only [hn,hv,hz]⟩

/-- A geometric bound for the complete SIGNED owner phase sum in log
space, with the exact old allocation. This has no zero hypothesis.
Discrete arithmetic-mask transport is a separate theorem. -/
theorem normalized_ownerPhase_core_bound {N : ℕ} (hN : 1≤N) {c u y : ℝ}
    (hc : 0≤c) (hcN : c≤(4/3 : ℝ)*N) (hy : 54≤|y|) (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*∫ t : ℝ in (39/20 : ℝ)*N..(203/100 : ℝ)*N,
      ownerPhase N c (phaseDamping y) t‖ ≤
      (2/27 : ℝ)*((N : ℝ)+1)*u*(199/50)*exp (-(N : ℝ)/200000) := by
  have hz54 := phaseDamping_norm hy
  have hz : phaseDamping y≠0 := norm_pos_iff.mp (by linarith only [hz54])
  have ha := core_endpoint_separation hN hcN (by norm_num : (39/20 : ℝ)≤39/20) hy
  have hb := core_endpoint_separation hN hcN (by norm_num : (39/20 : ℝ)≤203/100) hy
  have hi := ownerPhase_interval_norm N hc ha.1 hb.1 hz (phaseDamping_re y) ha.2 hb.2
  obtain ⟨hlo,hhi⟩ := normalized_core_endpoint_radial hu hU N
  have hd : 4/‖phaseDamping y‖≤(2/27 : ℝ) := by
    exact (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤4)
      (by norm_num : (0 : ℝ)<54) hz54).trans_eq (by norm_num)
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
  calc
    _ ≤ u^(N+1)*((4/‖phaseDamping y‖)*
        (radial N ((39/20 : ℝ)*N)+radial N ((203/100 : ℝ)*N))) :=
      mul_le_mul_of_nonneg_left hi (pow_nonneg hu _)
    _ = (4/‖phaseDamping y‖)*(u^(N+1)*radial N ((39/20 : ℝ)*N)+
        u^(N+1)*radial N ((203/100 : ℝ)*N)) := by ring
    _ ≤ (4/‖phaseDamping y‖)*
        (((N : ℝ)+1)*(u*(39/20))*exp (-(N : ℝ)/200000)+
          ((N : ℝ)+1)*(u*(203/100))*exp (-(N : ℝ)/200000)) :=
      mul_le_mul_of_nonneg_left (add_le_add hlo hhi) (by positivity)
    _ ≤ (2/27 : ℝ)*
        (((N : ℝ)+1)*(u*(39/20))*exp (-(N : ℝ)/200000)+
          ((N : ℝ)+1)*(u*(203/100))*exp (-(N : ℝ)/200000)) :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    _ = _ := by ring

theorem ownerPhase_core_budget_tendsto (u : ℝ) :
    Tendsto (fun N : ℕ => (2/27 : ℝ)*((N : ℝ)+1)*u*(199/50)*
      exp (-(N : ℝ)/200000)) atTop (𝓝 0) := by
  have h0 : 0<exp (-(1/200000 : ℝ)) := exp_pos _
  have h1 : exp (-(1/200000 : ℝ))<1 := exp_lt_one_iff.mpr (by norm_num)
  have h := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 h0 h1).const_mul
    ((2/27 : ℝ)*u*(199/50))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [← exp_nat_mul]
  ring

end RiemannGaussian.ZetaRieszOwnerPhasePrimitive

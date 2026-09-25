/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointShift

/-!
# Signed cancellation at a share seam

The share integral is performed before the radial estimate. Adjacent
intervals cancel their common endpoint exactly, even when that endpoint
is exponentially resonant. The remaining endpoint estimates keep the
literal finite radial window. These are modal integral theorems; no
identification with a finite arithmetic prime packet is asserted.
-/

namespace RiemannGaussian.ZetaRieszJointShare
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical
open ZetaRieszWideOwnerAudit

/-- An exact endpoint primitive for the oscillatory radial polynomial. -/
def radialPrimitive (a : ℂ) : ℕ → ℝ → ℂ
  | 0, T => Complex.exp (-a*T)/a
  | n+1, T => ((T : ℂ)^(n+1)*Complex.exp (-a*T)+(n+1)*radialPrimitive a n T)/a

theorem radialPrimitive_deriv {a : ℂ} (ha : a ≠ 0) (n : ℕ) (T : ℝ) :
    HasDerivAt (radialPrimitive a n) (-((T : ℂ)^n*Complex.exp (-a*T))) T := by
  have hd := (((Complex.ofRealCLM.hasDerivAt (x := T)).const_mul (-a)).cexp)
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at hd
  induction n with
  | zero =>
      change HasDerivAt (fun x : ℝ => Complex.exp (-a*x)/a) _ T
      apply (hd.div_const a).congr_deriv
      simp only [pow_zero, one_mul]
      field_simp
  | succ n ih =>
      have hp := (Complex.ofRealCLM.hasDerivAt (x := T)).pow (n+1)
      have hh := ((hp.mul hd).add (ih.const_mul ((n+1 : ℕ) : ℂ))).div_const a
      simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Complex.ofRealCLM_apply,
        Complex.ofReal_one, mul_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hh
      change HasDerivAt (fun x : ℝ =>
        ((x : ℂ)^(n+1)*Complex.exp (-a*x)+(n+1)*radialPrimitive a n x)/a) _ T
      apply hh.congr_deriv
      field_simp
      ring

/-- No growing-order integration-by-parts constant is lost: the exact
primitive costs at most three times the endpoint amplitude. -/
theorem radialPrimitive_bound {a : ℂ} (ha : 1 ≤ ‖a‖) (n : ℕ) {T : ℝ}
    (hT : 0 < T) (hn : (3/2 : ℝ)*n ≤ T) :
    ‖radialPrimitive a n T‖ ≤ 3*T^n*Real.exp (-a.re*T) := by
  induction n with
  | zero =>
      simp only [radialPrimitive, norm_div, Complex.norm_exp, Complex.mul_re,
        Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, pow_zero, mul_one]
      calc
        _ ≤ Real.exp (-a.re*T) := (div_le_self (Real.exp_pos _).le ha)
        _ ≤ _ := by nlinarith [Real.exp_pos (-a.re*T)]
  | succ n ih =>
      have hn' : (3/2 : ℝ)*n ≤ T := by push_cast at hn; linarith
      have hc : 3*((n : ℝ)+1) ≤ 2*T := by push_cast at hn; linarith
      have hp : ‖(T : ℂ)^(n+1)*Complex.exp (-a*T)‖ =
          T^(n+1)*Real.exp (-a.re*T) := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hT.le,
          Complex.norm_exp]
        simp
      rw [radialPrimitive, norm_div]
      apply (div_le_self (norm_nonneg _) ha).trans
      apply (norm_add_le _ _).trans
      rw [hp, norm_mul, show ‖(n+1 : ℂ)‖ = (n : ℝ)+1 by norm_cast]
      calc
        _ ≤ T^(n+1)*Real.exp (-a.re*T)+((n : ℝ)+1)*(3*T^n*Real.exp (-a.re*T)) := by
          gcongr
          exact ih hn'
        _ = (T+3*((n : ℝ)+1))*(T^n*Real.exp (-a.re*T)) := by rw [pow_succ]; ring
        _ ≤ (3*T)*(T^n*Real.exp (-a.re*T)) := by gcongr; linarith
        _ = _ := by rw [pow_succ]; ring

theorem radial_integral_endpoints {a : ℂ} (ha : a ≠ 0) (n : ℕ) (lo hi : ℝ) :
    (∫ T : ℝ in lo..hi, (T : ℂ)^n*Complex.exp (-a*T)) =
      radialPrimitive a n lo-radialPrimitive a n hi := by
  have hc : Continuous (fun T : ℝ => (T : ℂ)^n*Complex.exp (-a*T)) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun T _ => (radialPrimitive_deriv ha n T).neg)
    (by simpa using hc.intervalIntegrable lo hi)
  simpa [sub_eq_add_neg, add_comm] using hh

/-- The share antiderivative keeps the two endpoints with opposite signs. -/
theorem share_integral {B : ℂ} (hB : B ≠ 0) {T : ℝ} (hT : T ≠ 0)
    (b : ℂ) (left right : ℝ) :
    (∫ q : ℝ in left..right, Complex.exp ((b+(q : ℂ)*B)*T)) =
      (Complex.exp ((b+(right : ℂ)*B)*T)-Complex.exp ((b+(left : ℂ)*B)*T))/(B*T) := by
  have ht : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  have hd (q : ℝ) : HasDerivAt
      (fun x : ℝ => Complex.exp ((b+(x : ℂ)*B)*T)/(B*T))
      (Complex.exp ((b+(q : ℂ)*B)*T)) q := by
    have hh := (((((Complex.ofRealCLM.hasDerivAt (x := q)).mul_const B).const_add b).mul_const
      (T : ℂ)).cexp).div_const (B*T)
    convert! hh using 1
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]
    field_simp
  have hc : Continuous (fun q : ℝ => Complex.exp ((b+(q : ℂ)*B)*T)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun q _ => hd q)
    (hc.intervalIntegrable left right)]
  ring

/-- This identity removes an internal resonant edge before any norm. -/
theorem share_seam (B b : ℂ) (T left seam right : ℝ) :
    (∫ q : ℝ in left..seam, Complex.exp ((b+(q : ℂ)*B)*T))+
      (∫ q : ℝ in seam..right, Complex.exp ((b+(q : ℂ)*B)*T)) =
        ∫ q : ℝ in left..right, Complex.exp ((b+(q : ℂ)*B)*T) := by
  have hc : Continuous (fun q : ℝ => Complex.exp ((b+(q : ℂ)*B)*T)) := by fun_prop
  exact intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable left seam)
    (hc.intervalIntegrable seam right)

/-- The actual two radial endpoints have strict source-scale savings. -/
def windowRate (x : ℝ) : ℝ := radiusCeiling*x*Real.exp (1-x/2)

theorem windowRate_bounds :
    (0 ≤ windowRate (39/20) ∧ windowRate (39/20) < 1) ∧
      (0 ≤ windowRate (203/100) ∧ windowRate (203/100) < 1) := by
  have hrate {x : ℝ} (hx : 0 < x)
      (hh : Real.log (2*radiusCeiling) < LogarithmicDeviation.deviationCost x) :
      0 ≤ windowRate x ∧ windowRate x < 1 := by
    constructor
    · unfold windowRate radiusCeiling; positivity
    · have he := LogarithmicDeviation.log_rate_eq_deviation
        (by norm_num [radiusCeiling] : 0 < radiusCeiling) hx
      have hneg : Real.log (radiusCeiling*x)+(1-x/2) < 0 := by linarith
      have h := Real.exp_lt_one_iff.mpr hneg
      rwa [Real.exp_add, Real.exp_log (by unfold radiusCeiling; positivity)] at h
  exact ⟨hrate (by norm_num) ZetaRieszParityPacket.core_window_costs.1,
    hrate (by norm_num) ZetaRieszParityPacket.core_window_costs.2⟩

theorem factorial_endpoint (N : ℕ) {u x : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ radiusCeiling) (hx : 0 ≤ x) :
    u^(N+1)/(N.factorial : ℝ)*(x*N)^N*Real.exp (-(x*N)/2) ≤
      radiusCeiling*(windowRate x)^N := by
  have hn := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have he : Real.exp (N : ℝ)*Real.exp (-(x*N)/2) = (Real.exp (1-x/2))^N := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ = u^(N+1)*x^N*((N : ℝ)^N/(N.factorial : ℝ))*Real.exp (-(x*N)/2) := by
      rw [mul_pow]; ring
    _ ≤ radiusCeiling^(N+1)*x^N*Real.exp (N : ℝ)*Real.exp (-(x*N)/2) := by
      gcongr
      unfold radiusCeiling
      positivity
    _ = _ := by rw [mul_assoc, he, windowRate, mul_pow, mul_pow, pow_succ]; ring

/-- A signed finite-window radial moment. Its phase is never replaced
by the integral of its absolute value. -/
def windowMoment (u : ℝ) (N n : ℕ) (a : ℂ) : ℂ :=
  (u : ℂ)^(N+1)/(N.factorial : ℂ)*
    ∫ T : ℝ in (39/20 : ℝ)*N..(203/100 : ℝ)*N,
      (T : ℂ)^n*Complex.exp (-a*T)

/-- A nonresonant endpoint gives a geometric bound on the ORIGINAL
finite radial window; neither its saddle nor its cutoff is frozen. -/
theorem windowMoment_bound {a : ℂ} (ha : 1 ≤ ‖a‖) (hre : 1/2 ≤ a.re)
    (N n : ℕ) (hn : n ≤ N) {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) :
    ‖windowMoment u N n a‖ ≤
      3*radiusCeiling*((windowRate (39/20))^N+(windowRate (203/100))^N) := by
  by_cases hN : N = 0
  · subst N
    simp only [windowMoment, Nat.cast_zero, mul_zero, intervalIntegral.integral_same,
      mul_zero, norm_zero]
    unfold radiusCeiling
    positivity
  have hNp : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
  have han : a ≠ 0 := norm_pos_iff.mp (by linarith)
  have hend {x : ℝ} (hx : 3/2 ≤ x) :
      ‖radialPrimitive a n (x*N)‖ ≤ 3*(x*N)^N*Real.exp (-(x*N)/2) := by
    have hT : 0 < x*N := by positivity
    have hT1 : 1 ≤ x*N := by nlinarith
    have hpn : (3/2 : ℝ)*n ≤ x*N := by nlinarith
    apply (radialPrimitive_bound ha n hT hpn).trans
    gcongr
    nlinarith
  rw [windowMoment, norm_mul, norm_div, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hu, Complex.norm_natCast, radial_integral_endpoints han]
  apply (mul_le_mul_of_nonneg_left
    ((norm_sub_le _ _).trans (add_le_add (hend (by norm_num : (3/2 : ℝ) ≤ 39/20))
      (hend (by norm_num : (3/2 : ℝ) ≤ 203/100)))) (by positivity)).trans
  have hlo := factorial_endpoint N hu hU (by norm_num : (0 : ℝ) ≤ 39/20)
  have hhi := factorial_endpoint N hu hU (by norm_num : (0 : ℝ) ≤ 203/100)
  nlinarith

/-- Coupled share/radial integral, with the moving cutoff left as L.
Multiplication by any fixed modal residue is harmless, but an arithmetic
identification and additional nonconstant masks still need proof. -/
def jointModal (u : ℝ) (N : ℕ) (b B z : ℂ) (L left right : ℝ) : ℂ :=
  (u : ℂ)^(N+1)/(N.factorial : ℂ)*
    ∫ T : ℝ in (39/20 : ℝ)*N..(203/100 : ℝ)*N,
      (T : ℂ)^N*Complex.exp (-(T : ℂ)/2)*Complex.exp (z*L)*
        ∫ q : ℝ in left..right, Complex.exp ((b+(q : ℂ)*B)*T)

theorem jointModal_endpoints {B : ℂ} (hB : B ≠ 0) (u : ℝ) (N : ℕ)
    (b z : ℂ) (L left right : ℝ) :
    jointModal u N b B z L left right = Complex.exp (z*L)/B*
      (windowMoment u N (N-1) (1/2-b-right*B)-
        windowMoment u N (N-1) (1/2-b-left*B)) := by
  by_cases hN : N = 0
  · subst N
    simp [jointModal, windowMoment]
  have hNp : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have hid : ∀ T ∈ uIcc ((39/20 : ℝ)*N) ((203/100 : ℝ)*N),
      (T : ℂ)^N*Complex.exp (-(T : ℂ)/2)*Complex.exp (z*L)*
        (∫ q : ℝ in left..right, Complex.exp ((b+(q : ℂ)*B)*T)) =
      Complex.exp (z*L)/B*((T : ℂ)^(N-1)*Complex.exp (-(1/2-b-right*B)*T)-
        (T : ℂ)^(N-1)*Complex.exp (-(1/2-b-left*B)*T)) := by
    intro T hT
    rw [uIcc_of_le (by nlinarith)] at hT
    have ht : 0 < T := by nlinarith [hT.1]
    have htc : (T : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hp : (T : ℂ)^N = (T : ℂ)^(N-1)*(T : ℂ) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ N)]
    have he (q : ℝ) : Complex.exp (-(T : ℂ)/2)*Complex.exp ((b+(q : ℂ)*B)*T) =
        Complex.exp (-(1/2-b-q*B)*T) := by rw [← Complex.exp_add]; congr 1; ring
    rw [share_integral hB ht.ne', hp, ← he right, ← he left]
    field_simp
  rw [jointModal, intervalIntegral.integral_congr hid, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub]
  · simp only [windowMoment]
    ring
  · exact (by fun_prop : Continuous (fun T : ℝ =>
      (T : ℂ)^(N-1)*Complex.exp (-(1/2-b-right*B)*T))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun T : ℝ =>
      (T : ℂ)^(N-1)*Complex.exp (-(1/2-b-left*B)*T))).intervalIntegrable _ _

/-- No nonresonance assumption is imposed at the shared internal edge. -/
theorem jointModal_seam {B : ℂ} (hB : B ≠ 0) (u : ℝ) (N : ℕ)
    (b z : ℂ) (L left seam right : ℝ) :
    jointModal u N b B z L left seam+jointModal u N b B z L seam right =
      jointModal u N b B z L left right := by
  simp only [jointModal_endpoints hB]
  ring

/-- A genuine signed geometric estimate after adjacent pieces are joined.
The internal boundary may have norm smaller than the source radius. -/
theorem jointModal_bound {u L left right : ℝ} {b B z : ℂ}
    (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (hL : 0 ≤ L) (hz : z.re ≤ 0)
    (hB : B ≠ 0)
    (hl : 1 ≤ ‖1/2-b-left*B‖) (hr : 1 ≤ ‖1/2-b-right*B‖)
    (hlr : 1/2 ≤ (1/2-b-left*B).re) (hrr : 1/2 ≤ (1/2-b-right*B).re) (N : ℕ) :
    ‖jointModal u N b B z L left right‖ ≤
      (6*radiusCeiling/‖B‖)*((windowRate (39/20))^N+(windowRate (203/100))^N) := by
  have he : ‖Complex.exp (z*L)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simpa using mul_nonpos_of_nonpos_of_nonneg hz hL
  rw [jointModal_endpoints hB, norm_mul, norm_div]
  have hh := (norm_sub_le _ _).trans (add_le_add
    (windowMoment_bound hr hrr N (N-1) (Nat.sub_le _ _) hu hU)
    (windowMoment_bound hl hlr N (N-1) (Nat.sub_le _ _) hu hU))
  calc
    _ ≤ (1/‖B‖)*(3*radiusCeiling*((windowRate (39/20))^N+(windowRate (203/100))^N)+
        3*radiusCeiling*((windowRate (39/20))^N+(windowRate (203/100))^N)) := by
      gcongr
    _ = _ := by ring

theorem jointModal_tendsto {u left right : ℝ} {b B z : ℂ}
    (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (L : ℕ → ℝ) (hL : ∀ N, 0 ≤ L N)
    (hz : z.re ≤ 0) (hB : B ≠ 0)
    (hl : 1 ≤ ‖1/2-b-left*B‖) (hr : 1 ≤ ‖1/2-b-right*B‖)
    (hlr : 1/2 ≤ (1/2-b-left*B).re) (hrr : 1/2 ≤ (1/2-b-right*B).re) :
    Tendsto (fun N => jointModal u N b B z (L N) left right) atTop (𝓝 0) := by
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one windowRate_bounds.1.1
    windowRate_bounds.1.2).add (tendsto_pow_atTop_nhds_zero_of_lt_one
      windowRate_bounds.2.1 windowRate_bounds.2.2)).const_mul (6*radiusCeiling/‖B‖)
  simp only [add_zero, mul_zero] at h
  exact squeeze_zero_norm (fun N => jointModal_bound hu hU (hL N) hz hB hl hr hlr hrr N) h

/-- The resonance found numerically sits exactly at the old lower edge. -/
def modelBase (y : ℝ) : ℂ := -Complex.I*y
/-- The exact difference of the two synthetic modal ordinates. -/
def modelSlope (y : ℝ) : ℂ := Complex.I*((80/43 : ℝ)*y)

theorem model_endpoint_geometry (y : ℝ) :
    1/2-modelBase y-(43/80 : ℂ)*modelSlope y = 1/2 ∧
      1/2-modelBase y-(21/40 : ℂ)*modelSlope y = 1/2+Complex.I*(y/43) ∧
      1/2-modelBase y-(9/16 : ℂ)*modelSlope y = 1/2-Complex.I*(2*y/43) := by
  unfold modelBase modelSlope
  push_cast
  constructor
  · ring
  constructor <;> ring

/-- The enlarged joint interval's exterior endpoints have a fixed
frequency gap, although its internal seam is resonant. -/
theorem model_outer_gaps {y : ℝ} (hy : 54 < |y|) :
    1 ≤ ‖1/2-modelBase y-(21/40 : ℂ)*modelSlope y‖ ∧
      1 ≤ ‖1/2-modelBase y-(9/16 : ℂ)*modelSlope y‖ := by
  obtain ⟨_, hl, hr⟩ := model_endpoint_geometry y
  rw [hl, hr]
  have hlo := Complex.abs_im_le_norm (1/2+Complex.I*((y/43 : ℝ) : ℂ))
  have hhi := Complex.abs_im_le_norm (1/2-Complex.I*((2*y/43 : ℝ) : ℂ))
  norm_num [abs_div, abs_mul] at hlo hhi
  constructor <;> linarith

/-- The separately projected seam has positive source exponent. This
is an exact exponent check, not a claim about actual zeta zero locations. -/
theorem model_seam_exponent_pos :
    (3/100000 : ℝ) < Real.log (2*radiusCeiling)+Real.log radiusCeiling/10000 := by
  have hlog := Real.one_sub_inv_le_log_of_pos
    (by norm_num [radiusCeiling] : 0 < 2*radiusCeiling)
  have hex := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7/10) 5
  norm_num [Finset.sum_range_succ] at hex
  have htwo : Real.log 2 < (7/10 : ℝ) :=
    (Real.log_lt_iff_lt_exp (by norm_num)).mpr (by linarith)
  have he : Real.log (2*radiusCeiling) = Real.log 2+Real.log radiusCeiling :=
    Real.log_mul (by norm_num) (by norm_num [radiusCeiling])
  norm_num [radiusCeiling] at hlog
  norm_num [radiusCeiling] at he ⊢
  linarith

/-- Quantitative bypass of the seam counterexample, with the exact
moving radial cutoff permitted. This does not assert prime transport. -/
theorem model_joint_tendsto {y : ℝ} (hy : 54 < |y|) {z : ℂ} (hz : z.re ≤ 0)
    (L : ℕ → ℝ) (hL : ∀ N, 0 ≤ L N) :
    Tendsto (fun N => jointModal radiusCeiling N (modelBase y) (modelSlope y) z
      (L N) (21/40) (43/80)+jointModal radiusCeiling N (modelBase y) (modelSlope y) z
        (L N) (43/80) (9/16)) atTop (𝓝 0) := by
  have hB : modelSlope y ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [modelSlope] at hi
    have hy0 : y = 0 := by linarith
    norm_num [hy0] at hy
  simp_rw [jointModal_seam hB]
  apply jointModal_tendsto (by norm_num [radiusCeiling]) le_rfl L hL hz hB
  · convert (model_outer_gaps hy).1 using 1; norm_num
  · convert (model_outer_gaps hy).2 using 1; norm_num
  · simp [modelBase, modelSlope]
  · simp [modelBase, modelSlope]

/-- The exterior frequency condition must be checked, not inferred
from widening a box: a synthetic pair can resonate at any nonzero edge. -/
theorem retuned_edge_resonance (y : ℝ) {q : ℝ} (hq : q ≠ 0) :
    (1/2 : ℂ)-modelBase y-(q : ℂ)*(Complex.I*(y/q : ℝ)) = 1/2 := by
  unfold modelBase
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  push_cast
  field_simp
  ring

/-- Arbitrary common literal weights partition exactly at the same seam.
An estimate still needs the weighted arithmetic-to-mode bridge. -/
theorem finite_weighted_seam {ι : Type*} (S : Finset ι) (q : ι → ℝ) (W : ι → ℂ)
    {left seam right : ℝ} (hls : left ≤ seam) (hsr : seam ≤ right) :
    (∑ i ∈ S.filter (fun i => left < q i ∧ q i ≤ seam), W i)+
      (∑ i ∈ S.filter (fun i => seam < q i ∧ q i ≤ right), W i) =
        ∑ i ∈ S.filter (fun i => left < q i ∧ q i ≤ right), W i := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> grind

end
end RiemannGaussian.ZetaRieszJointShare

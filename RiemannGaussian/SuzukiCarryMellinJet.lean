/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryDeterminantGate
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual Mellin jets of the alternating carry profile

The coefficients come from the unchanged tent and its literal jump indices.
No source nonvanishing or signed prime-sum estimate is assumed here.
-/

namespace RiemannGaussian.SuzukiCarryMellinJet
noncomputable section
open Complex MeasureTheory Set Filter
open SuzukiCarryMellinLimit SuzukiCarryMellinRate SuzukiCarryDeterminantGate
open scoped BigOperators Topology ComplexConjugate

/-- A clamp used only to prove a uniform variation estimate. -/
def clamp (v : ℝ) : ℝ := min 3 (max 0 v)

theorem clamp_bounds (v : ℝ) : 0 ≤ clamp v ∧ clamp v ≤ 3 := by
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

theorem clamp_lipschitz (v w : ℝ) : |clamp v-clamp w| ≤ |v-w| := by
  simpa only [clamp, id_eq, Real.dist_eq, NNReal.coe_one, one_mul] using
    (((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_max 0).const_min 3).dist_le_mul v w

/-- Exact real power moment of the finite alternating jump profile. -/
def moment (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (jumpCount x),
    (-1 : ℝ)^k*tent (((k+1 : ℕ) : ℝ)*x/2)*((((k+1 : ℕ) : ℝ)*x/2)^n)

private theorem tent_clamp_pow (n : ℕ) (v : ℝ) :
    tent v*(clamp v)^n = tent v*v^n := by
  by_cases hlo : v ≤ 1
  · simp [tent_eq_zero_of_le hlo]
  by_cases hhi : 3 ≤ v
  · simp [tent_eq_zero_of_ge hhi]
  rw [clamp, max_eq_right (by linarith : 0 ≤ v), min_eq_right (le_of_not_ge hhi)]

private theorem weighted_tent_lipschitz (n : ℕ) (v w : ℝ) :
    |tent v*(clamp v)^n-tent w*(clamp w)^n| ≤
      ((3 : ℝ)^n+n*3^(n-1)) * |v-w| := by
  have hv := clamp_bounds v
  have hw := clamp_bounds w
  have hp : |clamp v^n-clamp w^n| ≤ |v-w| * n*3^(n-1) := by
    apply (abs_pow_sub_pow_le _ _ n).trans
    rw [abs_of_nonneg hv.1, abs_of_nonneg hw.1]
    calc
      _ ≤ |v-w| * n * max (clamp v) (clamp w)^(n-1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (clamp_lipschitz v w) (by positivity))
          (pow_nonneg (hv.1.trans (le_max_left _ _)) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hv.1.trans (le_max_left _ _)) (max_le hv.2 hw.2) _)
        (by positivity)
  have he : tent v*clamp v^n-tent w*clamp w^n =
      (tent v-tent w)*clamp v^n+tent w*(clamp v^n-clamp w^n) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hv.1 _),
    abs_of_nonneg (tent_nonneg w)]
  calc
    _ ≤ |v-w| * 3^n+1*(|v-w| * n*3^(n-1)) := by
      exact add_le_add
        (mul_le_mul (tent_lipschitz v w) (pow_le_pow_left₀ hv.1 hv.2 _)
          (pow_nonneg hv.1 _) (abs_nonneg _))
        (mul_le_mul (tent_le_one w) hp (abs_nonneg _) (by norm_num))
    _ = _ := by ring

/-- Abel summation controls the joined alternating chain without a count factor. -/
theorem alternating_chain_bound {K : ℕ} (g : ℝ → ℂ) (v : ℕ → ℝ)
    {C : ℝ} (hl : ∀ a b, ‖g a-g b‖ ≤ C * |a-b|)
    (hm : Monotone v) (hend : g (v (K-1)) = 0) :
    ‖∑ k ∈ Finset.range K, (-1 : ℂ)^k*g (v k)‖ ≤ C*(v (K-1)-v 0) := by
  have he := Finset.sum_range_by_parts (fun k => g (v k)) (fun k => (-1 : ℂ)^k) K
  simp only [smul_eq_mul, hend, zero_mul, zero_sub] at he
  have hp (n : ℕ) : ‖∑ i ∈ Finset.range n, (-1 : ℂ)^i‖ ≤ 1 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => (-1 : ℂ)^k) n, Fin.sum_neg_one_pow]
    split_ifs <;> norm_num
  have hf : (∑ k ∈ Finset.range K, (-1 : ℂ)^k*g (v k)) =
      -(∑ k ∈ Finset.range (K-1), (g (v (k+1))-g (v k))*
        ∑ i ∈ Finset.range (k+1), (-1 : ℂ)^i) := by
    rw [← he]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hf, norm_neg]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ Finset.range (K-1), C*(v (k+1)-v k) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      have hk := hl (v (k+1)) (v k)
      rw [abs_of_nonneg (sub_nonneg.mpr (hm (by omega)))] at hk
      exact (mul_le_mul_of_nonneg_left (hp (k+1)) (norm_nonneg _)).trans
        (by simpa only [mul_one] using hk)
    _ = C*(v (K-1)-v 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]

/-- Uniform control of every exact jump moment, including as x tends to zero. -/
theorem moment_abs_le (n : ℕ) {x : ℝ} (hx : 0 < x) :
    |moment n x| ≤ 3*((3 : ℝ)^n+n*3^(n-1)) := by
  let v : ℕ → ℝ := fun k => ((k+1 : ℕ) : ℝ)*x/2
  let g : ℝ → ℂ := fun t => (tent t*clamp t^n : ℝ)
  have hj : 0 < jumpCount x := Nat.ceil_pos.mpr (by positivity)
  have hlast : 3 ≤ v (jumpCount x-1) := by
    dsimp [v]
    rw [Nat.sub_add_cancel hj]
    have hc := mul_le_mul_of_nonneg_right (Nat.le_ceil (6/x)) hx.le
    rw [div_mul_cancel₀ _ hx.ne'] at hc
    change (6 : ℝ) ≤ (jumpCount x : ℝ)*x at hc
    linarith
  have hspan : v (jumpCount x-1)-v 0 ≤ 3 := by
    dsimp [v]
    rw [Nat.sub_add_cancel hj]
    have hc := mul_lt_mul_of_pos_right
      (Nat.ceil_lt_add_one (show 0 ≤ 6/x by positivity)) hx
    rw [add_mul, div_mul_cancel₀ _ hx.ne', one_mul] at hc
    change (jumpCount x : ℝ)*x < 6+x at hc
    simp only [Nat.cast_one]
    linarith
  have hm : Monotone v := by intro a b hab; dsimp [v]; gcongr
  have hl (a b : ℝ) : ‖g a-g b‖ ≤ ((3 : ℝ)^n+n*3^(n-1)) * |a-b| := by
    simpa only [g, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
      weighted_tent_lipschitz n a b
  have hend : g (v (jumpCount x-1)) = 0 := by simp [g, tent_eq_zero_of_ge hlast]
  have he : (∑ k ∈ Finset.range (jumpCount x), (-1 : ℂ)^k*g (v k)) =
      (moment n x : ℂ) := by
    simp only [moment, g, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [v]
    rw [tent_clamp_pow]
    push_cast
    ring
  have hb := alternating_chain_bound g v hl hm hend
  rw [he, Complex.norm_real, Real.norm_eq_abs] at hb
  apply hb.trans
  have hC : 0 ≤ (3 : ℝ)^n+n*3^(n-1) := by positivity
  nlinarith

/-- The exact fourth-degree exponential polynomial. -/
def expJet (z : ℂ) : ℂ := 1+z+z^2/2+z^3/6+z^4/24

theorem expJet_eq_sum (z : ℂ) :
    expJet z = ∑ n ∈ Finset.range 5, z^n/(n.factorial : ℂ) := by
  simp [expJet, Finset.sum_range_succ]
  ring

/-- The pointwise exponential remainder; factorial jump summation is still exact. -/
def expRemainder (tau v : ℝ) : ℂ := Complex.exp (I*tau*v)-expJet (I*tau*v)

private theorem hasDerivAt_expRemainder (tau v : ℝ) :
    HasDerivAt (expRemainder tau)
      (I*tau*(Complex.exp (I*tau*v)-(1+I*tau*v+(I*tau*v)^2/2+(I*tau*v)^3/6))) v := by
  have hz := ((hasDerivAt_id v).ofReal_comp).const_mul (I*(tau : ℂ))
  have hj := (((((hasDerivAt_const v (1 : ℂ)).add hz).add
    ((hz.pow 2).div_const 2)).add ((hz.pow 3).div_const 6)).add ((hz.pow 4).div_const 24))
  convert! hz.cexp.sub hj using 1
  try dsimp [expRemainder, expJet]
  norm_num
  ring

private theorem norm_I_tau_v (tau v : ℝ) : ‖I*tau*v‖ = |tau| * |v| := by
  simp [Complex.norm_real, Real.norm_eq_abs]

theorem expRemainder_bound (tau : ℝ) {v : ℝ} (hv : v ∈ Icc 0 3) :
    ‖expRemainder tau v‖ ≤ 243*Real.exp (3*|tau|)*|tau|^5 := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (I*tau*v) 5
  rw [← expJet_eq_sum, ← expRemainder, norm_I_tau_v,
    abs_of_nonneg hv.1] at h
  apply h.trans
  calc
    (|tau| * v)^5*Real.exp (|tau| * v) ≤
        (|tau| * 3)^5*Real.exp (|tau| * 3) := by
      gcongr <;> first | exact mul_nonneg (abs_nonneg tau) hv.1 | exact hv.2
    _ = _ := by ring_nf

theorem expRemainder_deriv_bound (tau : ℝ) {v : ℝ} (hv : v ∈ Icc 0 3) :
    ‖deriv (expRemainder tau) v‖ ≤ 81*Real.exp (3*|tau|)*|tau|^5 := by
  rw [(hasDerivAt_expRemainder tau v).deriv, norm_mul]
  have he : (1+I*tau*v+(I*tau*v)^2/2+(I*tau*v)^3/6) =
      ∑ n ∈ Finset.range 4, (I*tau*v)^n/(n.factorial : ℂ) := by
    simp [Finset.sum_range_succ]
    ring
  rw [he]
  apply (mul_le_mul_of_nonneg_left
    (Complex.norm_exp_sub_sum_le_norm_mul_exp (I*tau*v) 4) (norm_nonneg _)).trans
  rw [norm_I_tau_v, abs_of_nonneg hv.1]
  simp only [norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  calc
    |tau| * ((|tau| * v)^4*Real.exp (|tau| * v)) ≤
        |tau| * ((|tau| * 3)^4*Real.exp (|tau| * 3)) := by
      gcongr <;> first | exact mul_nonneg (abs_nonneg tau) hv.1 | exact hv.2
    _ = _ := by ring_nf

private theorem clamped_remainder_lipschitz (tau a b : ℝ) :
    ‖expRemainder tau (clamp a)-expRemainder tau (clamp b)‖ ≤
      (81*Real.exp (3*|tau|)*|tau|^5) * |a-b| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun v (_ : v ∈ Icc (0 : ℝ) 3) => (hasDerivAt_expRemainder tau v).differentiableAt)
    (fun v hv => expRemainder_deriv_bound tau hv) (convex_Icc 0 3)
    (clamp_bounds b) (clamp_bounds a)
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (clamp_lipschitz a b) (by positivity))

private theorem weighted_remainder_lipschitz (tau a b : ℝ) :
    ‖(tent a : ℂ)*expRemainder tau (clamp a)-
      (tent b : ℂ)*expRemainder tau (clamp b)‖ ≤
      (324*Real.exp (3*|tau|)*|tau|^5) * |a-b| := by
  have he : (tent a : ℂ)*expRemainder tau (clamp a)-
      (tent b : ℂ)*expRemainder tau (clamp b) =
      ((tent a-tent b : ℝ) : ℂ)*expRemainder tau (clamp a)+
        (tent b : ℂ)*(expRemainder tau (clamp a)-expRemainder tau (clamp b)) := by
    push_cast
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (tent_nonneg b)]
  calc
    _ ≤ |a-b| * (243*Real.exp (3*|tau|)*|tau|^5)+
        1*((81*Real.exp (3*|tau|)*|tau|^5) * |a-b|) :=
      add_le_add (mul_le_mul (tent_lipschitz a b)
        (expRemainder_bound tau (clamp_bounds a)) (norm_nonneg _) (abs_nonneg _))
        (mul_le_mul (tent_le_one b) (clamped_remainder_lipschitz tau a b)
          (norm_nonneg _) (by norm_num))
    _ = _ := by ring

private theorem jump_chain_bound (g : ℝ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hl : ∀ a b, ‖g a-g b‖ ≤ C * |a-b|) (hz : ∀ v, 3 ≤ v → g v = 0)
    {x : ℝ} (hx : 0 < x) :
    ‖∑ k ∈ Finset.range (jumpCount x), (-1 : ℂ)^k*g (((k+1 : ℕ) : ℝ)*x/2)‖ ≤ 3*C := by
  let v : ℕ → ℝ := fun k => ((k+1 : ℕ) : ℝ)*x/2
  have hj : 0 < jumpCount x := Nat.ceil_pos.mpr (by positivity)
  have hlast : 3 ≤ v (jumpCount x-1) := by
    dsimp [v]
    rw [Nat.sub_add_cancel hj]
    have hc := mul_le_mul_of_nonneg_right (Nat.le_ceil (6/x)) hx.le
    rw [div_mul_cancel₀ _ hx.ne'] at hc
    change (6 : ℝ) ≤ (jumpCount x : ℝ)*x at hc
    linarith
  have hspan : v (jumpCount x-1)-v 0 ≤ 3 := by
    dsimp [v]
    rw [Nat.sub_add_cancel hj]
    have hc := mul_lt_mul_of_pos_right
      (Nat.ceil_lt_add_one (show 0 ≤ 6/x by positivity)) hx
    rw [add_mul, div_mul_cancel₀ _ hx.ne', one_mul] at hc
    change (jumpCount x : ℝ)*x < 6+x at hc
    simp only [Nat.cast_one]
    linarith
  have hm : Monotone v := by intro a b hab; dsimp [v]; gcongr
  exact (alternating_chain_bound g v hl hm (hz _ hlast)).trans (by nlinarith)

/-- The exact finite fourth-degree profile, with the same jump indices. -/
def profileJet (tau x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (jumpCount x), (-1 : ℂ)^k*
    (tent (((k+1 : ℕ) : ℝ)*x/2) : ℂ)*expJet (I*tau*(((k+1 : ℕ) : ℝ)*x/2))

/-- No 1/x count loss occurs in the actual Taylor remainder. -/
theorem profile_sub_jet_bound (tau : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖profile tau x-profileJet tau x‖ ≤ 972*Real.exp (3*|tau|)*|tau|^5 := by
  let g : ℝ → ℂ := fun v => (tent v : ℂ)*expRemainder tau (clamp v)
  have hg (v : ℝ) : g v = (tent v : ℂ)*expRemainder tau v := by
    by_cases hlo : v ≤ 1
    · simp [g, tent_eq_zero_of_le hlo]
    by_cases hhi : 3 ≤ v
    · simp [g, tent_eq_zero_of_ge hhi]
    simp only [g, clamp, max_eq_right (by linarith : 0 ≤ v),
      min_eq_right (le_of_not_ge hhi)]
  have he : profile tau x-profileJet tau x =
      ∑ k ∈ Finset.range (jumpCount x), (-1 : ℂ)^k*g (((k+1 : ℕ) : ℝ)*x/2) := by
    rw [profile, profileJet, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hg]
    simp only [amplitude, expRemainder]
    push_cast
    ring
  rw [he]
  exact (jump_chain_bound g (by positivity)
    (weighted_remainder_lipschitz tau) (fun v hv => by simp [g, tent_eq_zero_of_ge hv]) hx).trans_eq
    (by ring)

theorem moment_complex (n : ℕ) (x : ℝ) :
    (moment n x : ℂ) = ∑ k ∈ Finset.range (jumpCount x),
      (-1 : ℂ)^k*(tent (((k+1 : ℕ) : ℝ)*x/2) : ℂ)*
        ((((k+1 : ℕ) : ℝ)*x/2 : ℝ) : ℂ)^n := by
  unfold moment
  push_cast
  rfl

theorem profileJet_eq_moments (tau x : ℝ) :
    profileJet tau x = (moment 0 x : ℂ)+I*tau*(moment 1 x : ℂ)-
      (tau : ℂ)^2/2*(moment 2 x : ℂ)-I*(tau : ℂ)^3/6*(moment 3 x : ℂ)+
      (tau : ℂ)^4/24*(moment 4 x : ℂ) := by
  simp only [moment_complex, Finset.mul_sum]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  unfold profileJet
  apply Finset.sum_congr rfl
  intro k _
  simp only [expJet, mul_pow, Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    pow_zero, pow_one]
  push_cast
  ring

/-- Signed quadratic and quartic densities of the literal tent profile. -/
def quadraticDensity (x : ℝ) : ℝ := moment 1 x^2-moment 0 x*moment 2 x

/-- Exact quartic modulation coefficient of the squared jump profile. -/
def quarticDensity (x : ℝ) : ℝ :=
  moment 2 x^2/4+moment 0 x*moment 4 x/12-moment 1 x*moment 3 x/3

/-- Every odd coefficient cancels algebraically, before the Mellin integral. -/
theorem profileJet_norm_sq (tau x : ℝ) :
    ‖profileJet tau x‖^2 = moment 0 x^2+quadraticDensity x*tau^2+
      quarticDensity x*tau^4+(moment 3 x^2/36-moment 2 x*moment 4 x/24)*tau^6+
        moment 4 x^2/576*tau^8 := by
  rw [profileJet_eq_moments, Complex.sq_norm, Complex.normSq_apply]
  simp [quadraticDensity, quarticDensity, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.mul_im]
  ring

/-- One explicit, deliberately unoptimized remainder constant. -/
def remainderConstant : ℝ :=
  (12+972*Real.exp 3)*(972*Real.exp 3)+2400

private theorem sixth_bound {x : ℝ} (hx : 0 < x) :
    |moment 3 x^2/36-moment 2 x*moment 4 x/24| ≤ 1800 := by
  have h2 : |moment 2 x| ≤ 45 := by have h := moment_abs_le 2 hx; norm_num at h; exact h
  have h3 : |moment 3 x| ≤ 162 := by have h := moment_abs_le 3 hx; norm_num at h; exact h
  have h4 : |moment 4 x| ≤ 567 := by have h := moment_abs_le 4 hx; norm_num at h; exact h
  calc
    _ ≤ |moment 3 x^2/36|+|moment 2 x*moment 4 x/24| := abs_sub _ _
    _ = |moment 3 x|^2/36+(|moment 2 x| * |moment 4 x|)/24 := by
      rw [abs_div, abs_div, abs_pow, abs_mul]
      norm_num
    _ ≤ (162 : ℝ)^2/36+(45*567)/24 := by gcongr
    _ ≤ 1800 := by norm_num

private theorem eighth_bound {x : ℝ} (hx : 0 < x) :
    |moment 4 x^2/576| ≤ 600 := by
  have h4 : |moment 4 x| ≤ 567 := by have h := moment_abs_le 4 hx; norm_num at h; exact h
  rw [abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 576)]
  calc
    _ ≤ (567 : ℝ)^2/576 := by gcongr
    _ ≤ 600 := by norm_num

/-- A uniform O(tau^5) remainder for the squared, joined profile. -/
theorem mass_remainder_bound {tau x : ℝ} (ht : |tau| ≤ 1) (hx : 0 < x) :
    |‖profile tau x‖^2-moment 0 x^2-quadraticDensity x*tau^2-
      quarticDensity x*tau^4| ≤ remainderConstant*|tau|^5 := by
  let G : ℝ := 972*Real.exp 3
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hp : ‖profile tau x‖ ≤ 6 := (profile_norm_le tau hx).trans (by linarith)
  have he : ‖profile tau x-profileJet tau x‖ ≤ G*|tau|^5 := by
    apply (profile_sub_jet_bound tau hx).trans
    dsimp [G]
    gcongr
    linarith
  have ht5 : |tau|^5 ≤ 1 := pow_le_one₀ (abs_nonneg _) ht
  have hj : ‖profileJet tau x‖ ≤ 6+G := by
    have h := norm_sub_le (profile tau x) (profile tau x-profileJet tau x)
    rw [sub_sub_cancel] at h
    nlinarith
  have hs : |‖profile tau x‖^2-‖profileJet tau x‖^2| ≤ (12+G)*G*|tau|^5 := by
    have hf : |‖profile tau x‖^2-‖profileJet tau x‖^2| =
        |‖profile tau x‖-‖profileJet tau x‖| * (‖profile tau x‖+‖profileJet tau x‖) := by
      rw [show ‖profile tau x‖^2-‖profileJet tau x‖^2 =
        (‖profile tau x‖-‖profileJet tau x‖)*(‖profile tau x‖+‖profileJet tau x‖) by ring,
        abs_mul, abs_of_nonneg (show 0 ≤ ‖profile tau x‖+‖profileJet tau x‖ by positivity)]
    rw [hf]
    calc
      _ ≤ (G*|tau|^5)*(12+G) :=
        mul_le_mul ((abs_norm_sub_norm_le _ _).trans he) (by linarith)
          (by positivity) (by positivity)
      _ = _ := by ring
  have ht6 : |tau|^6 ≤ |tau|^5 := pow_le_pow_of_le_one (abs_nonneg _) ht (by decide)
  have ht8 : |tau|^8 ≤ |tau|^5 := pow_le_pow_of_le_one (abs_nonneg _) ht (by decide)
  have hh : |‖profileJet tau x‖^2-moment 0 x^2-quadraticDensity x*tau^2-
      quarticDensity x*tau^4| ≤ 2400*|tau|^5 := by
    rw [profileJet_norm_sq]
    have hf : moment 0 x^2+quadraticDensity x*tau^2+quarticDensity x*tau^4+
        (moment 3 x^2/36-moment 2 x*moment 4 x/24)*tau^6+moment 4 x^2/576*tau^8-
        moment 0 x^2-quadraticDensity x*tau^2-quarticDensity x*tau^4 =
        (moment 3 x^2/36-moment 2 x*moment 4 x/24)*tau^6+moment 4 x^2/576*tau^8 := by ring
    rw [hf]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_pow, abs_pow]
    have h6 := sixth_bound hx
    have h8 := eighth_bound hx
    nlinarith [mul_le_mul h6 ht6 (by positivity : 0 ≤ |tau|^6) (by norm_num : (0 : ℝ) ≤ 1800),
      mul_le_mul h8 ht8 (by positivity : 0 ≤ |tau|^8) (by norm_num : (0 : ℝ) ≤ 600)]
  have hf : ‖profile tau x‖^2-moment 0 x^2-quadraticDensity x*tau^2-quarticDensity x*tau^4 =
      (‖profile tau x‖^2-‖profileJet tau x‖^2)+
      (‖profileJet tau x‖^2-moment 0 x^2-quadraticDensity x*tau^2-quarticDensity x*tau^4) := by ring
  rw [hf]
  exact (abs_add_le _ _).trans ((add_le_add hs hh).trans_eq (by dsimp [G, remainderConstant]; ring))

theorem measurable_moment_exp (n : ℕ) :
    Measurable (fun t : ℝ => moment n (Real.exp t)) := by
  classical
  have hj : Measurable (fun t : ℝ => jumpCount (Real.exp t)) :=
    Nat.measurable_ceil.comp (measurable_const.div Real.measurable_exp)
  have he : (fun t : ℝ => moment n (Real.exp t)) =
      (fun t : ℝ => ∑' k : ℕ, if k < jumpCount (Real.exp t) then
        (-1 : ℝ)^k*tent (((k+1 : ℕ) : ℝ)*Real.exp t/2)*
          (((k+1 : ℕ) : ℝ)*Real.exp t/2)^n else 0) := by
    funext t
    rw [tsum_eq_sum (s := Finset.range (jumpCount (Real.exp t)))
      (fun k hk => by rw [if_neg (by simpa only [Finset.mem_range] using hk)])]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [if_pos (Finset.mem_range.mp hk)]
  rw [he]
  apply Measurable.tsum
  intro k
  apply Measurable.ite (measurableSet_lt measurable_const hj) _ measurable_const
  have hv : Continuous (fun t : ℝ => ((k+1 : ℕ) : ℝ)*Real.exp t/2) := by fun_prop
  have hf : Continuous tent := by unfold tent; fun_prop
  exact ((continuous_const.mul (hf.comp hv)).mul (hv.pow n)).measurable

theorem moment_zero_above (n : ℕ) {x : ℝ} (hx : 6 ≤ x) : moment n x = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  have hk : (1 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k+1 by omega)
  have hv : 3 ≤ ((k+1 : ℕ) : ℝ)*x/2 := by nlinarith
  simp only [tent_eq_zero_of_ge hv, mul_zero, zero_mul]

theorem quadraticDensity_bound {x : ℝ} (hx : 0 < x) : |quadraticDensity x| ≤ 279 := by
  have h0 : |moment 0 x| ≤ 3 := by have h := moment_abs_le 0 hx; norm_num at h; exact h
  have h1 : |moment 1 x| ≤ 12 := by have h := moment_abs_le 1 hx; norm_num at h; exact h
  have h2 : |moment 2 x| ≤ 45 := by have h := moment_abs_le 2 hx; norm_num at h; exact h
  calc
    _ ≤ |moment 1 x^2|+|moment 0 x*moment 2 x| := abs_sub _ _
    _ = |moment 1 x|^2+|moment 0 x| * |moment 2 x| := by rw [abs_pow, abs_mul]
    _ ≤ 12^2+3*45 := by gcongr
    _ = 279 := by norm_num

theorem quarticDensity_bound {x : ℝ} (hx : 0 < x) : |quarticDensity x| ≤ 1296 := by
  have h0 : |moment 0 x| ≤ 3 := by have h := moment_abs_le 0 hx; norm_num at h; exact h
  have h1 : |moment 1 x| ≤ 12 := by have h := moment_abs_le 1 hx; norm_num at h; exact h
  have h2 : |moment 2 x| ≤ 45 := by have h := moment_abs_le 2 hx; norm_num at h; exact h
  have h3 : |moment 3 x| ≤ 162 := by have h := moment_abs_le 3 hx; norm_num at h; exact h
  have h4 : |moment 4 x| ≤ 567 := by have h := moment_abs_le 4 hx; norm_num at h; exact h
  calc
    _ ≤ |moment 2 x^2/4|+|moment 0 x*moment 4 x/12|+|moment 1 x*moment 3 x/3| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |moment 2 x|^2/4+(|moment 0 x| * |moment 4 x|)/12+
        (|moment 1 x| * |moment 3 x|)/3 := by
      rw [abs_div, abs_div, abs_div, abs_pow, abs_mul, abs_mul]
      norm_num
    _ ≤ 45^2/4+(3*567)/12+(12*162)/3 := by gcongr
    _ = 1296 := by norm_num

/-- The actual quadratic and quartic Mellin coefficients. -/
def B (s : ℂ) : ℂ := ∫ t : ℝ, Complex.exp (s*t)*(quadraticDensity (Real.exp t) : ℂ)

/-- Mellin integral of the exact quartic modulation coefficient. -/
def C (s : ℂ) : ℂ := ∫ t : ℝ, Complex.exp (s*t)*(quarticDensity (Real.exp t) : ℂ)

private theorem integrable_bounded_density {s : ℂ} (hs : 0 < s.re)
    {g : ℝ → ℝ} (hg : Measurable (fun t : ℝ => g (Real.exp t)))
    {D : ℝ} (_hD : 0 ≤ D) (hb : ∀ x, 0 < x → |g x| ≤ D)
    (hz : ∀ x, 6 ≤ x → g x = 0) :
    Integrable (fun t : ℝ => Complex.exp (s*t)*(g (Real.exp t) : ℂ)) := by
  have hm : Integrable ((Iic (Real.log 6)).indicator
      (fun t : ℝ => D*Real.exp (s.re*t))) :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      ((integrableOn_exp_mul_Iic hs (Real.log 6)).const_mul D)
  apply hm.mono' (((Complex.continuous_exp.measurable.comp
    (measurable_const.mul Complex.measurable_ofReal))).mul
      (Complex.measurable_ofReal.comp hg)).aestronglyMeasurable
  filter_upwards with t
  change ‖Complex.exp (s*t)*(g (Real.exp t) : ℂ)‖ ≤
    (Iic (Real.log 6)).indicator (fun t : ℝ => D*Real.exp (s.re*t)) t
  by_cases ht : t ≤ Real.log 6
  · rw [Set.indicator_of_mem (show t ∈ Iic (Real.log 6) from ht), norm_mul,
      Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have he : (s*(t : ℂ)).re = s.re*t := by simp [Complex.mul_re]
    rw [he]
    exact (mul_le_mul_of_nonneg_left (hb _ (Real.exp_pos t)) (Real.exp_pos _).le).trans_eq (by ring)
  · have hx : 6 ≤ Real.exp t :=
      ((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 6)).mp (lt_of_not_ge ht)).le
    rw [hz _ hx, Complex.ofReal_zero, mul_zero, norm_zero,
      Set.indicator_of_notMem (show t ∉ Iic (Real.log 6) from ht)]

theorem integrable_B {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ => Complex.exp (s*t)*(quadraticDensity (Real.exp t) : ℂ)) := by
  apply integrable_bounded_density hs
    (((measurable_moment_exp 1).pow_const 2).sub
      ((measurable_moment_exp 0).mul (measurable_moment_exp 2))) (by norm_num)
    (fun _ hx => quadraticDensity_bound hx)
  intro x hx
  simp [quadraticDensity, moment_zero_above _ hx]

theorem integrable_C {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ => Complex.exp (s*t)*(quarticDensity (Real.exp t) : ℂ)) := by
  apply integrable_bounded_density hs
    (((((measurable_moment_exp 2).pow_const 2).div_const 4).add
      (((measurable_moment_exp 0).mul (measurable_moment_exp 4)).div_const 12)).sub
      (((measurable_moment_exp 1).mul (measurable_moment_exp 3)).div_const 3)) (by norm_num)
    (fun _ hx => quarticDensity_bound hx)
  intro x hx
  simp [quarticDensity, moment_zero_above _ hx]

theorem profile_zero_eq_moment (x : ℝ) : profile 0 x = (moment 0 x : ℂ) := by
  rw [moment_complex]
  simp [profile, amplitude]

private def normalizedRemainder (s : ℂ) (tau t : ℝ) : ℂ :=
  (Complex.exp (s*t)*(‖profile tau (Real.exp t)‖^2 : ℝ)-
    Complex.exp (s*t)*(‖profile 0 (Real.exp t)‖^2 : ℝ)-
    Complex.exp (s*t)*(quadraticDensity (Real.exp t) : ℂ)*(tau : ℂ)^2-
    Complex.exp (s*t)*(quarticDensity (Real.exp t) : ℂ)*(tau : ℂ)^4)/(tau : ℂ)^4

private theorem normalizedRemainder_eq (s : ℂ) (tau t : ℝ) :
    normalizedRemainder s tau t = Complex.exp (s*t)*
      ((‖profile tau (Real.exp t)‖^2-moment 0 (Real.exp t)^2-
        quadraticDensity (Real.exp t)*tau^2-quarticDensity (Real.exp t)*tau^4 : ℝ) : ℂ)/
          (tau : ℂ)^4 := by
  rw [normalizedRemainder, profile_zero_eq_moment, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]
  push_cast
  ring

private theorem integrable_normalizedRemainder {s : ℂ} (hs : 0 < s.re) (tau : ℝ) :
    Integrable (normalizedRemainder s tau) :=
  ((((integrable_continuumResponse hs tau).sub (integrable_continuumResponse hs 0)).sub
    ((integrable_B hs).mul_const ((tau : ℂ)^2))).sub
    ((integrable_C hs).mul_const ((tau : ℂ)^4))).div_const ((tau : ℂ)^4)

private theorem integral_normalizedRemainder {s : ℂ} (hs : 0 < s.re) (tau : ℝ) :
    (∫ t : ℝ, normalizedRemainder s tau t) =
      jetRemainder (continuumResponse s) (B s) (C s) tau := by
  simp only [normalizedRemainder]
  rw [integral_div]
  have h1 := integral_sub (integrable_continuumResponse hs tau) (integrable_continuumResponse hs 0)
  have h2 := integral_sub ((integrable_continuumResponse hs tau).sub (integrable_continuumResponse hs 0))
    ((integrable_B hs).mul_const ((tau : ℂ)^2))
  have h3 := integral_sub (((integrable_continuumResponse hs tau).sub
    (integrable_continuumResponse hs 0)).sub ((integrable_B hs).mul_const ((tau : ℂ)^2)))
    ((integrable_C hs).mul_const ((tau : ℂ)^4))
  simp only [Pi.sub_apply] at h2 h3
  rw [h2, h1, integral_mul_const, integral_mul_const] at h3
  convert! congrArg (fun z : ℂ => z/(tau : ℂ)^4) h3 using 1

private theorem normalizedRemainder_bound (s : ℂ) {tau : ℝ} (ht : tau ≠ 0)
    (ht1 : |tau| ≤ 1) (t : ℝ) :
    ‖normalizedRemainder s tau t‖ ≤ remainderConstant*Real.exp (s.re*t)*|tau| := by
  rw [normalizedRemainder_eq]
  simp only [norm_div, norm_mul, Complex.norm_exp, Complex.norm_real,
    Real.norm_eq_abs, norm_pow]
  have hre : (s*(t : ℂ)).re = s.re*t := by simp [Complex.mul_re]
  rw [hre]
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mass_remainder_bound ht1 (Real.exp_pos t))
      (Real.exp_pos _).le) (by positivity)).trans_eq
  field_simp [abs_ne_zero.mpr ht]

private theorem normalizedRemainder_zero_above (s : ℂ) (tau : ℝ) {t : ℝ}
    (ht : Real.log 6 < t) : normalizedRemainder s tau t = 0 := by
  have hx : 6 ≤ Real.exp t :=
    ((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 6)).mp ht).le
  simp [normalizedRemainder_eq, profile_eq_zero_above hx, moment_zero_above _ hx,
    quadraticDensity, quarticDensity]

/-- The literal continuum response has the actual fourth-order expansion,
through all accumulating carry knots, for every positive real part. -/
theorem fourthOrderExpansion {s : ℂ} (hs : 0 < s.re) :
    FourthOrderExpansion (continuumResponse s) (B s) (C s) := by
  let l := 𝓝[>] (0 : ℝ)
  have hsmall : ∀ᶠ tau : ℝ in l, 0 < tau ∧ tau < 1 := by
    have hh : ∀ᶠ tau : ℝ in 𝓝[>] (0 : ℝ), tau < 1 :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have hp : ∀ᶠ tau : ℝ in 𝓝[>] (0 : ℝ), 0 < tau := self_mem_nhdsWithin
    exact hp.and hh
  let envelope : ℝ → ℝ := (Iic (Real.log 6)).indicator
    (fun t : ℝ => remainderConstant*Real.exp (s.re*t))
  have hE : Integrable envelope :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      ((integrableOn_exp_mul_Iic hs (Real.log 6)).const_mul remainderConstant)
  have hm : ∀ᶠ tau : ℝ in l, AEStronglyMeasurable (normalizedRemainder s tau) :=
    .of_forall (fun tau => (integrable_normalizedRemainder hs tau).aestronglyMeasurable)
  have hb : ∀ᶠ tau : ℝ in l, ∀ᵐ t : ℝ, ‖normalizedRemainder s tau t‖ ≤ envelope t := by
    filter_upwards [hsmall] with tau htau
    filter_upwards with t
    dsimp only [envelope]
    by_cases ht : t ≤ Real.log 6
    · rw [Set.indicator_of_mem (show t ∈ Iic (Real.log 6) from ht)]
      have hta : |tau| ≤ 1 := by rw [abs_of_pos htau.1]; exact htau.2.le
      exact (normalizedRemainder_bound s htau.1.ne' hta t).trans
        (by have hC : 0 ≤ remainderConstant*Real.exp (s.re*t) := by unfold remainderConstant; positivity
            nlinarith)
    · rw [normalizedRemainder_zero_above s tau (lt_of_not_ge ht), norm_zero,
        Set.indicator_of_notMem (show t ∉ Iic (Real.log 6) from ht)]
  have hl : ∀ᵐ t : ℝ, Tendsto (fun tau : ℝ => normalizedRemainder s tau t) l (𝓝 (0 : ℂ)) := by
    filter_upwards with t
    have hta : Tendsto (fun tau : ℝ => |tau|) l (𝓝 0) := by
      have hid : Tendsto (fun tau : ℝ => tau) l (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [abs_zero] using hid.abs
    have hlim : Tendsto (fun tau : ℝ => remainderConstant*Real.exp (s.re*t)*|tau|) l (𝓝 0) :=
      by simpa only [mul_zero] using hta.const_mul (remainderConstant*Real.exp (s.re*t))
    apply squeeze_zero_norm' ?_ hlim
    filter_upwards [hsmall] with tau htau
    exact normalizedRemainder_bound s htau.1.ne'
      (by rw [abs_of_pos htau.1]; exact htau.2.le) t
  have hi := tendsto_integral_filter_of_dominated_convergence envelope hm hb hE hl
  simp only [integral_zero] at hi
  exact hi.congr' (.of_forall (integral_normalizedRemainder hs))

/-- Only the explicit analytic wedge remains in the source gate. -/
theorem exists_fixed_code_of_wedge {p s : ℂ} (hp : 0 < p.re) (hs : 0 < s.re)
    (hw : B p*C s-C p*B s ≠ 0) :
    ∃ tau : ℝ, 0 < tau ∧ continuumDet p s tau ≠ 0 ∧
      ∀ᶠ H : ℕ in atTop,
        (‖continuumDet p s tau‖/2)*Real.exp ((p.re+s.re)*Real.log H) ≤
          ‖nativeDet H p s tau‖ :=
  exists_fixed_code_source_lower hp hs (fourthOrderExpansion hp) (fourthOrderExpansion hs) hw

/-- Changing the three finite modulation ratios cannot repair a degenerate
quadratic/quartic wedge at that order. This is an exact algebraic test,
not a claim about the uncomputed higher jets of the full response. -/
theorem asymmetric_quartic_determinant (A B C a b c : ℂ) (v w tau : ℝ) :
    ((evenJet A B C (v*tau)-evenJet A B C 0)*
      (evenJet a b c (w*tau)-evenJet a b c 0)-
      (evenJet A B C (w*tau)-evenJet A B C 0)*
      (evenJet a b c (v*tau)-evenJet a b c 0)) =
        (v : ℂ)^2*(w : ℂ)^2*((w : ℂ)^2-(v : ℂ)^2)*(B*c-C*b)*(tau : ℂ)^6 := by
  simp only [evenJet, Complex.ofReal_mul, Complex.ofReal_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    mul_zero, add_zero]
  ring

theorem asymmetric_quartic_loss_of_wedge_zero (A B C a b c : ℂ)
    (hw : B*c-C*b = 0) (v w tau : ℝ) :
    ((evenJet A B C (v*tau)-evenJet A B C 0)*
      (evenJet a b c (w*tau)-evenJet a b c 0)-
      (evenJet A B C (w*tau)-evenJet A B C 0)*
      (evenJet a b c (v*tau)-evenJet a b c 0)) = 0 := by
  rw [asymmetric_quartic_determinant, hw, mul_zero, zero_mul]

/-- If the fourth-order wedge is lost, a sixth-order jet would test a new
minor. This identity does not assume that the actual sixth-order expansion
has been established, and earns no arithmetic/source bound by itself. -/
theorem sixth_jet_determinant (A B C D a b c d : ℂ) (tau : ℝ) :
    contrastDet (fun t => evenJet A B C t+D*(t : ℂ)^6)
      (fun t => evenJet a b c t+d*(t : ℂ)^6) tau =
        12*(B*c-C*b)*(tau : ℂ)^6+
          60*(B*d-D*b)*(tau : ℂ)^8+48*(C*d-D*c)*(tau : ℂ)^10 := by
  simp only [contrastDet, evenJet, Complex.ofReal_zero, Complex.ofReal_mul,
    Complex.ofReal_ofNat, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (4 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0),
    mul_zero, add_zero]
  ring

end
end RiemannGaussian.SuzukiCarryMellinJet

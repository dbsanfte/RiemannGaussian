/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityMaskedPhaseAudit
import RiemannGaussian.ZetaMoebiusPoleJetFilter

/-!
# Actual zero denominators and hard-share half-plane stability

Rightmost is an explicit temporary hypothesis, not a consequence of RH
failure. These results control zero modes and a two-node masked integral.
They do not remove a pole from a masked arithmetic carrier or estimate its
analytic residual. Filtering the total moment is a separate operation.
-/

namespace RiemannGaussian.ZetaRieszHalfPlaneModes
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators Classical ComplexConjugate
set_option backward.isDefEq.respectTransparency false

/-- The horizontal source radius at the safe evaluation line. -/
def sourceRadius (rho : NontrivialZetaZero) : ℝ := 3/2-rho.1.re

/-- The temporary global hypothesis; no maximizing zero is constructed. -/
def Rightmost (rho : NontrivialZetaZero) : Prop :=
  ∀ tau : NontrivialZetaZero, tau.1.re ≤ rho.1.re

/-- The direct denominator at the selected zero's actual ordinate. -/
def direct (rho tau : NontrivialZetaZero) : ℂ :=
  (3/2+Complex.I*(rho.1.im : ℂ))-tau.1

/-- The denominator of the canonical reflected mode. -/
def reflected (R : ℝ) (z : ℂ) : ℂ := (R^2 : ℝ)/conj z

theorem sourceRadius_pos (rho : NontrivialZetaZero) : 0 < sourceRadius rho := by
  dsimp [sourceRadius]
  linarith [NontrivialZetaZero.re_lt_one rho]

theorem direct_self (rho : NontrivialZetaZero) :
    direct rho rho = (sourceRadius rho : ℂ) := by
  apply Complex.ext <;> simp [direct, sourceRadius]

theorem direct_re (rho tau : NontrivialZetaZero) :
    (direct rho tau).re = 3/2-tau.1.re := by simp [direct]

theorem direct_re_ge_of_rightmost {rho : NontrivialZetaZero} (h : Rightmost rho)
    (tau : NontrivialZetaZero) : sourceRadius rho ≤ (direct rho tau).re := by
  rw [direct_re]
  dsimp [sourceRadius]
  linarith [h tau]

theorem reflected_re (R : ℝ) (z : ℂ) :
    (reflected R z).re = R^2*z.re/‖z‖^2 := by
  simp [reflected, Complex.div_re, Complex.normSq_eq_norm_sq, pow_two,
    Complex.mul_re, Complex.mul_im]

/-- Reflection pushes a positive-real-part denominator strictly right,
provided the original zero really lies inside the canonical circle. -/
theorem reflected_re_gt {R : ℝ} {z : ℂ} (hz : 0 < z.re) (hR : ‖z‖ < R) :
    z.re < (reflected R z).re := by
  have hn : 0 < ‖z‖ := hz.trans_le (Complex.re_le_norm z)
  have hs : ‖z‖^2 < R^2 := by nlinarith
  rw [reflected_re, lt_div_iff₀ (sq_pos_of_pos hn)]
  nlinarith

theorem reflected_direct_re_gt_of_rightmost {rho : NontrivialZetaZero}
    (h : Rightmost rho) (tau : NontrivialZetaZero) {R : ℝ}
    (hR : ‖direct rho tau‖ < R) :
    sourceRadius rho ≤ (direct rho tau).re ∧
      (direct rho tau).re < (reflected R (direct rho tau)).re := by
  have hd := direct_re_ge_of_rightmost h tau
  exact ⟨hd, reflected_re_gt ((sourceRadius_pos rho).trans_le hd) hR⟩

/-- Every point of the canonical support is the negative direct
denominator of an actual nontrivial zeta zero. -/
theorem local_support_actual_zero (rho : NontrivialZetaZero)
    (r : Set.Ico (3/4 : ℝ) 1) {i : ℂ}
    (hi : i ∈ adaptiveZetaZeroSupport r rho.1.im) :
    ∃ tau : NontrivialZetaZero, direct rho tau = -i := by
  have hdiv := (mem_adaptiveZetaZeroSupport r rho.1.im i).mp hi
  have hmem := (MeromorphicOn.divisor (localZetaPoleRemoved rho.1.im)
    (Metric.ball 0 (adaptiveZetaCanonicalRadius r rho.1.im))).supportWithinDomain hdiv
  have hin : ‖i‖ < 1 := by
    have hh : ‖i‖ < adaptiveZetaCanonicalRadius r rho.1.im := by
      simpa only [Metric.mem_ball, dist_zero_right] using hmem
    exact hh.trans (adaptiveZetaCanonicalRadius_spec r rho.1.im).2.1
  have hspos : 0 < (3/2+Complex.I*(rho.1.im : ℂ)+i).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_self, add_zero]
    norm_num
    linarith [(abs_le.mp (Complex.abs_re_le_norm i)).1]
  let tau : NontrivialZetaZero := ⟨3/2+Complex.I*(rho.1.im : ℂ)+i,
    isNontrivialZetaZero_of_poleRemoved_eq_zero hspos
      (adaptiveZetaPoleRemoved_eq_zero_of_divisor_ne_zero r rho.1.im hdiv)⟩
  refine ⟨tau, ?_⟩
  change (3/2+Complex.I*(rho.1.im : ℂ))-(3/2+Complex.I*(rho.1.im : ℂ)+i) = -i
  ring

/-- The rightmost hypothesis applies to every actual local divisor
denominator, not just a separately supplied list of model modes. -/
theorem local_direct_re_ge_of_rightmost {rho : NontrivialZetaZero} (h : Rightmost rho)
    (r : Set.Ico (3/4 : ℝ) 1) {i : ℂ}
    (hi : i ∈ adaptiveZetaZeroSupport r rho.1.im) : sourceRadius rho ≤ (-i).re := by
  obtain ⟨tau, ht⟩ := local_support_actual_zero rho r hi
  rw [← ht]
  exact direct_re_ge_of_rightmost h tau

/-- Nonnegative normalized shares preserve the closed right half-plane. -/
theorem convex_re_ge {ι : Type*} (S : Finset ι) (q : ι → ℝ) (z : ι → ℂ)
    {u : ℝ} (hq : ∀ j ∈ S, 0 ≤ q j) (hs : ∑ j ∈ S, q j = 1)
    (hz : ∀ j ∈ S, u ≤ (z j).re) :
    u ≤ (∑ j ∈ S, (q j : ℂ)*z j).re := by
  have hh := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hz j hj) (hq j hj))
  rw [← Finset.sum_mul, hs, one_mul] at hh
  simpa using hh

theorem convex_norm_ge {ι : Type*} (S : Finset ι) (q : ι → ℝ) (z : ι → ℂ)
    {u : ℝ} (hq : ∀ j ∈ S, 0 ≤ q j) (hs : ∑ j ∈ S, q j = 1)
    (hz : ∀ j ∈ S, u ≤ (z j).re) :
    u ≤ ‖∑ j ∈ S, (q j : ℂ)*z j‖ :=
  (convex_re_ge S q z hq hs hz).trans (Complex.re_le_norm _)

/-- Actual direct and admissible reflected zero modes can resonate
inside the source disk only if at least one actual zero is to the right.
This asserts no quantitative ordinate bound or successor chain. -/
theorem resonance_forces_rightward {ι : Type*} (S : Finset ι) (q : ι → ℝ)
    (tau : ι → NontrivialZetaZero) (flip : ι → Bool) (R : ℝ)
    (rho : NontrivialZetaZero)
    (hq : ∀ j ∈ S, 0 ≤ q j) (hs : ∑ j ∈ S, q j = 1)
    (hR : ∀ j ∈ S, flip j = true → ‖direct rho (tau j)‖ < R)
    (hres : ‖∑ j ∈ S, (q j : ℂ)*
      (if flip j then reflected R (direct rho (tau j)) else direct rho (tau j))‖ <
        sourceRadius rho) :
    ∃ j ∈ S, rho.1.re < (tau j).1.re := by
  by_contra! hn
  apply (not_lt_of_ge (convex_norm_ge S q
    (fun j => if flip j then reflected R (direct rho (tau j)) else direct rho (tau j)) hq hs ?_)) hres
  intro j hj
  have hd : sourceRadius rho ≤ (direct rho (tau j)).re := by
    rw [direct_re]
    dsimp [sourceRadius]
    linarith [hn j hj]
  split_ifs with hb
  · exact hd.trans (reflected_re_gt ((sourceRadius_pos rho).trans_le hd) (hR j hj hb)).le
  · exact hd

/-- A resonance of depth greater than ε forces a participating actual
zero with horizontal gain greater than ε. It gives no ordinate control:
different rightward modes can cancel their ordinate offsets. -/
theorem resonance_depth_forces_rightward {ι : Type*} (S : Finset ι) (q : ι → ℝ)
    (tau : ι → NontrivialZetaZero) (flip : ι → Bool) (R : ℝ)
    (rho : NontrivialZetaZero) (ε : ℝ)
    (hq : ∀ j ∈ S, 0 ≤ q j) (hs : ∑ j ∈ S, q j = 1)
    (hR : ∀ j ∈ S, flip j = true → ‖direct rho (tau j)‖ < R)
    (hres : ‖∑ j ∈ S, (q j : ℂ)*
      (if flip j then reflected R (direct rho (tau j)) else direct rho (tau j))‖ <
        sourceRadius rho-ε) :
    ∃ j ∈ S, rho.1.re+ε < (tau j).1.re := by
  by_contra! hn
  apply (not_lt_of_ge (convex_norm_ge S q
    (fun j => if flip j then reflected R (direct rho (tau j)) else direct rho (tau j)) hq hs ?_)) hres
  intro j hj
  have hd : sourceRadius rho-ε ≤ (direct rho (tau j)).re := by
    rw [direct_re]
    dsimp [sourceRadius]
    linarith [hn j hj]
  have hp : 0 < (direct rho (tau j)).re := by
    rw [direct_re]
    linarith [NontrivialZetaZero.re_lt_one (tau j)]
  split_ifs with hb
  · exact hd.trans (reflected_re_gt hp (hR j hj hb)).le
  · exact hd

/-- The affine two-mode denominator, before the hard share projection. -/
def mix (z₁ z₂ : ℂ) (q : ℝ) : ℂ := (q : ℂ)*z₁+(1-(q : ℂ))*z₂

theorem mix_affine (z₁ z₂ : ℂ) (q : ℝ) :
    mix z₁ z₂ q = z₂+(z₁-z₂)*(q : ℂ) := by unfold mix; ring

theorem mix_re_ge {u q : ℝ} {z₁ z₂ : ℂ}
    (h₁ : u ≤ z₁.re) (h₂ : u ≤ z₂.re) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    u ≤ (mix z₁ z₂ q).re := by
  simp only [mix, Complex.add_re, Complex.mul_re, Complex.sub_re,
    Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
    Complex.one_im, zero_mul, sub_zero]
  nlinarith

theorem mix_ne_zero {u q : ℝ} {z₁ z₂ : ℂ} (hu : 0 < u)
    (h₁ : u ≤ z₁.re) (h₂ : u ≤ z₂.re) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    mix z₁ z₂ q ≠ 0 := by
  intro hz
  have hh := mix_re_ge h₁ h₂ hq0 hq1
  rw [hz, Complex.zero_re] at hh
  linarith

/-- A genuine hard-share two-node integral, retaining its complex sign. -/
def twoBand (u : ℝ) (z₁ z₂ : ℂ) (a b : ℝ) (N : ℕ) : ℂ :=
  ∫ q : ℝ in a..b, ((u : ℂ)/mix z₁ z₂ q)^(N+2)

/-- Exact divided-difference formula on a segment of the half-plane.
No individual prime-leg limit is used. -/
theorem twoBand_eq {u a b : ℝ} {z₁ z₂ : ℂ} (hu : 0 < u)
    (h₁ : u ≤ z₁.re) (h₂ : u ≤ z₂.re)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hne : z₁ ≠ z₂) (N : ℕ) :
    twoBand u z₁ z₂ a b N = (u : ℂ)/((z₁-z₂)*(N+1))*
      (((u : ℂ)/mix z₁ z₂ a)^(N+1)-((u : ℂ)/mix z₁ z₂ b)^(N+1)) := by
  have hd (q : ℝ) : HasDerivAt (mix z₁ z₂) (z₁-z₂) q := by
    have hh := ((hasDerivAt_id q).ofReal_comp.const_mul (z₁-z₂)).const_add z₂
    simp only [id_eq, Complex.ofReal_one, mul_one] at hh
    simpa only [← mix_affine] using hh
  have hs : z₁-z₂ ≠ 0 := sub_ne_zero.mpr hne
  have hn : (N+1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  have deriv (q : ℝ) (hq : q ∈ Icc a b) : HasDerivAt
      (fun x : ℝ => -(u : ℂ)/((z₁-z₂)*(N+1))*((u : ℂ)/mix z₁ z₂ x)^(N+1))
      (((u : ℂ)/mix z₁ z₂ q)^(N+2)) q := by
    have hz := mix_ne_zero hu h₁ h₂ (ha.trans hq.1) (hq.2.trans hb)
    have hh := (((hasDerivAt_const q (u : ℂ)).div (hd q) hz).pow (N+1)).const_mul
      (-(u : ℂ)/((z₁-z₂)*(N+1)))
    apply hh.congr_deriv
    push_cast
    simp only [Pi.div_apply]
    rw [div_pow, div_pow, pow_succ, pow_succ]
    field_simp
    ring
  have hc : ContinuousOn (fun q : ℝ => ((u : ℂ)/mix z₁ z₂ q)^(N+2)) (Icc a b) := by
    apply ContinuousOn.pow
    apply ContinuousOn.div continuousOn_const
    · exact (continuous_iff_continuousAt.mpr (fun q => (hd q).continuousAt)).continuousOn
    · intro q hq
      exact mix_ne_zero hu h₁ h₂ (ha.trans hq.1) (hq.2.trans hb)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun q hq => deriv q (by simpa [uIcc_of_le hab] using hq))
    (hc.intervalIntegrable_of_Icc hab)
  change twoBand u z₁ z₂ a b N = _ at hh
  rw [hh]
  ring

/-- A uniform quantitative mixed-node saving, prior to projection onto
a real channel. Coincident nodes are handled separately below. -/
theorem twoBand_bound {u a b : ℝ} {z₁ z₂ : ℂ} (hu : 0 < u)
    (h₁ : u ≤ z₁.re) (h₂ : u ≤ z₂.re)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hne : z₁ ≠ z₂) (N : ℕ) :
    ‖twoBand u z₁ z₂ a b N‖ ≤ 2*u/(‖z₁-z₂‖*(N+1)) := by
  have bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
      ‖((u : ℂ)/mix z₁ z₂ q)^(N+1)‖ ≤ 1 := by
    rw [norm_pow]
    apply pow_le_one₀ (norm_nonneg _)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hu.le]
    have hz : u ≤ ‖mix z₁ z₂ q‖ := (mix_re_ge h₁ h₂ hq0 hq1).trans (Complex.re_le_norm _)
    exact (div_le_one (hu.trans_le hz)).mpr hz
  rw [twoBand_eq hu h₁ h₂ ha hab hb hne, norm_mul, norm_div, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hu.le]
  have hN : ‖(N+1 : ℂ)‖ = (N+1 : ℝ) := by
    norm_cast
  rw [hN]
  have hh := (norm_sub_le (((u : ℂ)/mix z₁ z₂ a)^(N+1))
    (((u : ℂ)/mix z₁ z₂ b)^(N+1))).trans
      (add_le_add (bound a ha (hab.trans hb)) (bound b (ha.trans hab) hb))
  calc
    _ ≤ (u/(‖z₁-z₂‖*(N+1)))*2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- The exact confluent formula. At `z=u` this is the pure selected
mode and has no mixed-node saving. -/
theorem twoBand_coincident (u a b : ℝ) (z : ℂ) (N : ℕ) :
    twoBand u z z a b N = ((b-a : ℝ) : ℂ)*((u : ℂ)/z)^(N+2) := by
  have hq (q : ℝ) : mix z z q = z := by unfold mix; ring
  simp_rw [twoBand, hq]
  rw [intervalIntegral.integral_const, Complex.real_smul]

/-- The quantitative hard-share bound gives decay of every distinct
two-node assignment in the half-plane. -/
theorem twoBand_tendsto {u a b : ℝ} {z₁ z₂ : ℂ} (hu : 0 < u)
    (h₁ : u ≤ z₁.re) (h₂ : u ≤ z₂.re)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hne : z₁ ≠ z₂) :
    Tendsto (twoBand u z₁ z₂ a b) atTop (𝓝 0) := by
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*u/‖z₁-z₂‖)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (fun N => ?_) ht
  convert twoBand_bound hu h₁ h₂ ha hab hb hne N using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- In the closed half-plane, a repeated node can have source-radius
norm only when it is precisely the real selected node. -/
theorem norm_gt_of_half_plane_ne_source {u : ℝ} {z : ℂ} (_hu : 0 < u)
    (hz : u ≤ z.re) (hne : z ≠ (u : ℂ)) : u < ‖z‖ := by
  by_contra! h
  have hre : z.re = u := le_antisymm ((Complex.re_le_norm z).trans h) hz
  have hnorm : ‖z‖ = u := le_antisymm h (hz.trans (Complex.re_le_norm z))
  have hsq := Complex.sq_norm_sub_sq_im z
  rw [hre, hnorm] at hsq
  have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
  exact hne (Complex.ext hre (by simpa using him))

theorem twoBand_coincident_tendsto {u : ℝ} (a b : ℝ) {z : ℂ} (hu : 0 < u)
    (hz : u ≤ z.re) (hne : z ≠ (u : ℂ)) :
    Tendsto (twoBand u z z a b) atTop (𝓝 0) := by
  have hnorm : ‖(u : ℂ)/z‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hu.le]
    have hh := norm_gt_of_half_plane_ne_source hu hz hne
    exact (div_lt_one (hu.trans hh)).mpr hh
  have ht := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm).comp
    (tendsto_add_atTop_nat 2)).const_mul ((b-a : ℝ) : ℂ)
  change Tendsto (fun N => twoBand u z z a b N) atTop (𝓝 0)
  simpa only [twoBand_coincident, Function.comp_def, mul_zero] using ht

end
end RiemannGaussian.ZetaRieszHalfPlaneModes

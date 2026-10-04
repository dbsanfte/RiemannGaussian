/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingMomentIsolation
import RiemannGaussian.ZetaRieszCeilingDensityAudit
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum

/-!
# Exact integer-mode audit of the multi-order ceiling strategy

This is a SYNTHETIC local divisor, not a family of actual zeta zeros or a
prime array. All singular residues are negative integers. The selected
residue is -2. Its translated roots-of-unity cloud retains an exact
algebraic cancellation across moment orders. A regular correction is
included explicitly, including orders zero and one.

The complete-arithmetic moment majorant and local analytic-radius data
alone must not be upgraded to the actual joinedPhysical ceiling.
-/

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingClusterPowerAudit

/-- A translated unit-circle mode. -/
def node (u : ℝ) (ζ : ℂ) (i : ℕ) : ℂ := (u : ℂ)+(1-u)*ζ^i

/-- The whole negative-integer singular contribution, at logged power k. -/
def singularPower (M : ℕ) (u : ℝ) (ζ : ℂ) (k : ℕ) : ℂ :=
  -2*∑ i ∈ Finset.range M, (node u ζ i)^k

/-- The complete explicit regular correction. It is not a deletion of
low factorial orders and is not asserted to be the actual zeta remainder. -/
def regularPower (M : ℕ) (u : ℝ) (k : ℕ) : ℂ := 2*(M : ℂ)*(u : ℂ)^k

/-- The exact model array, retaining the correction at every order. -/
def modelArray (M : ℕ) (u : ℝ) (ζ : ℂ) (n : ℕ) : ℂ :=
  singularPower M u ζ (n+1)+regularPower M u (n+1)

/-- Character orthogonality before any norm or separate incidence price. -/
theorem sum_root_powers {M k : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ M)
    (hk : 0 < k) (hkM : k < M) :
    (∑ i ∈ Finset.range M, (ζ^i)^k) = 0 := by
  have hne := hζ.pow_ne_one_of_pos_of_lt hk.ne' hkM
  simp_rw [←pow_mul, Nat.mul_comm _ k, pow_mul]
  rw [geom_sum_eq hne]
  have hp : (ζ^k)^M = 1 := by
    rw [←pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [hp, sub_self, zero_div]

/-- Exact translated root cancellation through ALL powers below M. -/
theorem sum_node_powers {M k : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ M)
    (hkM : k < M) (u : ℝ) :
    (∑ i ∈ Finset.range M, (node u ζ i)^k) = (M : ℂ)*(u : ℂ)^k := by
  have hexp (i : ℕ) : (node u ζ i)^k =
      ∑ j ∈ Finset.range (k+1),
        ((1-u : ℂ)^j*(u : ℂ)^(k-j)*(k.choose j : ℂ))*(ζ^i)^j := by
    unfold node
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum]
  rw [Finset.sum_eq_single 0]
  · simp [mul_comm]
  · intro j hj hj0
    have hjk : j <= k := by simpa using Finset.mem_range.mp hj
    rw [sum_root_powers hζ (by omega) (by omega), mul_zero]
  · simp

/-- The regular term cancels the finite root trace exactly; no order is
discarded and no approximation of the cancellation is used. -/
theorem modelArray_eq_zero {M n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ M)
    (hn : n+1 < M) (u : ℝ) : modelArray M u ζ n = 0 := by
  unfold modelArray singularPower regularPower
  rw [sum_node_powers hζ hn]
  ring

/-- Every translated mode has norm at most one. -/
theorem node_norm_le {u : ℝ} (hu : 0 <= u) (hu1 : u <= 1)
    {ζ : ℂ} (hz : ‖ζ‖ = 1) (i : ℕ) : ‖node u ζ i‖ <= 1 := by
  unfold node
  have h := norm_add_le (u : ℂ) ((1-u : ℂ)*ζ^i)
  rw [norm_mul, norm_pow, hz, one_pow, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hu] at h
  have hreal : ‖(1-u : ℂ)‖ = 1-u := by
    norm_cast
    rw [Real.norm_of_nonneg (by linarith)]
  rw [hreal] at h
  linarith only [h]

/-- The source mode is exactly one before taking its negative residue. -/
theorem node_zero (u : ℝ) (ζ : ℂ) : node u ζ 0 = 1 := by simp [node]

/-- A strict unit-circle node other than one has real part below one. -/
theorem re_lt_one_of_unit {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) : z.re < 1 := by
  have hr := Complex.re_le_norm z
  rw [hz] at hr
  by_contra! hc
  have he : z.re = 1 := by linarith
  have hs : z.re*z.re+z.im*z.im = 1 := by
    simpa only [Complex.sq_norm, Complex.normSq_apply, hz, one_pow] using
      (Complex.sq_norm z).symm
  have hi : z.im = 0 := by nlinarith only [hs, he]
  apply hne
  apply Complex.ext <;> simp [he, hi]

/-- Every unselected mode is strictly smaller than the source radius. -/
theorem node_norm_lt {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    {ζ : ℂ} (hz : ‖ζ‖ = 1) {i : ℕ} (hne : ζ^i ≠ 1) : ‖node u ζ i‖ < 1 := by
  have hunit : ‖ζ^i‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hr := re_lt_one_of_unit hunit hne
  have hs : (ζ^i).re*(ζ^i).re+(ζ^i).im*(ζ^i).im = 1 := by
    rw [←Complex.normSq_apply, ←Complex.sq_norm, hunit, one_pow]
  have he : Complex.normSq (node u ζ i) =
      u^2+(1-u)^2+2*u*(1-u)*(ζ^i).re := by
    simp only [node, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    linear_combination (1-u)^2*hs
  have hn := Complex.sq_norm (node u ζ i)
  rw [he] at hn
  have hp : 0 < u*(1-u) := mul_pos hu (by linarith)
  have hc := mul_lt_mul_of_pos_left hr hp
  nlinarith only [hn, hc, norm_nonneg (node u ζ i)]

/-- Physical denominator of a toy node. This does not assert a zeta zero. -/
def denominator (u : ℝ) (ζ : ℂ) (i : ℕ) : ℂ := (u : ℂ)/node u ζ i

/-- The translated circle has no zero node at any allowed index. -/
theorem node_ne_zero {u : ℝ} (hu : 1/2 < u) (hu1 : u < 1)
    {ζ : ℂ} (hz : ‖ζ‖ = 1) (i : ℕ) : node u ζ i ≠ 0 := by
  have hunit : ‖ζ^i‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hr : -1 <= (ζ^i).re := by
    have h := Complex.abs_re_le_norm (ζ^i)
    rw [hunit] at h
    exact (abs_le.mp h).1
  have hc := mul_le_mul_of_nonneg_left hr (show 0 <= 1-u by linarith)
  apply Complex.ne_zero_of_re_pos
  simp only [node, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.sub_re, Complex.one_re, Complex.ofReal_im, Complex.sub_im,
    Complex.one_im, zero_mul, sub_zero]
  linarith

/-- ALL toy denominators lie in the selected rightmost half-plane.
This is stronger than requiring arbitrary disk exposure alone. -/
theorem denominator_re_ge {u : ℝ} (hu : 1/2 < u) (hu1 : u < 1)
    {ζ : ℂ} (hz : ‖ζ‖ = 1) (i : ℕ) : u <= (denominator u ζ i).re := by
  have hunit : ‖ζ^i‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hr : (ζ^i).re <= 1 := by simpa only [hunit] using Complex.re_le_norm (ζ^i)
  have hs : (ζ^i).re*(ζ^i).re+(ζ^i).im*(ζ^i).im = 1 := by
    rw [←Complex.normSq_apply, ←Complex.sq_norm, hunit, one_pow]
  have he : (node u ζ i).re-Complex.normSq (node u ζ i) =
      (2*u-1)*(1-u)*(1-(ζ^i).re) := by
    simp only [node, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    linear_combination -(1-u)^2*hs
  have hpos : 0 <= (2*u-1)*(1-u)*(1-(ζ^i).re) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hnorm : 0 < Complex.normSq (node u ζ i) :=
    Complex.normSq_pos.mpr (node_ne_zero hu hu1 hz i)
  have hx : Complex.normSq (node u ζ i) <= (node u ζ i).re := by linarith only [he, hpos]
  unfold denominator
  rw [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  apply (le_div_iff₀ hnorm).mpr
  exact mul_le_mul_of_nonneg_left hx (by linarith)

/-- Strict exposure of every unselected denominator. -/
theorem denominator_norm_gt {M i : ℕ} {u : ℝ} (hu : 1/2 < u) (hu1 : u < 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ M) (hi : i < M) (hi0 : i ≠ 0) :
    u < ‖denominator u ζ i‖ := by
  have hM : M ≠ 0 := by omega
  have hz := hζ.norm'_eq_one hM
  have hn := node_norm_lt (show 0 < u by linarith) hu1 hz
    (hζ.pow_ne_one_of_pos_of_lt hi0 hi)
  have hne := node_ne_zero hu hu1 hz i
  unfold denominator
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 <= u)]
  apply (lt_div_iff₀ (norm_pos_iff.mpr hne)).mpr
  simpa only [mul_one] using mul_lt_mul_of_pos_left hn (show 0 < u by linarith)

/-- Literal local index cutoff for the toy finite-divisor disk. -/
def localIndices (M : ℕ) (u : ℝ) (ζ : ℂ) : Finset ℕ :=
  (Finset.range M).filter (fun i => 5*u/4 < ‖node u ζ i‖)

/-- The source is retained by the local cutoff. -/
theorem zero_mem_local {M : ℕ} (hM : 0 < M) {u : ℝ} (hu : u <= 3/5) (ζ : ℂ) :
    0 ∈ localIndices M u ζ := by
  simp only [localIndices, Finset.mem_filter, Finset.mem_range, node_zero, norm_one]
  exact ⟨hM, by linarith⟩

/-- Every LOCAL toy position has actual nontrivial-strip coordinates,
is no farther right than the selected one, and lies in a radius-4/5 disk.
These are synthetic coordinates, not `NontrivialZetaZero` objects. -/
theorem local_geometry {M i : ℕ} {u : ℝ} (hu : 1/2 < u) (hu1 : u < 1)
    {ζ : ℂ} (hz : ‖ζ‖ = 1) (hi : i ∈ localIndices M u ζ) :
    ‖denominator u ζ i‖ < 4/5 ∧ u <= (denominator u ζ i).re ∧
      0 < 3/2-(denominator u ζ i).re ∧ 3/2-(denominator u ζ i).re < 1 := by
  have he := (Finset.mem_filter.mp hi).2
  have hre := denominator_re_ge hu hu1 hz i
  have hd : ‖denominator u ζ i‖ < 4/5 := by
    unfold denominator
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 <= u)]
    apply (div_lt_iff₀ (norm_pos_iff.mpr (node_ne_zero hu hu1 hz i))).mpr
    linarith only [he]
  have hr := (Complex.re_le_norm (denominator u ζ i)).trans_lt hd
  exact ⟨hd, hre, by linarith, by linarith⟩

/-- Exact remaining regular coefficient after the physical local cutoff.
All omitted nodes are included with their negative signs. -/
def localRegular (M : ℕ) (u : ℝ) (ζ : ℂ) (n : ℕ) : ℂ :=
  regularPower M u (n+1)-2*∑ i ∈ (Finset.range M) \ localIndices M u ζ,
    (node u ζ i)^(n+1)

/-- Exact local principal-part ledger, before norms. -/
theorem model_eq_local (M : ℕ) (u : ℝ) (ζ : ℂ) (n : ℕ) :
    modelArray M u ζ n =
      -2*(∑ i ∈ localIndices M u ζ, (node u ζ i)^(n+1))+localRegular M u ζ n := by
  unfold modelArray singularPower localRegular
  have h := Finset.sum_sdiff (f := fun i => (node u ζ i)^(n+1))
    (Finset.filter_subset (fun i => 5*u/4 < ‖node u ζ i‖) (Finset.range M))
  change (∑ i ∈ (Finset.range M) \ localIndices M u ζ, (node u ζ i)^(n+1))+
    (∑ i ∈ localIndices M u ζ, (node u ζ i)^(n+1)) =
    ∑ i ∈ Finset.range M, (node u ζ i)^(n+1) at h
  linear_combination 2*h

/-- The cloud has DISTINCT positions, not repeated indices disguising
fractional or inconsistent residue weights. -/
theorem node_injective {M : ℕ} {u : ℝ} (hu1 : u < 1) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ M) :
    Function.Injective (fun i : Fin M => node u ζ i.val) := by
  intro i j he
  have hc : (1-(u : ℂ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_gt hu1)
  unfold node at he
  have h := mul_left_cancel₀ hc (add_left_cancel he)
  exact Fin.ext (hζ.pow_inj i.isLt j.isLt h)

/-- Physical denominators also have distinct positions. -/
theorem denominator_injective {M : ℕ} {u : ℝ} (hu : 1/2 < u) (hu1 : u < 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ M) :
    Function.Injective (fun i : Fin M => denominator u ζ i.val) := by
  intro i j he
  have hM : M ≠ 0 := by have h := i.isLt; omega
  have hz := hζ.norm'_eq_one hM
  have hc : (u : ℂ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by linarith)
  unfold denominator at he
  have hh := (div_eq_div_iff (node_ne_zero hu hu1 hz i.val)
    (node_ne_zero hu hu1 hz j.val)).mp he
  exact node_injective hu1 hζ (mul_left_cancel₀ hc hh).symm

/-- The LOCAL remainder has a fixed coefficient radius greater than one.
Every order, including zero and one, is covered by this exact bound. -/
theorem localRegular_bound {M : ℕ} {u : ℝ} (hu : 0 <= u) (hu1 : u <= 3/5)
    (ζ : ℂ) (n : ℕ) : ‖localRegular M u ζ n‖ <= 4*M*(3/4 : ℝ)^(n+1) := by
  let S := (Finset.range M) \ localIndices M u ζ
  have hs : S.card <= M := by
    exact (Finset.card_le_card Finset.sdiff_subset).trans_eq (Finset.card_range M)
  have hn : ‖∑ i ∈ S, (node u ζ i)^(n+1)‖ <= M*(3/4 : ℝ)^(n+1) := by
    calc
      _ <= ∑ i ∈ S, ‖(node u ζ i)^(n+1)‖ := norm_sum_le _ _
      _ <= ∑ _i ∈ S, (3/4 : ℝ)^(n+1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := (Finset.mem_sdiff.mp hi).2
        have hm := (Finset.mem_sdiff.mp hi).1
        have he : ‖node u ζ i‖ <= 5*u/4 := by
          by_contra! he
          exact hi' (Finset.mem_filter.mpr ⟨hm, he⟩)
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (he.trans (by linarith)) _
      _ = (S.card : ℝ)*(3/4 : ℝ)^(n+1) := by simp
      _ <= _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (by positivity)
  have hp : ‖regularPower M u (n+1)‖ <= 2*M*(3/4 : ℝ)^(n+1) := by
    unfold regularPower
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_natCast, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg hu]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu (by linarith) _) (by positivity)
  have he := norm_sub_le (regularPower M u (n+1))
    (2*∑ i ∈ S, (node u ζ i)^(n+1))
  rw [norm_mul, Complex.norm_ofNat] at he
  change ‖localRegular M u ζ n‖ <= _ at he
  linarith only [he, hp, mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) <= 2)]

/-- Explicit local analytic representative of the regular coefficients. -/
def localGenerating (M : ℕ) (u : ℝ) (ζ t : ℂ) : ℂ :=
  2*(M : ℂ)*(u : ℂ)/(1-(u : ℂ)*t)-
    2*∑ i ∈ (Finset.range M) \ localIndices M u ζ,
      node u ζ i/(1-node u ζ i*t)

/-- The regular part is analytic on a genuine fixed closed disk beyond
the source radius. This remains a MODEL analyticity statement. -/
theorem localGenerating_analytic {M : ℕ} {u : ℝ} (hu : 0 <= u)
    (hu1 : u <= 10001/20000) (ζ : ℂ) {t : ℂ} (ht : ‖t‖ <= 4/3) :
    AnalyticAt ℂ (localGenerating M u ζ) t := by
  have hden {b : ℂ} (hb : ‖b‖ <= (10001/16000 : ℝ)) : 1-b*t ≠ 0 := by
    have hn : ‖b*t‖ < 1 := by
      rw [norm_mul]
      have h := mul_le_mul hb ht (norm_nonneg _) (by norm_num : (0 : ℝ) <= 10001/16000)
      norm_num at h
      linarith
    exact sub_ne_zero.mpr (by intro he; rw [←he, norm_one] at hn; linarith)
  have hscalar : ‖(u : ℂ)‖ <= 10001/16000 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hu]
    linarith only [hu1]
  have ha : AnalyticAt ℂ (fun v : ℂ => 2*(M : ℂ)*(u : ℂ)/(1-(u : ℂ)*v)) t :=
    analyticAt_const.div (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
      (hden hscalar)
  have hi (i : ℕ) (hi : i ∈ (Finset.range M) \ localIndices M u ζ) :
      AnalyticAt ℂ (fun v => node u ζ i/(1-node u ζ i*v)) t := by
    have he : ‖node u ζ i‖ <= 5*u/4 := by
      by_contra! he
      exact (Finset.mem_sdiff.mp hi).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1, he⟩)
    have hb : ‖node u ζ i‖ <= 10001/16000 := he.trans (by linarith only [hu1])
    exact analyticAt_const.div (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
      (hden hb)
  exact ha.sub (analyticAt_const.mul (Finset.analyticAt_fun_sum _ hi))

/-- The analytic representative has EXACTLY the regular coefficients in
the local ledger; it is not merely a function with a similar radius. -/
theorem hasSum_localRegular {M : ℕ} {u : ℝ} (hu : 0 <= u)
    (hu1 : u <= 10001/20000) (ζ : ℂ) {t : ℂ} (ht : ‖t‖ <= 4/3) :
    HasSum (fun n : ℕ => localRegular M u ζ n*t^n)
      (localGenerating M u ζ t) := by
  have hgeom {b : ℂ} (hb : ‖b‖ <= (10001/16000 : ℝ)) :
      HasSum (fun n : ℕ => b^(n+1)*t^n) (b/(1-b*t)) := by
    have hn : ‖b*t‖ < 1 := by
      rw [norm_mul]
      have h := mul_le_mul hb ht (norm_nonneg _)
        (by norm_num : (0 : ℝ) <= 10001/16000)
      norm_num at h
      linarith
    have h := (hasSum_geometric_of_norm_lt_one hn).mul_left b
    simpa only [mul_pow, pow_succ, div_eq_mul_inv, mul_assoc,
      mul_comm, mul_left_comm] using h
  have hscalar : ‖(u : ℂ)‖ <= 10001/16000 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hu]
    linarith only [hu1]
  have hreg := (hgeom hscalar).mul_left (2*(M : ℂ))
  have hi (i : ℕ) (hi : i ∈ (Finset.range M) \ localIndices M u ζ) :
      HasSum (fun n : ℕ => (node u ζ i)^(n+1)*t^n)
        (node u ζ i/(1-node u ζ i*t)) := by
    have he : ‖node u ζ i‖ <= 5*u/4 := by
      by_contra! he
      exact (Finset.mem_sdiff.mp hi).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1, he⟩)
    exact hgeom (he.trans (by linarith only [hu1]))
  have hs := (hasSum_sum hi).mul_left (2 : ℂ)
  have hh := (hreg.sub hs).congr_fun
    (g := fun n : ℕ => localRegular M u ζ n*t^n) (fun n => by
      simp only [localRegular, regularPower, sub_mul, mul_assoc, Finset.sum_mul]
      )
  simpa only [localGenerating, div_eq_mul_inv, mul_assoc] using hh

/-- A uniform whole-family budget, used only AFTER the exact low-order
cancellation. No separate positive debit is assigned to low orders. -/
theorem norm_modelArray_le_three_count {M n : ℕ} {u : ℝ} (hu : 0 <= u)
    (hu1 : u <= 3/5) {ζ : ℂ} (hz : ‖ζ‖ = 1) (hn : 1 <= n) :
    ‖modelArray M u ζ n‖ <= 3*M := by
  have hu' : u <= 1 := by linarith
  have hs : ‖∑ i ∈ Finset.range M, (node u ζ i)^(n+1)‖ <= (M : ℝ) := by
    calc
      _ <= ∑ i ∈ Finset.range M, ‖(node u ζ i)^(n+1)‖ := norm_sum_le _ _
      _ <= ∑ _i ∈ Finset.range M, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_pow]
        exact (pow_le_pow_left₀ (norm_nonneg _) (node_norm_le hu hu' hz i) _).trans
          (by simp)
      _ = _ := by simp
  have hp : u^(n+1) <= 1/2 := by
    have h := pow_le_pow_of_le_one hu hu' (show 2 <= n+1 by omega)
    have hsq := pow_le_pow_left₀ hu hu1 2
    norm_num at hsq
    linarith only [h, hsq]
  have hb := norm_add_le (singularPower M u ζ (n+1)) (regularPower M u (n+1))
  unfold modelArray
  apply hb.trans
  unfold singularPower regularPower
  rw [norm_mul, norm_neg, Complex.norm_ofNat, norm_mul, norm_mul,
    Complex.norm_ofNat, Complex.norm_natCast, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hu]
  nlinarith only [mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) <= 2),
    mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) <= 2*M)]

/-- The negative selected residue survives eventually. -/
theorem modelArray_tendsto {M : ℕ} (hM : 0 < M) {u : ℝ}
    (hu : 0 < u) (hu1 : u < 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ M) :
    Tendsto (modelArray M u ζ) atTop (𝓝 (-2)) := by
  have hz := hζ.norm'_eq_one hM.ne'
  have hn (i : ℕ) (hi : i ∈ (Finset.range M).erase 0) :
      Tendsto (fun n : ℕ => (node u ζ i)^(n+1)) atTop (𝓝 0) := by
    obtain ⟨hi0, hiM⟩ := Finset.mem_erase.mp hi
    have he := node_norm_lt hu hu1 hz
      (hζ.pow_ne_one_of_pos_of_lt hi0 (Finset.mem_range.mp hiM))
    exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one he).comp (tendsto_add_atTop_nat 1)
  have hs := tendsto_finsetSum ((Finset.range M).erase 0) hn
  simp only [Finset.sum_const_zero] at hs
  have hreg : Tendsto (fun n : ℕ => regularPower M u (n+1)) atTop (𝓝 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (show ‖(u : ℂ)‖ < 1 by simpa [Real.norm_of_nonneg hu.le] using hu1)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [regularPower, mul_zero, Function.comp_def] using hp.const_mul (2*(M : ℂ))
  have ht := ((hs.const_add (1 : ℂ)).const_mul (-2 : ℂ)).add hreg
  norm_num at ht
  apply ht.congr
  intro n
  unfold modelArray singularPower
  rw [←Finset.sum_erase_add _ _ (Finset.mem_range.mpr hM), node_zero, one_pow]
  ring

/-- Concrete integer cloud size; it is not a claimed actual zero count. -/
def modeCount : ℕ := 131072

/-- The original restricted source radius. -/
def sourceRadius : ℝ := 10001/20000

/-- Concrete primitive root; no enumeration of 131072 nodes is trusted. -/
def root : ℂ := Complex.exp (2*Real.pi*I/(modeCount : ℂ))

/-- Kernel-checked exact order of the root. -/
theorem root_primitive : IsPrimitiveRoot root modeCount := by
  exact Complex.isPrimitiveRoot_exp modeCount (by norm_num [modeCount])

/-- An exact block Bernoulli certificate pays the full late-order mass. -/
theorem real_axis_growth_covers_cloud : (3*modeCount : ℝ) <= (2*sourceRadius)^modeCount := by
  have hb' : (641/625 : ℝ) <= (10001/10000)^256 := by
    norm_num
  have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) <= 641/625) hb' 512
  rw [←pow_mul] at hc
  have hn : (3 : ℝ)*131072 <= (641/625 : ℝ)^512 := by
    set_option exponentiation.threshold 512 in norm_num
  unfold modeCount sourceRadius
  change (3 : ℝ)*131072 <= ((2 : ℝ)*(10001/20000))^131072
  rw [show (2 : ℝ)*(10001/20000) = 10001/10000 by norm_num]
  exact hn.trans (by simpa only [Nat.reduceMul] using hc)

/-- ALL orders satisfy the complete real-axis pole majorant, not just
the finite detector window. This is a MODEL result, not a prime bound. -/
theorem model_complete_moment_bound (n : ℕ) :
    ‖modelArray modeCount sourceRadius root n‖ <= (2*sourceRadius)^(n+1) := by
  by_cases hn : n+1 < modeCount
  · rw [modelArray_eq_zero root_primitive hn]
    simpa only [norm_zero] using pow_nonneg
      (by norm_num [sourceRadius] : (0 : ℝ) <= 2*sourceRadius) (n+1)
  · have hnM : modeCount <= n+1 := by omega
    have hb := norm_modelArray_le_three_count (M := modeCount)
      (by norm_num [sourceRadius] : 0 <= sourceRadius)
      (by norm_num [sourceRadius] : sourceRadius <= 3/5)
      (root_primitive.norm'_eq_one (by norm_num [modeCount]))
      (show 1 <= n by unfold modeCount at hnM; omega)
    exact hb.trans (real_axis_growth_covers_cloud.trans
      (pow_le_pow_right₀ (by norm_num [sourceRadius] : 1 <= 2*sourceRadius) hnM))

/-- The SAME joined evaluator eventually violates the requested ceiling
for this synthetic array. No identification with actual primes is made. -/
theorem model_joined_gt_ceiling :
    ∀ᶠ N : ℕ in atTop, (42/25 : ℝ) <
      (-ZetaRieszSignedSelbergPayment.traceError (modelArray modeCount sourceRadius root) (N-1)-
        ZetaRieszSelbergSourceAudit.harmonicEvaluation
          (modelArray modeCount sourceRadius root) sourceRadius N).re := by
  have ht := ZetaRieszCeilingDensityAudit.joined_double_tendsto _
    (modelArray_tendsto (by norm_num [modeCount] : 0 < modeCount)
      (by norm_num [sourceRadius] : 0 < sourceRadius)
      (by norm_num [sourceRadius] : sourceRadius < 1) root_primitive)
    (u := sourceRadius) (by norm_num [sourceRadius]) (by norm_num [sourceRadius])
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  simp only [Complex.ofReal_re] at hr
  have hc := ZetaRieszEndgameSlack.retainedCost_lower
    (u := sourceRadius) (by norm_num [sourceRadius])
    (by norm_num [sourceRadius, ZetaRieszWideOwnerAudit.radiusCeiling])
  exact hr.eventually_const_lt (by linarith only [hc])

end RiemannGaussian.ZetaRieszCeilingClusterPowerAudit

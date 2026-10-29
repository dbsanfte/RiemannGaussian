/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryPartitionRate
import RiemannGaussian.SemiprimeD1BoundaryWidth
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Cube-root width bound for the actual acquired partition -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BoundaryPartitionWidthRate
open SemiprimeD1BoundaryPlan SemiprimeD1BoundaryPartitionRate

/-- Real cube witness determined solely by the original occurrence count and degree. -/
noncomputable def ratioRoot (g : Graph) : Real :=
  ((g.edges.length : Real) / (maxDegree g : Real)) ^ ((3 : Real)⁻¹)

/-- The deterministic ratio root has exactly its defining cube. -/
theorem ratioRoot_cube (g : Graph) :
    ratioRoot g ^ 3 = (g.edges.length : Real) / (maxDegree g : Real) := by
  exact Real.rpow_inv_natCast_pow (by positivity) (by decide : (3 : Nat) ≠ 0)

/-- On a valid nonempty graph, the cube root is positive and at least one. -/
theorem ratioRoot_ge_one (g : Graph) (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hm : 0 < g.edges.length) : 1 ≤ ratioRoot g := by
  have hd : (0 : Real) < maxDegree g := by exact_mod_cast maxDegree_pos g hg hm
  have hmd : (maxDegree g : Real) ≤ g.edges.length := by exact_mod_cast maxDegree_le_edges g
  have hnon : 0 ≤ ratioRoot g := Real.rpow_nonneg (by positivity) _
  have hc := ratioRoot_cube g
  have hcube : (1 : Real)^3 ≤ ratioRoot g ^ 3 := by
    rw [hc]
    exact (le_div_iff₀ hd).mpr (by simpa using hmd)
  exact (pow_le_pow_iff_left₀ (by norm_num) hnon (by decide)).mp hcube

/-- Actual successful acquisition lies above the continuous cube witness. -/
theorem ratioRoot_le_chooseK (g : Graph) (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hm : 0 < g.edges.length) : ratioRoot g ≤ (chooseK g : Real) := by
  have hd : (0 : Real) < maxDegree g := by exact_mod_cast maxDegree_pos g hg hm
  have hs : (g.edges.length : Real) ≤ (chooseK g : Real)^3 * (maxDegree g : Real) := by
    exact_mod_cast chooseK_sufficient g hg hm
  apply (pow_le_pow_iff_left₀ (by dsimp [ratioRoot]; positivity) (by positivity) (by decide : 3 ≠ 0)).mp
  rw [ratioRoot_cube]
  exact (div_le_iff₀ hd).mpr hs

/-- The first successful actual integer lies at most one above its continuous root. -/
theorem chooseK_le_ratioRoot_add_one (g : Graph) (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hm : 0 < g.edges.length) : (chooseK g : Real) ≤ ratioRoot g + 1 := by
  have hk := SemiprimeD1BoundaryChoice.chooseK_bounds g
  by_cases hsmall : chooseK g ≤ 2
  · have he : chooseK g = 2 := by omega
    rw [he]
    have hr := ratioRoot_ge_one g hg hm
    norm_num
    linarith
  · have hprev := chooseK_previous_fails g hg hm (by omega)
    have hp : (((chooseK g - 1 : Nat) : Real)^3) * (maxDegree g : Real) < g.edges.length := by
      exact_mod_cast hprev
    have hd : (0 : Real) < maxDegree g := by exact_mod_cast maxDegree_pos g hg hm
    have hlt : ((chooseK g - 1 : Nat) : Real)^3 < ratioRoot g ^ 3 := by
      rw [ratioRoot_cube]
      exact (lt_div_iff₀ hd).mpr hp
    have hl := (pow_lt_pow_iff_left₀ (by positivity : (0 : Real) ≤ (chooseK g - 1 : Nat))
      (by dsimp [ratioRoot]; positivity) (by decide : 3 ≠ 0)).mp hlt
    have hsub : ((chooseK g - 1 : Nat) : Real) = (chooseK g : Real) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hsub] at hl
    linarith

/-- Actual acquisition is no larger than the least integer above the cube root,
subject to its fixed minimum menu size two. -/
theorem chooseK_le_ceil_ratioRoot (g : Graph) (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hm : 0 < g.edges.length) : chooseK g ≤ max 2 (Nat.ceil (ratioRoot g)) := by
  let t := max 2 (Nat.ceil (ratioRoot g))
  have ht : 2 ≤ t := Nat.le_max_left _ _
  by_cases htop : t ≤ g.edges.length + 2
  · apply chooseK_le_candidate g hg hm t ht htop
    have hrceil : ratioRoot g ≤ (Nat.ceil (ratioRoot g) : Real) := Nat.le_ceil _
    have hct : (Nat.ceil (ratioRoot g) : Real) ≤ (t : Real) := by
      exact_mod_cast (Nat.le_max_right 2 (Nat.ceil (ratioRoot g)))
    have hpow := pow_le_pow_left₀ (show 0 ≤ ratioRoot g by dsimp [ratioRoot]; positivity)
      (hrceil.trans hct) 3
    have hd : (0 : Real) < maxDegree g := by exact_mod_cast maxDegree_pos g hg hm
    have hc : ratioRoot g ^ 3 * (maxDegree g : Real) = g.edges.length := by
      rw [ratioRoot_cube, div_mul_cancel₀ _ hd.ne']
    have hh := mul_le_mul_of_nonneg_right hpow hd.le
    rw [hc] at hh
    exact_mod_cast hh
  · have hh := (SemiprimeD1BoundaryChoice.chooseK_bounds g).2
    dsimp only [t] at *
    omega

/-- Cube-root form of the actual partition width, with its explicit ratio witness. -/
theorem acquired_width_ratioRoot (g : Graph) (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hm : 0 < g.edges.length) :
    ((acquire g).width : Real) ≤ (g.edges.length : Real) / 2 +
      3 * (ratioRoot g ^ 2 * (maxDegree g : Real)) := by
  let r := ratioRoot g
  let k := chooseK g
  let m : Real := g.edges.length
  let d : Real := maxDegree g
  let q := r^2 * d
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast maxDegree_pos g hg hm
  have hm0 : 0 ≤ m := by positivity
  have hr0 : 0 ≤ r := by dsimp [r, ratioRoot]; positivity
  have hr1 : 1 ≤ r := ratioRoot_ge_one g hg hm
  have hk0 : (0 : Real) < k := by
    have hh := (SemiprimeD1BoundaryChoice.chooseK_bounds g).1
    dsimp [k]
    exact_mod_cast (show 0 < chooseK g by omega)
  have hc : r^3 * d = m := by
    dsimp [r, d, m]
    rw [ratioRoot_cube, div_mul_cancel₀ _ (ne_of_gt hd)]
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hrk : r ≤ (k : Real) := ratioRoot_le_chooseK g hg hm
  have hkr : (k : Real) ≤ 2 * r := by
    have hh := chooseK_le_ratioRoot_add_one g hg hm
    dsimp only [k, r] at *
    linarith
  have hfrac : m / (k : Real) ≤ q := by
    apply (div_le_iff₀ hk0).mpr
    calc
      m = r * q := by dsimp [q]; rw [← hc]; ring
      _ ≤ (k : Real) * q := mul_le_mul_of_nonneg_right hrk hq0
      _ = q * (k : Real) := mul_comm _ _
  let B := ((2 * k - 1 : Nat) : Real) * m * d / 2
  have hcount : ((2 * k - 1 : Nat) : Real) ≤ 2 * (k : Real) := by
    exact_mod_cast (Nat.sub_le (2 * k) 1)
  have hb1 : B ≤ (k : Real) * m * d := by
    have hh := mul_le_mul_of_nonneg_right hcount (show 0 ≤ m * d by positivity)
    dsimp [B]
    nlinarith
  have hb2 : (k : Real) * m * d ≤ (2 * q)^2 := by
    have hh := mul_le_mul_of_nonneg_right hkr (show 0 ≤ m * d by positivity)
    have he : 2 * r * m * d = 2 * q^2 := by
      dsimp [q]
      rw [← hc]
      ring
    nlinarith [sq_nonneg q]
  have hsqrt : Real.sqrt B ≤ 2 * q := Real.sqrt_le_iff.mpr ⟨by positivity, hb1.trans hb2⟩
  have hw := SemiprimeD1BoundaryWidth.acquired_width g hg
  change ((acquire g).width : Real) ≤ (1 / 2 + 1 / (k : Real)) * m + Real.sqrt B at hw
  have he : (1 / 2 + 1 / (k : Real)) * m = m / 2 + m / (k : Real) := by ring
  rw [he] at hw
  change ((acquire g).width : Real) ≤ m / 2 + 3 * q
  linarith

/-- The ratio-root correction is precisely the cube root of `M^2*Delta`. -/
theorem ratioRoot_square_degree (g : Graph) (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hm : 0 < g.edges.length) :
    ratioRoot g ^ 2 * (maxDegree g : Real) =
      ((g.edges.length : Real)^2 * (maxDegree g : Real)) ^ ((3 : Real)⁻¹) := by
  have hd : (0 : Real) < maxDegree g := by exact_mod_cast maxDegree_pos g hg hm
  have hc : ratioRoot g ^ 3 * (maxDegree g : Real) = g.edges.length := by
    rw [ratioRoot_cube, div_mul_cancel₀ _ hd.ne']
  apply (pow_left_inj₀ (by dsimp [ratioRoot]; positivity) (by positivity) (by decide : 3 ≠ 0)).mp
  have hroot : (((g.edges.length : Real)^2 * (maxDegree g : Real)) ^ ((3 : Real)⁻¹))^3 =
      (g.edges.length : Real)^2 * (maxDegree g : Real) :=
    Real.rpow_inv_natCast_pow (by positivity) (by decide : (3 : Nat) ≠ 0)
  rw [hroot]
  calc
    (ratioRoot g ^ 2 * (maxDegree g : Real))^3 =
        (ratioRoot g ^ 3 * (maxDegree g : Real))^2 * (maxDegree g : Real) := by ring
    _ = _ := by rw [hc]

/-- Explicit cube-root width bound for the actual deterministic acquired partition. -/
theorem acquired_width_cuberoot (g : Graph) (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hm : 0 < g.edges.length) :
    ((acquire g).width : Real) ≤ (g.edges.length : Real) / 2 +
      3 * (((g.edges.length : Real)^2 * (maxDegree g : Real)) ^ ((3 : Real)⁻¹)) := by
  simpa only [ratioRoot_square_degree g hg hm] using acquired_width_ratioRoot g hg hm

end RiemannGaussian.SemiprimeD1BoundaryPartitionWidthRate

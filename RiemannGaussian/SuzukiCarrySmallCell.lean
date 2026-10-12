/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryMellinBranches

/-!
# Quantitative small-cell bounds for the literal carry jets

Finite alternating Euler-polynomial prefixes give an extra factor x in
all five tent moments. The coefficient table is rational algebra, not
numerical fitting. Every entry is checked against the original prefixes.
-/

namespace RiemannGaussian.SuzukiCarrySmallCell
noncomputable section
open Complex MeasureTheory Set Filter
open SuzukiCarryMellinLimit SuzukiCarryMellinJet SuzukiCarryMellinBranches
open scoped BigOperators Topology
set_option maxHeartbeats 0
set_option maxRecDepth 4096

private def euler (j : ℕ) (v : ℝ) : ℝ := match j with
  | 0 => 1
  | 1 => v-1/2
  | 2 => v^2-v
  | 3 => v^3-3*v^2/2+1/4
  | 4 => v^4-2*v^3+v
  | 5 => v^5-5*v^4/2+5*v^2/2-1/2
  | _ => 0

private theorem euler_translation {j : ℕ} (hj : j ≤ 5) (v : ℝ) :
    euler j v+euler j (v+1) = 2*v^j := by
  interval_cases j <;> norm_num [euler] <;> ring

private theorem alternating_power_prefix {j : ℕ} (hj : j ≤ 5) (K : ℕ) :
    (∑ k ∈ Finset.range K, (-1 : ℝ)^k*((k+1 : ℕ) : ℝ)^j) =
      (euler j 1-(-1 : ℝ)^K*euler j ((K+1 : ℕ) : ℝ))/2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have he := euler_translation hj ((K+1 : ℕ) : ℝ)
    have hv : euler j ((K+1+1 : ℕ) : ℝ) =
        2*((K+1 : ℕ) : ℝ)^j-euler j ((K+1 : ℕ) : ℝ) := by
      push_cast at he ⊢
      linarith
    rw [hv]
    ring

private def fastPrefix (j K : ℕ) (x : ℝ) : ℝ :=
  (x/2)^j*(euler j 1-(-1 : ℝ)^K*euler j ((K+1 : ℕ) : ℝ))/2

private theorem powerPrefix_eq_fast {j : ℕ} (hj : j ≤ 5) (K : ℕ) (x : ℝ) :
    powerPrefix j K x = fastPrefix j K x := by
  have he : powerPrefix j K x = (x/2)^j*
      (∑ k ∈ Finset.range K, (-1 : ℝ)^k*((k+1 : ℕ) : ℝ)^j) := by
    unfold powerPrefix
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [show ((k+1 : ℕ) : ℝ)*x/2 = ((k+1 : ℕ) : ℝ)*(x/2) by ring, mul_pow]
    ring
  rw [he, alternating_power_prefix hj]
  unfold fastPrefix
  ring

private def fastBranch (j n : ℕ) (x : ℝ) : ℝ :=
  2*fastPrefix (j+1) (n/3) x-fastPrefix (j+1) (n/6) x-
    fastPrefix (j+1) (n/2) x+fastPrefix j (n/6) x+
    3*fastPrefix j (n/2) x-4*fastPrefix j (n/3) x

private theorem branch_eq_fast {j : ℕ} (hj : j ≤ 4) (n : ℕ) (x : ℝ) :
    branchMoment j n x = fastBranch j n x := by
  unfold branchMoment fastBranch
  simp_rw [powerPrefix_eq_fast (show j+1 ≤ 5 by omega),
    powerPrefix_eq_fast (show j ≤ 5 by omega)]

/-- Exact Euler-prefix coefficient table, available for further rational
cell certificates. -/
def smallTable (j v : ℕ) : Fin 5 → Fin 6 → ℚ := match (j,v) with
  | (0, 0) => ![![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (0, 1) => ![![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (0, 2) => ![![0, (1/4), 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (0, 3) => ![![(1/4), (-1/12), 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (0, 4) => ![![(1/6), (-1/3), 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (0, 5) => ![![(-1/6), (-1/3), 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (0, 6) => ![![(-1/2), (1/3), 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (0, 7) => ![![(-1/6), (1/3), 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (0, 8) => ![![(1/6), (1/12), 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (0, 9) => ![![(1/4), (-1/4), 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (0, 10) => ![![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (0, 11) => ![![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (1, 0) => ![![0, (-1/12), 0, 0, 0, 0],
      ![0, 0, (1/144), 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (1, 1) => ![![(-1/12), (-1/12), 0, 0, 0, 0],
      ![(1/144), (1/72), (1/144), 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (1, 2) => ![![(-1/6), (2/3), 0, 0, 0, 0],
      ![(1/36), (1/36), (-1/18), 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (1, 3) => ![![(1/2), 0, 0, 0, 0, 0],
      ![0, (-1/12), 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (1, 4) => ![![(1/2), (-3/4), 0, 0, 0, 0],
      ![(-1/12), (-1/12), (1/16), 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (1, 5) => ![![(-1/4), (-3/4), 0, 0, 0, 0],
      ![(-5/48), (1/24), (1/16), 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (1, 6) => ![![-1, (3/4), 0, 0, 0, 0],
      ![0, (1/6), (-1/16), 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (1, 7) => ![![(-1/4), (3/4), 0, 0, 0, 0],
      ![(5/48), (1/24), (-1/16), 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (1, 8) => ![![(1/2), 0, 0, 0, 0, 0],
      ![(1/12), (-1/12), 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (1, 9) => ![![(1/2), (-2/3), 0, 0, 0, 0],
      ![0, (-1/12), (1/18), 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (1, 10) => ![![(-1/6), (1/12), 0, 0, 0, 0],
      ![(-1/36), (1/36), (-1/144), 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (1, 11) => ![![(-1/12), (1/12), 0, 0, 0, 0],
      ![(-1/144), (1/72), (-1/144), 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (2, 0) => ![![(1/4), (-1/2), 0, 0, 0, 0],
      ![0, (-1/12), (1/12), 0, 0, 0],
      ![0, 0, (1/192), (-1/288), 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (2, 1) => ![![(-1/4), (-1/2), 0, 0, 0, 0],
      ![0, (1/12), (1/12), 0, 0, 0],
      ![(1/576), 0, (-1/192), (-1/288), 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (2, 2) => ![![(-3/4), (7/4), 0, 0, 0, 0],
      ![(1/6), (1/4), (-7/24), 0, 0, 0],
      ![(-1/144), (-1/48), (-1/64), (7/576), 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (2, 3) => ![![1, (5/12), 0, 0, 0, 0],
      ![(1/8), (-1/3), (-5/72), 0, 0, 0],
      ![(-1/32), (-1/64), (1/48), (5/1728), 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (2, 4) => ![![(17/12), (-11/6), 0, 0, 0, 0],
      ![(-5/18), (-17/36), (11/36), 0, 0, 0],
      ![(-5/216), (5/144), (17/576), (-11/864), 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (2, 5) => ![![(-5/12), (-11/6), 0, 0, 0, 0],
      ![(-4/9), (5/36), (11/36), 0, 0, 0],
      ![(49/1728), (1/18), (-5/576), (-11/864), 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (2, 6) => ![![(-9/4), (11/6), 0, 0, 0, 0],
      ![0, (3/4), (-11/36), 0, 0, 0],
      ![(1/16), 0, (-3/64), (11/864), 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (2, 7) => ![![(-5/12), (11/6), 0, 0, 0, 0],
      ![(4/9), (5/36), (-11/36), 0, 0, 0],
      ![(49/1728), (-1/18), (-5/576), (11/864), 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (2, 8) => ![![(17/12), (-5/12), 0, 0, 0, 0],
      ![(5/18), (-17/36), (5/72), 0, 0, 0],
      ![(-5/216), (-5/144), (17/576), (-5/1728), 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (2, 9) => ![![1, (-7/4), 0, 0, 0, 0],
      ![(-1/8), (-1/3), (7/24), 0, 0, 0],
      ![(-1/32), (1/64), (1/48), (-7/576), 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (2, 10) => ![![(-3/4), (1/2), 0, 0, 0, 0],
      ![(-1/6), (1/4), (-1/12), 0, 0, 0],
      ![(-1/144), (1/48), (-1/64), (1/288), 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (2, 11) => ![![(-1/4), (1/2), 0, 0, 0, 0],
      ![0, (1/12), (-1/12), 0, 0, 0],
      ![(1/576), 0, (-1/192), (1/288), 0, 0],
      ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0]]
  | (3, 0) => ![![(3/2), (-25/12), 0, 0, 0, 0],
      ![0, (-3/4), (25/48), 0, 0, 0],
      ![0, 0, (3/32), (-25/576), 0, 0],
      ![0, 0, 0, (-1/288), (25/20736), 0],
      ![0, 0, 0, 0, 0, 0]]
  | (3, 1) => ![![(-7/12), (-25/12), 0, 0, 0, 0],
      ![(-11/48), (7/24), (25/48), 0, 0, 0],
      ![(29/576), (11/192), (-7/192), (-25/576), 0, 0],
      ![(-47/20736), (-29/5184), (-11/3456), (7/5184), (25/20736), 0],
      ![0, 0, 0, 0, 0, 0]]
  | (3, 2) => ![![(-8/3), (14/3), 0, 0, 0, 0],
      ![(7/12), (4/3), (-7/6), 0, 0, 0],
      ![(1/36), (-7/48), (-1/6), (7/72), 0, 0],
      ![(-11/1296), (-1/324), (7/864), (1/162), (-7/2592), 0],
      ![0, 0, 0, 0, 0, 0]]
  | (3, 3) => ![![2, 2, 0, 0, 0, 0],
      ![(3/4), -1, (-1/2), 0, 0, 0],
      ![(-3/16), (-3/16), (1/8), (1/24), 0, 0],
      ![0, (1/48), (1/96), (-1/216), (-1/864), 0],
      ![0, 0, 0, 0, 0, 0]]
  | (3, 4) => ![![4, (-19/4), 0, 0, 0, 0],
      ![(-3/4), -2, (19/16), 0, 0, 0],
      ![(-5/24), (3/16), (1/4), (-19/192), 0, 0],
      ![(11/432), (5/216), (-1/96), (-1/108), (19/6912), 0],
      ![0, 0, 0, 0, 0, 0]]
  | (3, 5) => ![![(-3/4), (-19/4), 0, 0, 0, 0],
      ![(-25/16), (3/8), (19/16), 0, 0, 0],
      ![(25/192), (25/64), (-3/64), (-19/192), 0, 0],
      ![(73/2304), (-25/1728), (-25/1152), (1/576), (19/6912), 0],
      ![0, 0, 0, 0, 0, 0]]
  | (3, 6) => ![![(-11/2), (19/4), 0, 0, 0, 0],
      ![0, (11/4), (-19/16), 0, 0, 0],
      ![(3/8), 0, (-11/32), (19/192), 0, 0],
      ![0, (-1/24), 0, (11/864), (-19/6912), 0],
      ![0, 0, 0, 0, 0, 0]]
  | (3, 7) => ![![(-3/4), (19/4), 0, 0, 0, 0],
      ![(25/16), (3/8), (-19/16), 0, 0, 0],
      ![(25/192), (-25/64), (-3/64), (19/192), 0, 0],
      ![(-73/2304), (-25/1728), (25/1152), (1/576), (-19/6912), 0],
      ![0, 0, 0, 0, 0, 0]]
  | (3, 8) => ![![4, -2, 0, 0, 0, 0],
      ![(3/4), -2, (1/2), 0, 0, 0],
      ![(-5/24), (-3/16), (1/4), (-1/24), 0, 0],
      ![(-11/432), (5/216), (1/96), (-1/108), (1/864), 0],
      ![0, 0, 0, 0, 0, 0]]
  | (3, 9) => ![![2, (-14/3), 0, 0, 0, 0],
      ![(-3/4), -1, (7/6), 0, 0, 0],
      ![(-3/16), (3/16), (1/8), (-7/72), 0, 0],
      ![0, (1/48), (-1/96), (-1/216), (7/2592), 0],
      ![0, 0, 0, 0, 0, 0]]
  | (3, 10) => ![![(-8/3), (25/12), 0, 0, 0, 0],
      ![(-7/12), (4/3), (-25/48), 0, 0, 0],
      ![(1/36), (7/48), (-1/6), (25/576), 0, 0],
      ![(11/1296), (-1/324), (-7/864), (1/162), (-25/20736), 0],
      ![0, 0, 0, 0, 0, 0]]
  | (3, 11) => ![![(-7/12), (25/12), 0, 0, 0, 0],
      ![(11/48), (7/24), (-25/48), 0, 0, 0],
      ![(29/576), (-11/192), (-7/192), (25/576), 0, 0],
      ![(47/20736), (-29/5184), (11/3456), (7/5184), (-25/20736), 0],
      ![0, 0, 0, 0, 0, 0]]
  | (4, 0) => ![![(25/4), (-15/2), 0, 0, 0, 0],
      ![0, (-25/6), (5/2), 0, 0, 0],
      ![(-3/16), 0, (25/32), (-5/16), 0, 0],
      ![0, (1/24), 0, (-25/432), (5/288), 0],
      ![0, 0, (-5/2304), 0, (125/82944), (-5/13824)]]
  | (4, 1) => ![![(-5/4), (-15/2), 0, 0, 0, 0],
      ![(-5/3), (5/6), (5/2), 0, 0, 0],
      ![(9/32), (5/8), (-5/32), (-5/16), 0, 0],
      ![(1/864), (-1/16), (-5/72), (5/432), (5/288), 0],
      ![(-85/82944), (-5/41472), (5/1536), (25/10368), (-25/82944), (-5/13824)]]
  | (4, 2) => ![![(-35/4), (51/4), 0, 0, 0, 0],
      ![(5/3), (35/6), (-17/4), 0, 0, 0],
      ![(7/16), (-5/8), (-35/32), (17/32), 0, 0],
      ![(-11/108), (-7/72), (5/72), (35/432), (-17/576), 0],
      ![(5/1296), (55/5184), (35/6912), (-25/10368), (-175/82944), (17/27648)]]
  | (4, 3) => ![![4, (89/12), 0, 0, 0, 0],
      ![(13/4), (-8/3), (-89/36), 0, 0, 0],
      ![(-3/4), (-39/32), (1/2), (89/288), 0, 0],
      ![(-5/64), (1/6), (13/96), (-1/27), (-89/5184), 0],
      ![(1/64), (25/3072), (-5/576), (-65/13824), (5/5184), (89/248832)]]
  | (4, 4) => ![![(137/12), (-77/6), 0, 0, 0, 0],
      ![(-17/9), (-137/18), (77/18), 0, 0, 0],
      ![(-167/144), (17/24), (137/96), (-77/144), 0, 0],
      ![(55/324), (167/648), (-17/216), (-137/1296), (77/2592), 0],
      ![(91/7776), (-275/15552), (-835/62208), (85/31104), (685/248832), (-77/124416)]]
  | (4, 5) => ![![(-17/12), (-77/6), 0, 0, 0, 0],
      ![(-47/9), (17/18), (77/18), 0, 0, 0],
      ![(127/288), (47/24), (-17/96), (-77/144), 0, 0],
      ![(707/2592), (-127/1296), (-47/216), (17/1296), (77/2592), 0],
      ![(-3617/248832), (-3535/124416), (635/124416), (235/31104), (-85/248832), (-77/124416)]]
  | (4, 6) => ![![(-57/4), (77/6), 0, 0, 0, 0],
      ![0, (19/2), (-77/18), 0, 0, 0],
      ![(27/16), 0, (-57/32), (77/144), 0, 0],
      ![0, (-3/8), 0, (19/144), (-77/2592), 0],
      ![(-1/32), 0, (5/256), 0, (-95/27648), (77/124416)]]
  | (4, 7) => ![![(-17/12), (77/6), 0, 0, 0, 0],
      ![(47/9), (17/18), (-77/18), 0, 0, 0],
      ![(127/288), (-47/24), (-17/96), (77/144), 0, 0],
      ![(-707/2592), (-127/1296), (47/216), (17/1296), (-77/2592), 0],
      ![(-3617/248832), (3535/124416), (635/124416), (-235/31104), (-85/248832), (77/124416)]]
  | (4, 8) => ![![(137/12), (-89/12), 0, 0, 0, 0],
      ![(17/9), (-137/18), (89/36), 0, 0, 0],
      ![(-167/144), (-17/24), (137/96), (-89/288), 0, 0],
      ![(-55/324), (167/648), (17/216), (-137/1296), (89/5184), 0],
      ![(91/7776), (275/15552), (-835/62208), (-85/31104), (685/248832), (-89/248832)]]
  | (4, 9) => ![![4, (-51/4), 0, 0, 0, 0],
      ![(-13/4), (-8/3), (17/4), 0, 0, 0],
      ![(-3/4), (39/32), (1/2), (-17/32), 0, 0],
      ![(5/64), (1/6), (-13/96), (-1/27), (17/576), 0],
      ![(1/64), (-25/3072), (-5/576), (65/13824), (5/5184), (-17/27648)]]
  | (4, 10) => ![![(-35/4), (15/2), 0, 0, 0, 0],
      ![(-5/3), (35/6), (-5/2), 0, 0, 0],
      ![(7/16), (5/8), (-35/32), (5/16), 0, 0],
      ![(11/108), (-7/72), (-5/72), (35/432), (-5/288), 0],
      ![(5/1296), (-55/5184), (35/6912), (25/10368), (-175/82944), (5/13824)]]
  | (4, 11) => ![![(-5/4), (15/2), 0, 0, 0, 0],
      ![(5/3), (5/6), (-5/2), 0, 0, 0],
      ![(9/32), (-5/8), (-5/32), (5/16), 0, 0],
      ![(-1/864), (-1/16), (5/72), (5/432), (-5/288), 0],
      ![(-85/82944), (5/41472), (5/1536), (-25/10368), (-25/82944), (5/13824)]]
  | _ => fun _ _ => 0

/-- Rational coefficients of the exact reduced small-cell moments. -/
def smallCoefficient (j v a b : ℕ) : ℚ :=
  if ha : a < 5 then if hb : b < 6 then smallTable j v ⟨a,ha⟩ ⟨b,hb⟩ else 0 else 0

/-- The original branch after dividing its exact additional x factor. -/
def smallMoment (j v : ℕ) (x t : ℝ) : ℝ :=
  ∑ a : Fin 5, ∑ b : Fin 6, (smallCoefficient j v a b : ℝ)*x^a.val*t^b.val

private def rowCost (j : ℕ) : ℝ := match j with
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 16
  | 4 => 46
  | _ => 0

private theorem coefficient_cost {j v : ℕ} (hj : j ≤ 4) (hv : v < 12) :
    (∑ a : Fin 5, ∑ b : Fin 6, |(smallCoefficient j v a b : ℝ)|) ≤ rowCost j := by
  let q : ℕ → ℚ := fun k => match k with
    | 0 => 1 | 1 => 2 | 2 => 6 | 3 => 16 | 4 => 46 | _ => 0
  have hq : (∑ a : Fin 5, ∑ b : Fin 6, |smallTable j v a b|) ≤ q j := by
    interval_cases j <;> interval_cases v <;> decide +kernel
  have hcost : (q j : ℝ) = rowCost j := by
    interval_cases j <;> norm_num [q,rowCost]
  have hc : (∑ a : Fin 5, ∑ b : Fin 6, |(smallTable j v a b : ℝ)|) ≤ (q j : ℝ) := by
    exact_mod_cast hq
  simpa only [smallCoefficient, dite_eq_left (Fin.is_lt _), hcost] using hc

private theorem smallMoment_abs_le {j v : ℕ} (hj : j ≤ 4) (hv : v < 12)
    {x t : ℝ} (hx : x ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    |smallMoment j v x t| ≤ rowCost j := by
  have hp (a : ℕ) : |x^a| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hx.1 _)]
    simpa using pow_le_pow_left₀ hx.1 hx.2 a
  have hq (b : ℕ) : |t^b| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg ht.1 _)]
    simpa using pow_le_pow_left₀ ht.1 ht.2 b
  unfold smallMoment
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ a : Fin 5, ∑ b : Fin 6, |(smallCoefficient j v a b : ℝ)| := by
      apply Finset.sum_le_sum
      intro a _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro b _
      rw [abs_mul, abs_mul]
      calc
        _ ≤ |(smallCoefficient j v a b : ℝ)| * 1 * 1 := by gcongr; exact hp _; exact hq _
        _ = _ := by ring
    _ ≤ _ := coefficient_cost hj hv

private theorem fastBranch_small {j v : ℕ} (hj : j ≤ 4) (hv : v < 12)
    (m : ℕ) {x t : ℝ} (hx : 0 < x)
    (hm : (m : ℝ)*x = 1-((v : ℝ)+t)*x/12) :
    fastBranch j (12*m+v) x = x*smallMoment j v x t := by
  have h2 : (12*m+v)/2 = 6*m+v/2 := by omega
  have h3 : (12*m+v)/3 = 4*m+v/3 := by omega
  have h6 : (12*m+v)/6 = 2*m+v/6 := by omega
  have hm' : (m : ℝ) = (1-((v : ℝ)+t)*x/12)/x :=
    (eq_div_iff hx.ne').mpr hm
  unfold fastBranch fastPrefix
  rw [h2, h3, h6]
  simp only [pow_add, pow_mul]
  norm_num only [show (-1 : ℝ)^2 = 1 by norm_num,
    show (-1 : ℝ)^4 = 1 by norm_num, show (-1 : ℝ)^6 = 1 by norm_num, one_pow, one_mul]
  interval_cases j <;> interval_cases v <;>
    norm_num [euler, smallMoment, smallCoefficient, smallTable, Fin.sum_univ_succ] <;>
    rw [hm'] <;> field_simp <;> ring

/-- Exact fractional-cell normalization, retaining every moment order. -/
theorem moment_eq_small {j : ℕ} (hj : j ≤ 4) {x : ℝ} (hx : 0 < x) :
    moment j x = x*smallMoment j (⌊12/x⌋₊%12) x (12/x-(⌊12/x⌋₊ : ℝ)) := by
  let n := ⌊12/x⌋₊
  let v := n%12
  let m := n/12
  let t := 12/x-(n : ℝ)
  have hv : v < 12 := Nat.mod_lt _ (by norm_num)
  have hn : n = 12*m+v := by dsimp [m,v]; omega
  have hnx : (n : ℝ) = 12*(m : ℝ)+(v : ℝ) := by exact_mod_cast hn
  have hm : (m : ℝ)*x = 1-((v : ℝ)+t)*x/12 := by
    dsimp [t]
    rw [hnx]
    field_simp
    ring
  rw [moment_eq_branch _ hx]
  change branchMoment j n x = _
  rw [branch_eq_fast hj, hn, fastBranch_small hj hv m hx hm]

/-- Every factorial order used by B,C has a uniform linear small-cell bound. -/
theorem moment_small_abs_le {j : ℕ} (hj : j ≤ 4) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) : |moment j x| ≤ rowCost j*x := by
  let n := ⌊12/x⌋₊
  let v := n%12
  let m := n/12
  let t := 12/x-(n : ℝ)
  have hv : v < 12 := Nat.mod_lt _ (by norm_num)
  have hn : n = 12*m+v := by dsimp [m,v]; omega
  have hnx : (n : ℝ) = 12*(m : ℝ)+(v : ℝ) := by exact_mod_cast hn
  have ht : t ∈ Icc 0 1 := by
    constructor
    · exact sub_nonneg.mpr (Nat.floor_le (by positivity : 0 ≤ 12/x))
    · have h := Nat.lt_floor_add_one (12/x)
      change 12/x-(n : ℝ) ≤ 1
      dsimp [n] at h ⊢
      linarith
  have hm : (m : ℝ)*x = 1-((v : ℝ)+t)*x/12 := by
    dsimp [t]
    field_simp
    nlinarith [hnx]
  rw [moment_eq_branch j hx]
  change |branchMoment j n x| ≤ _
  rw [branch_eq_fast hj, hn, fastBranch_small hj hv m hx hm, abs_mul, abs_of_pos hx]
  have h := smallMoment_abs_le hj hv ⟨hx.le,hx1⟩ ht
  nlinarith

/-- The quadratic density loses two powers of x at the accumulation point. -/
theorem quadraticDensity_small {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    |quadraticDensity x| ≤ 10*x^2 := by
  have h0 := moment_small_abs_le (j := 0) (by norm_num) hx hx1
  have h1 := moment_small_abs_le (j := 1) (by norm_num) hx hx1
  have h2 := moment_small_abs_le (j := 2) (by norm_num) hx hx1
  norm_num [rowCost] at h0 h1 h2
  unfold quadraticDensity
  apply (abs_sub _ _).trans
  rw [abs_pow, abs_mul]
  nlinarith [sq_abs (moment 1 x), abs_nonneg (moment 0 x),
    abs_nonneg (moment 1 x), abs_nonneg (moment 2 x)]

/-- The same certified gain applies to the actual quartic density. -/
theorem quarticDensity_small {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    |quarticDensity x| ≤ 24*x^2 := by
  have h0 := moment_small_abs_le (j := 0) (by norm_num) hx hx1
  have h1 := moment_small_abs_le (j := 1) (by norm_num) hx hx1
  have h2 := moment_small_abs_le (j := 2) (by norm_num) hx hx1
  have h3 := moment_small_abs_le (j := 3) (by norm_num) hx hx1
  have h4 := moment_small_abs_le (j := 4) (by norm_num) hx hx1
  norm_num [rowCost] at h0 h1 h2 h3 h4
  unfold quarticDensity
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_add_le _ _) le_rfl).trans
  rw [abs_div, abs_div, abs_div, abs_pow, abs_mul, abs_mul]
  norm_num
  nlinarith [sq_abs (moment 2 x), abs_nonneg (moment 0 x), abs_nonneg (moment 1 x),
    abs_nonneg (moment 2 x), abs_nonneg (moment 3 x), abs_nonneg (moment 4 x)]

end
end RiemannGaussian.SuzukiCarrySmallCell

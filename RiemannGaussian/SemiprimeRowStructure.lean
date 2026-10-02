/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeOrderSeparation
import Mathlib.Tactic.Group

/-!
# Common structure of weighted factor-sum rows

The centre depends on the product of the weights. Its exponential is the
coupled part left after the two axis powers have been shared. A four-corner
identity tests exactly whether a proposed separable batch is valid in a
group; a collapse in only one prime component is already a separating signal.

These are algebraic identities, not a coverage or bit-complexity theorem.
This side-investigation algebra is checked in the ordinary library; numerical probes remain optional.
-/

namespace RiemannGaussian.SemiprimeRowStructure

/-- Weighted anchor, before any loss of the two weight indices. -/
def rowAnchor {G : Type*} [CommGroup G]
    (g : G) (N a b centre : ℤ) : G := g ^ (a*N+b-centre)

/-- A product-group cache preserves each literal anchor exactly. -/
theorem rowAnchor_factor {G : Type*} [CommGroup G]
    (g : G) (N a b centre : ℤ) :
    rowAnchor g N a b centre = (g^N)^a * g^b * (g⁻¹)^centre := by
  simp only [rowAnchor, ← zpow_mul, inv_zpow, ← zpow_neg, ← zpow_add]
  congr 1
  ring

/-- The normalized four-corner defect contains only the four centres.
The large N-dependent axis powers cancel before the test. -/
theorem rowAnchor_cross_ratio {G : Type*} [CommGroup G]
    (g : G) (N a a' b b' c00 c01 c10 c11 : ℤ) :
    (rowAnchor g N a b c00 * rowAnchor g N a' b' c11) /
      (rowAnchor g N a b' c01 * rowAnchor g N a' b c10) =
      g ^ (c01+c10-c00-c11) := by
  simp only [rowAnchor, ← zpow_add]
  rw [div_eq_mul_inv, ← zpow_neg, ← zpow_add]
  congr 1
  ring

/-- An exact local test for separability; approximate real centres do not
license replacing a modular anchor matrix by an outer product. -/
theorem rowAnchor_cross_eq_iff {G : Type*} [CommGroup G]
    (g : G) (N a a' b b' c00 c01 c10 c11 : ℤ) :
    rowAnchor g N a b c00 * rowAnchor g N a' b' c11 =
      rowAnchor g N a b' c01 * rowAnchor g N a' b c10 ↔
      g ^ (c01+c10-c00-c11) = 1 := by
  rw [← div_eq_one, rowAnchor_cross_ratio]

/-- The centre-curvature test is precisely a local-order divisibility test.
It is not a guarantee that any tested curvature has the required divisor. -/
theorem rowAnchor_cross_eq_iff_order_dvd {G : Type*} [CommGroup G]
    (g : G) (N a a' b b' c00 c01 c10 c11 : ℤ) :
    rowAnchor g N a b c00 * rowAnchor g N a' b' c11 =
      rowAnchor g N a b' c01 * rowAnchor g N a' b c10 ↔
      (orderOf g : ℤ) ∣ c01+c10-c00-c11 := by
  rw [rowAnchor_cross_eq_iff, orderOf_dvd_iff_zpow_eq_one]

/-- A four-corner collapse in just one prime component immediately factors
the input; there is no need to build the large row collision polynomial. -/
theorem centre_defect_separates {p q signal : ℕ} (hq : q.Prime)
    (hp : p ∣ signal) (hnq : ¬q ∣ signal) :
    Nat.gcd (p*q) signal = p := by
  exact SemiprimeOrderSeparation.gcd_semiprime_of_separating_residue hq hp hnq

/-- Swapping the two weight indices cancels their common centre exactly.
All such ratios depend only on the weight difference, not on its product. -/
theorem rowAnchor_swap_ratio {G : Type*} [CommGroup G]
    (g : G) (N a b centre : ℤ) :
    rowAnchor g N a b centre / rowAnchor g N b a centre =
      g ^ ((a-b)*(N-1)) := by
  simp only [rowAnchor]
  rw [div_eq_mul_inv, ← zpow_neg, ← zpow_add]
  congr 1
  ring

/-- The raw signed difference retains an invertible common prefix.
This is the ring version of shared-phase cancellation; the resulting
signal is exactly the N-1 projected-period signal. -/
theorem rowAnchor_swap_difference {K : Type*} [CommRing K]
    (g : Kˣ) (N a b centre : ℤ) :
    (rowAnchor (G := Kˣ) g N a b centre : K) -
      (rowAnchor (G := Kˣ) g N b a centre : K) =
      (rowAnchor (G := Kˣ) g N b a centre : K) *
        (((g ^ ((a-b)*(N-1)) : Kˣ) : K) - 1) := by
  have h : rowAnchor g N a b centre =
      rowAnchor g N b a centre * g ^ ((a-b)*(N-1)) := by
    simp only [rowAnchor, ← zpow_add]
    congr 1
    ring
  rw [h, Units.val_mul]
  ring

/-- The companion even channel also shares the same cheap projected
period; it adds a minus-one test, not a new weighted-centre observable. -/
theorem rowAnchor_swap_sum {K : Type*} [CommRing K]
    (g : Kˣ) (N a b centre : ℤ) :
    (rowAnchor (G := Kˣ) g N a b centre : K) +
      (rowAnchor (G := Kˣ) g N b a centre : K) =
      (rowAnchor (G := Kˣ) g N b a centre : K) *
        (((g ^ ((a-b)*(N-1)) : Kˣ) : K) + 1) := by
  have h : rowAnchor g N a b centre =
      rowAnchor g N b a centre * g ^ ((a-b)*(N-1)) := by
    simp only [rowAnchor, ← zpow_add]
    congr 1
    ring
  rw [h, Units.val_mul]
  ring

/-- Retaining the target-one boundary gives a root-preserving paired
product. The cheap difference mode alone is insufficient: the common
prefix still enters both the linear and quadratic terms. -/
theorem rowAnchor_swap_target_product {K : Type*} [CommRing K]
    (g : Kˣ) (N a b centre : ℤ) :
    ((rowAnchor (G := Kˣ) g N a b centre : K) - 1) *
      ((rowAnchor (G := Kˣ) g N b a centre : K) - 1) =
      (rowAnchor (G := Kˣ) g N b a centre : K)^2 *
        ((g ^ ((a-b)*(N-1)) : Kˣ) : K) -
      (rowAnchor (G := Kˣ) g N b a centre : K) *
        (((g ^ ((a-b)*(N-1)) : Kˣ) : K) + 1) + 1 := by
  have h : rowAnchor g N a b centre =
      rowAnchor g N b a centre * g ^ ((a-b)*(N-1)) := by
    simp only [rowAnchor, ← zpow_add]
    congr 1
    ring
  rw [h, Units.val_mul]
  ring

/-- Reciprocal trace cancellation preserves both target-one hits and
target-minus-one hits. It retains the product prefix as well as the
ratio; no unknown prime field or division by a nonunit is used. -/
theorem unit_trace_collision_factorization {K : Type*} [CommRing K]
    (x y : Kˣ) :
    ((x : K)^2 - 1) * ((y : K)^2 - 1) =
      ((x*y : Kˣ) : K) *
        (((x*y : Kˣ) : K) + (((x*y)⁻¹ : Kˣ) : K) -
          ((x/y : Kˣ) : K) - ((y/x : Kˣ) : K)) := by
  have hx : (x : K) * ((x⁻¹ : Kˣ) : K) = 1 := by simp
  have hy : (y : K) * ((y⁻¹ : Kˣ) : K) = 1 := by simp
  simp only [div_eq_mul_inv, mul_inv_rev, Units.val_mul]
  linear_combination
    -((y : K) * ((y⁻¹ : Kˣ) : K)) * hx - hy +
      ((x : K)^2) * hy + ((y : K)^2) * hx

/-- In either hidden prime field, the joined trace detects exactly the
union of the two rows' squared target-one collisions. It creates no
field collision except an existing target-one or target-minus-one hit. -/
theorem unit_trace_collision_iff {K : Type*} [CommRing K] [IsDomain K]
    (x y : Kˣ) :
    (((x*y : Kˣ) : K) + (((x*y)⁻¹ : Kˣ) : K) -
        ((x/y : Kˣ) : K) - ((y/x : Kˣ) : K) = 0) ↔
      (x : K)^2 = 1 ∨ (y : K)^2 = 1 := by
  have h := unit_trace_collision_factorization x y
  have hne : ((x*y : Kˣ) : K) ≠ 0 := Units.ne_zero _
  rw [← mul_eq_zero_iff_left hne, ← h, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- Cheap row-swap cancellation can destroy the only original hit.
The centre is the literal ceil(2 sqrt(77*1*2)), not a synthetic phase.
Neither the even nor the odd swapped channel replaces the target-one test. -/
theorem swap_cancellation_does_not_preserve_hit :
    24^2 < 4*77*1*2 ∧ 4*77*1*2 ≤ 25^2 ∧
      2^(1*77+2-25) % 77 = 71 ∧ 2^(2*77+1-25) % 77 = 23 ∧
      Nat.gcd 77 (71-1) = 7 ∧
      Nat.gcd 77 (71-23) = 1 ∧ Nat.gcd 77 (71+23) = 1 := by
  norm_num

end RiemannGaussian.SemiprimeRowStructure

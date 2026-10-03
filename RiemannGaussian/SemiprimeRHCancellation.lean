/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSquareProductCover
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Signed-product cancellation with the original row targets retained

The RH proof's `ZetaRieszPrimeFourier.divisorCharacter_eq_primeProduct`
uses signed subset expansion to replace a complete divisor character by
its Euler factors. Here the same finite ring algebra is applied to the
original collision differences. Its product retains every prime-field
collision; using row increments as the Euler factors tests something else.

Removing a row's centre phase preserves its collision only if the target
is rephased too. A mixed difference then has a small separable axis term
AND the exact mixed centre-power term. A kernel-checked semiprime control
shows that even retaining this latter term in a signed sum can erase an
original proper hit. The collision product keeps that hit.

These identities do not bound the cost of constructing the coupled centres
or computing the full collision product. They prove no factoring exponent.
-/

namespace RiemannGaussian.SemiprimeRHCancellation

open scoped BigOperators

/-- Original row differences, with their common target unchanged. -/
def collisionProduct {R ι : Type*} [CommRing R]
    (S : Finset ι) (r : ι → R) (t : R) : R := ∏ j ∈ S, (r j-t)

/-- The complete signed subset expansion retains every target factor.
It is a mathematical expansion, not an algorithm that enumerates subsets. -/
theorem collisionProduct_eq_subset_expansion {R ι : Type*} [CommRing R]
    [DecidableEq ι] (S : Finset ι) (r : ι → R) (t : R) :
    collisionProduct S r t =
      ∑ J ∈ S.powerset, (∏ j ∈ J, r j) * (-t)^((S \ J).card) := by
  classical
  simp only [collisionProduct, sub_eq_add_neg]
  rw [Finset.prod_add]
  simp only [Finset.prod_const]

/-- Over a hidden prime field the product detects exactly the union
of the original target collisions, including repeated row values. -/
theorem collisionProduct_map_zero_iff {R F ι : Type*} [CommRing R]
    [CommRing F] [IsDomain F] (φ : R →+* F)
    (S : Finset ι) (r : ι → R) (t : R) :
    φ (collisionProduct S r t) = 0 ↔ ∃ j ∈ S, φ (r j) = φ t := by
  classical
  simp only [collisionProduct, map_prod, map_sub, Finset.prod_eq_zero_iff, sub_eq_zero]

/-- The Euler-factor normalization removes only an invertible common
target. The factors are the original rows, not their phase increments. -/
theorem collisionProduct_eq_euler_product {R ι : Type*} [CommRing R]
    (S : Finset ι) (r : ι → R) (t : Rˣ) :
    collisionProduct S r (t : R) =
      (-(t : R))^S.card * ∏ j ∈ S, (1-r j*((t⁻¹ : Rˣ) : R)) := by
  have h (j : ι) : r j-(t : R) =
      (-(t : R))*(1-r j*((t⁻¹ : Rˣ) : R)) := by
    have ht : (t : R)*((t⁻¹ : Rˣ) : R)=1 := by simp
    linear_combination -(r j)*ht
  simp_rw [collisionProduct, h]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- Euler expansion collapses the complete signed subset character
to its listed atomic factors over any commutative ring. -/
theorem signedSubsetSum_eq_euler_product {R ι : Type*} [CommRing R]
    (S : Finset ι) (z : ι → R) :
    (∑ J ∈ S.powerset, (-1 : R)^J.card * ∏ j ∈ J, z j) =
      ∏ j ∈ S, (1-z j) := by
  classical
  have h := Finset.prod_one_add (f := fun j => -z j) S
  simpa only [sub_eq_add_neg, Finset.prod_neg] using h.symm

/-- The short signed-subset circuit vanishes exactly when an ATOMIC
factor equals one. It is not a test for an arbitrary original subset row. -/
theorem signedSubsetSum_zero_iff {R ι : Type*} [CommRing R] [IsDomain R]
    (S : Finset ι) (z : ι → R) :
    (∑ J ∈ S.powerset, (-1 : R)^J.card * ∏ j ∈ J, z j) = 0 ↔
      ∃ j ∈ S, z j = 1 := by
  classical
  rw [signedSubsetSum_eq_euler_product]
  simp only [Finset.prod_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro ⟨j, hj, he⟩
    exact ⟨j, hj, he.symm⟩
  · rintro ⟨j, hj, he⟩
    exact ⟨j, hj, he.symm⟩

/-- Multiplying every original difference by its own unit phase
retains its product up to one unit, without discarding a target channel. -/
theorem collisionProduct_rephase {R ι : Type*} [CommRing R]
    (S : Finset ι) (r : ι → R) (t : R) (u : ι → Rˣ) :
    (∏ j ∈ S, ((u j : R)*r j-(u j : R)*t)) =
      (∏ j ∈ S, (u j : R))*collisionProduct S r t := by
  simp only [← mul_sub, Finset.prod_mul_distrib, collisionProduct]

/-- Multiplication by a public unit preserves the entire GCD signal,
including prime powers and aggregate saturation, for every modulus. -/
theorem unit_mul_gcd_eq {n : ℕ} (u : (ZMod n)ˣ) (x : ZMod n) :
    n.gcd ((u : ZMod n)*x).val=n.gcd x.val := by
  rw [ZMod.val_mul]
  calc
    n.gcd ((u : ZMod n).val*x.val % n) =
        ((u : ZMod n).val*x.val % n).gcd n := Nat.gcd_comm _ _
    _ = n.gcd ((u : ZMod n).val*x.val) := (Nat.gcd_rec _ _).symm
    _ = n.gcd x.val := by
      rw [Nat.gcd_comm n _, Nat.gcd_comm n x.val]
      exact (ZMod.val_coe_unit_coprime u).gcd_mul_left_cancel x.val

/-- Applying the RH-style Euler normalization to the original row
differences preserves the exact GCD for every modulus, including squares.
There is no new assumption about the unknown local orders. -/
theorem collisionProduct_euler_gcd_eq {n : ℕ} {ι : Type*}
    (S : Finset ι) (r : ι → ZMod n) (t : (ZMod n)ˣ) :
    n.gcd (collisionProduct S r (t : ZMod n)).val=
      n.gcd (∏ j ∈ S, (1-r j*((t⁻¹ : (ZMod n)ˣ) : ZMod n))).val := by
  have he : (((-t)^S.card : (ZMod n)ˣ) : ZMod n)=(-(t : ZMod n))^S.card := by simp
  rw [collisionProduct_eq_euler_product, ← he]
  exact unit_mul_gcd_eq ((-t)^S.card) _

/-- Public centre normalization, with the same normalization applied
to the baby target. There is no hidden-prime input. -/
def rephasedResidual {R : Type*} [CommRing R]
    (g : Rˣ) (N a b c : ℤ) (t : R) : R :=
  ((g^(a*N+b) : Rˣ) : R)-t*((g^c : Rˣ) : R)

/-- Exact common-phase extraction retains the coupled centre power
in the transformed target. -/
theorem rephasedResidual_eq {R : Type*} [CommRing R]
    (g : Rˣ) (N a b c : ℤ) (t : R) :
    rephasedResidual g N a b c t =
      ((g^c : Rˣ) : R)*((SemiprimeRowStructure.rowAnchor (G := Rˣ) g N a b c : R)-t) := by
  have h : g^c*SemiprimeRowStructure.rowAnchor g N a b c=g^(a*N+b) := by
    simp only [SemiprimeRowStructure.rowAnchor, ← zpow_add]
    congr 1
    ring
  have hv := congrArg (fun x : Rˣ => (x : R)) h
  simp only [Units.val_mul] at hv
  unfold rephasedResidual
  rw [← hv]
  ring

/-- Rephasing preserves each individual collision over every nonzero
prime-field image. It does not authorize summing different residuals. -/
theorem rephasedResidual_map_zero_iff {R F : Type*} [CommRing R]
    [CommRing F] [IsDomain F] (φ : R →+* F)
    (g : Rˣ) (N a b c : ℤ) (t : R) :
    φ (rephasedResidual g N a b c t) = 0 ↔
      φ (SemiprimeRowStructure.rowAnchor (G := Rˣ) g N a b c : R) = φ t := by
  rw [rephasedResidual_eq, map_mul, map_sub]
  have hne : φ ((g^c : Rˣ) : R) ≠ 0 :=
    (Units.map φ.toMonoidHom (g^c)).ne_zero
  rw [mul_eq_zero_iff_left hne, sub_eq_zero]

/-- The target-preserving row normalization keeps the exact public GCD,
without a squarefree-modulus or hidden-prime assumption. -/
theorem rephasedResidual_gcd_eq {n : ℕ} (g : (ZMod n)ˣ)
    (N a b c : ℤ) (t : ZMod n) :
    n.gcd (rephasedResidual g N a b c t).val=
      n.gcd ((SemiprimeRowStructure.rowAnchor (G := (ZMod n)ˣ) g N a b c : ZMod n)-t).val := by
  rw [rephasedResidual_eq]
  exact unit_mul_gcd_eq (g^c) _

/-- The two-dimensional signed difference cancels the axis powers
into a short Euler product. The exact centre-power companion survives.
Even this complete signed value need not preserve an individual hit. -/
theorem rephasedResidual_mixed_difference {R : Type*} [CommRing R]
    (g : Rˣ) (N a b u v c00 c01 c10 c11 : ℤ) (t : R) :
    rephasedResidual g N a b c00 t-
      rephasedResidual g N a (b+v) c01 t-
      rephasedResidual g N (a+u) b c10 t+
      rephasedResidual g N (a+u) (b+v) c11 t =
      ((g^(a*N+b) : Rˣ) : R)*
        (((g^(u*N) : Rˣ) : R)-1)*(((g^v : Rˣ) : R)-1)-
      t*(((g^c00 : Rˣ) : R)-((g^c01 : Rˣ) : R)-
        ((g^c10 : Rˣ) : R)+((g^c11 : Rˣ) : R)) := by
  have h01 : g^(a*N+(b+v)) = g^(a*N+b)*g^v := by rw [← zpow_add]; congr 1; ring
  have h10 : g^((a+u)*N+b) = g^(a*N+b)*g^(u*N) := by rw [← zpow_add]; congr 1; ring
  have h11 : g^((a+u)*N+(b+v)) = g^(a*N+b)*g^(u*N)*g^v := by
    rw [← zpow_add, ← zpow_add]
    congr 1
    ring
  simp only [rephasedResidual, h01, h10, h11, Units.val_mul]
  ring

/-- A complete two-block divisor orbit has one common product centre.
Its signed multiplicative ratio removes that centre exactly, leaving
only an N+1 projected-period test. No factor of the input is supplied. -/
theorem rowAnchor_block_divisor_ratio {G : Type*} [CommGroup G]
    (g : G) (N r s c : ℤ) :
    (SemiprimeRowStructure.rowAnchor g N 1 (r*s) c*
        SemiprimeRowStructure.rowAnchor g N (r*s) 1 c)/
      (SemiprimeRowStructure.rowAnchor g N r s c*
        SemiprimeRowStructure.rowAnchor g N s r c) =
      g^((r-1)*(s-1)*(N+1)) := by
  simp only [SemiprimeRowStructure.rowAnchor, ← zpow_add]
  rw [div_eq_mul_inv, ← zpow_neg, ← zpow_add]
  congr 1
  ring

/-- The short common-centre orbit signal is precisely an order
divisibility condition, rather than the union of its original row hits. -/
theorem block_divisor_ratio_eq_one_iff {G : Type*} [CommGroup G]
    (g : G) (N r s c : ℤ) :
    (SemiprimeRowStructure.rowAnchor g N 1 (r*s) c*
        SemiprimeRowStructure.rowAnchor g N (r*s) 1 c)/
      (SemiprimeRowStructure.rowAnchor g N r s c*
        SemiprimeRowStructure.rowAnchor g N s r c) = 1 ↔
      (orderOf g : ℤ) ∣ (r-1)*(s-1)*(N+1) := by
  rw [rowAnchor_block_divisor_ratio, orderOf_dvd_iff_zpow_eq_one]

/-- Public positive-exponent form of the literal rephased row.
Exact integer square roots are used in its centre. -/
def literalResidual (N g a b i : ℕ) : ZMod N :=
  (g : ZMod N)^(a*N+b)-
    (g : ZMod N)^(SemiprimeLehmanCoverage.literalCentre N (a*b))*(g : ZMod N)^i

set_option maxRecDepth 32768 in
/-- A genuine offset-zero weighted row outside the small-factor
prefix has a proper GCD after rephasing. Its centre is literal. -/
theorem control_literal_row_hit :
    SemiprimeLehmanCoverage.literalCentre 3036046577 (12*17)=1573981 ∧
      12*65521+17*46337=1573981 ∧
      (literalResidual 3036046577 2 12 17 0).val=2754363954 ∧
      Nat.gcd 3036046577 (literalResidual 3036046577 2 12 17 0).val=46337 := by
  norm_num [literalResidual, SemiprimeLehmanCoverage.literalCentre,
    SemiprimeLehmanCoverage.ceilSqrt]
  reduce_mod_char
  norm_num [ZMod.val_ofNat]

set_option maxRecDepth 32768 in
/-- Keeping the centre companion in the signed four-corner sum still
loses the original proper hit. The centre-free axis product is also a unit. -/
theorem control_mixed_difference_misses :
    Nat.gcd 3036046577
      (literalResidual 3036046577 2 12 17 0-
        literalResidual 3036046577 2 12 19 0-
        literalResidual 3036046577 2 13 17 0+
        literalResidual 3036046577 2 13 19 0).val=1 ∧
      Nat.gcd 3036046577
        (((2 : ZMod 3036046577)^(12*3036046577+17))*
          ((2 : ZMod 3036046577)^3036046577-1)*((2 : ZMod 3036046577)^2-1)).val=1 := by
  norm_num [literalResidual, SemiprimeLehmanCoverage.literalCentre,
    SemiprimeLehmanCoverage.ceilSqrt]
  reduce_mod_char
  norm_num [ZMod.val_ofNat]

set_option maxRecDepth 32768 in
/-- The original four collision factors keep the proper prime signal
on the same exact block, before any signed-amplitude collapse. -/
theorem control_collision_product_preserves_hit :
    Nat.gcd 3036046577
      (literalResidual 3036046577 2 12 17 0*
        literalResidual 3036046577 2 12 19 0*
        literalResidual 3036046577 2 13 17 0*
        literalResidual 3036046577 2 13 19 0).val=46337 := by
  norm_num [literalResidual, SemiprimeLehmanCoverage.literalCentre,
    SemiprimeLehmanCoverage.ceilSqrt]
  reduce_mod_char
  norm_num [ZMod.val_ofNat]

/-- All four control rows are primitive and belong to the full
weight budget. The witness is not an artefact of a nonprimitive row. -/
theorem control_primitive_weight_budget :
    Nat.Coprime 12 17 ∧ Nat.Coprime 12 19 ∧
      Nat.Coprime 13 17 ∧ Nat.Coprime 13 19 ∧ 13*19 ≤ 39^2 := by norm_num

set_option maxRecDepth 32768 in
/-- The exact common-centre divisor cancellation can lose BOTH
proper prime signals on a genuine weighted-hit control. -/
theorem control_divisor_orbit_ratio_misses :
    Nat.gcd 3036046577
      (((2 : ZMod 3036046577)^((12-1)*(17-1)*(3036046577+1))-1).val)=1 ∧
      Nat.gcd 3036046577 (literalResidual 3036046577 2 17 12 0).val=65521 := by
  norm_num [literalResidual, SemiprimeLehmanCoverage.literalCentre,
    SemiprimeLehmanCoverage.ceilSqrt]
  reduce_mod_char
  norm_num [ZMod.val_ofNat]

end RiemannGaussian.SemiprimeRHCancellation

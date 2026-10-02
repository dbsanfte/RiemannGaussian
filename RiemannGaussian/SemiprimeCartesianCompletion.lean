/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRowStructure
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Root-preserving Cartesian batches and their centre boundary

Two root lists give an exact detector for every Cartesian pair. This does
not assert that the literal weighted centres separate into two lists.
The mixed centre increment quantifies the correction that must be retained.
The algebra is checked in the ordinary library and CI; numerical probes remain optional.
-/

namespace RiemannGaussian.SemiprimeCartesianCompletion

open scoped BigOperators
open Polynomial

/-- The small input polynomial, retaining every root with multiplicity. -/
noncomputable def rootPolynomial {R ι : Type*} [CommRing R] (A : Finset ι) (x : ι → R) : R[X] :=
  ∏ a ∈ A, (X-C (x a))

/-- A Cartesian root product is one resultant of two small polynomials.
No hidden prime, field inversion or pair list occurs in this identity. -/
theorem grid_resultant_eq {R ι κ : Type*} [CommRing R] [Nontrivial R]
    (A : Finset ι) (B : Finset κ) (x : ι → R) (y : κ → R) :
    (rootPolynomial A x).resultant (rootPolynomial B y) A.card B.card =
      ∏ a ∈ A, ∏ b ∈ B, (x a-y b) := by
  classical
  have hA : (rootPolynomial A x).natDegree = A.card :=
    natDegree_finsetProd_X_sub_C_eq_card A x
  have hB : (rootPolynomial B y).natDegree = B.card :=
    natDegree_finsetProd_X_sub_C_eq_card B y
  rw [← hA]
  unfold rootPolynomial
  rw [resultant_prod_left A (fun a => X-C (x a)) _ B.card
    (by simp) (by simpa only [rootPolynomial] using hB.le)]
  simp only [natDegree_X_sub_C]
  simp_rw [resultant_X_sub_C_left _ _ _ (by simpa only [rootPolynomial] using hB.le)]
  simp only [eval_prod, eval_sub, eval_X, eval_C]

/-- Over either hidden prime field, the entire Cartesian detector has
exactly the union of the original pair collisions as its zero set. -/
theorem grid_resultant_eq_zero_iff {R ι κ : Type*} [CommRing R] [IsDomain R]
    (A : Finset ι) (B : Finset κ) (x : ι → R) (y : κ → R) :
    (rootPolynomial A x).resultant (rootPolynomial B y) A.card B.card = 0 ↔
      ∃ a ∈ A, ∃ b ∈ B, x a=y b := by
  classical
  rw [grid_resultant_eq]
  simp only [Finset.prod_eq_zero_iff, sub_eq_zero]

/-- Separated integer centres yield exactly the two small root lists.
The equality is not licensed for a general square-root centre. -/
theorem rowAnchor_separatedCentre {G : Type*} [CommGroup G]
    (g : G) (N a b r c : ℤ) :
    SemiprimeRowStructure.rowAnchor g N a b (r+c) =
      g^(a*N-r) / g^(c-b) := by
  simp only [SemiprimeRowStructure.rowAnchor, div_eq_mul_inv, ← zpow_neg, ← zpow_add]
  congr 1
  ring

/-- Unrounded literal centre, written to expose its mixed increment. -/
noncomputable def realCentre (N a b : ℝ) : ℝ :=
  2*Real.sqrt N*Real.sqrt a*Real.sqrt b

/-- Exact integer centre. No floating-point rounding enters the theorem. -/
noncomputable def roundedCentre (N a b : ℝ) : ℤ := ⌈realCentre N a b⌉

/-- The literal square-root formula agrees with the separated square
roots under the original nonnegative input conditions. -/
theorem realCentre_eq_sqrt {N a b : ℝ} (hN : 0 ≤ N) (ha : 0 ≤ a) :
    realCentre N a b = Real.sqrt (4*N*a*b) := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ 4*N*a),
    Real.sqrt_mul (by positivity : 0 ≤ 4*N), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
  norm_num [realCentre]

/-- Centre curvature is a positive product of square-root increments.
It survives even on an adjacent four-corner block. -/
theorem realCentre_mixed_increment (N a b h : ℝ) :
    realCentre N a b + realCentre N (a+h) (b+h) -
      realCentre N a (b+h) - realCentre N (a+h) b =
      2*Real.sqrt N*(Real.sqrt (a+h)-Real.sqrt a)*
        (Real.sqrt (b+h)-Real.sqrt b) := by
  unfold realCentre
  ring

/-- A uniform square-root increment estimate on the actual weight box. -/
theorem sqrt_increment_lower {a h B : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hab : a+h ≤ B) :
    h ≤ 2*Real.sqrt B*(Real.sqrt (a+h)-Real.sqrt a) := by
  have hah : 0 ≤ a+h := by linarith
  have hB : 0 ≤ B := by linarith
  have hd : 0 ≤ Real.sqrt (a+h)-Real.sqrt a :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have he : (Real.sqrt (a+h)-Real.sqrt a)*
      (Real.sqrt (a+h)+Real.sqrt a)=h := by
    nlinarith [Real.sq_sqrt hah, Real.sq_sqrt ha]
  have hs : Real.sqrt (a+h)+Real.sqrt a ≤ 2*Real.sqrt B := by
    have h1 := Real.sqrt_le_sqrt hab
    have h2 := Real.sqrt_le_sqrt (show a ≤ B by linarith)
    linarith
  have hm := mul_le_mul_of_nonneg_left hs hd
  nlinarith

/-- Even a tiny block retains curvature on the sqrt(N)/B scale.
This is an integer-exponent completion bound, not a complexity lower
bound for every modular or resultant algorithm. -/
theorem realCentre_mixed_lower {N a b h B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hh : 0 ≤ h) (hB : 0 < B) (haB : a+h ≤ B) (hbB : b+h ≤ B) :
    Real.sqrt N*h^2/(2*B) ≤
      2*Real.sqrt N*(Real.sqrt (a+h)-Real.sqrt a)*
        (Real.sqrt (b+h)-Real.sqrt b) := by
  have h1 := sqrt_increment_lower ha hh haB
  have h2 := sqrt_increment_lower hb hh hbB
  have hd : 0 ≤ Real.sqrt (a+h)-Real.sqrt a :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hm := mul_le_mul h1 h2 hh (by positivity)
  have hm' : h^2 ≤ 4*B*(Real.sqrt (a+h)-Real.sqrt a)*
      (Real.sqrt (b+h)-Real.sqrt b) := by
    calc
      h^2 = h*h := by ring
      _ ≤ (2*Real.sqrt B*(Real.sqrt (a+h)-Real.sqrt a))*
          (2*Real.sqrt B*(Real.sqrt (b+h)-Real.sqrt b)) := hm
      _ = 4*(Real.sqrt B)^2*(Real.sqrt (a+h)-Real.sqrt a)*
          (Real.sqrt (b+h)-Real.sqrt b) := by ring
      _ = _ := by rw [Real.sq_sqrt hB.le]
  apply (div_le_iff₀ (by positivity : 0 < 2*B)).mpr
  have hmN := mul_le_mul_of_nonneg_left hm' (Real.sqrt_nonneg N)
  nlinarith

/-- Rounding changes the mixed increment by less than two. -/
theorem roundedCentre_mixed_gt (N a b h : ℝ) :
    2*Real.sqrt N*(Real.sqrt (a+h)-Real.sqrt a)*
        (Real.sqrt (b+h)-Real.sqrt b)-2 <
      (roundedCentre N a b : ℝ) + (roundedCentre N (a+h) (b+h) : ℝ) -
        (roundedCentre N a (b+h) : ℝ) - (roundedCentre N (a+h) b : ℝ) := by
  have h00 := Int.le_ceil (realCentre N a b)
  have h11 := Int.le_ceil (realCentre N (a+h) (b+h))
  have h01 := Int.ceil_lt_add_one (realCentre N a (b+h))
  have h10 := Int.ceil_lt_add_one (realCentre N (a+h) b)
  have he := realCentre_mixed_increment N a b h
  change _ < _+_-(Int.ceil (realCentre N a (b+h)) : ℝ)-
    (Int.ceil (realCentre N (a+h) b) : ℝ)
  simp only [roundedCentre]
  linarith

/-- The explicit curvature lower bound also holds for literal integer
centres, paying the full two-unit rounding boundary. -/
theorem roundedCentre_mixed_lower {N a b h B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hh : 0 ≤ h) (hB : 0 < B) (haB : a+h ≤ B) (hbB : b+h ≤ B) :
    Real.sqrt N*h^2/(2*B)-2 <
      (roundedCentre N a b : ℝ) + (roundedCentre N (a+h) (b+h) : ℝ) -
        (roundedCentre N a (b+h) : ℝ) - (roundedCentre N (a+h) b : ℝ) := by
  have hl := realCentre_mixed_lower (N := N) ha hb hh hB haB hbB
  have hr := roundedCentre_mixed_gt N a b h
  linarith

/-- Every additive row/column centre fit retains at least half the
mixed increment as the width of its literal correction interval. -/
theorem separated_correction_width {c00 c01 c10 c11 r0 r1 s0 s1 lo hi : ℝ}
    (h00 : lo ≤ c00-r0-s0) (h00' : c00-r0-s0 ≤ hi)
    (h01 : lo ≤ c01-r0-s1) (h01' : c01-r0-s1 ≤ hi)
    (h10 : lo ≤ c10-r1-s0) (h10' : c10-r1-s0 ≤ hi)
    (h11 : lo ≤ c11-r1-s1) (h11' : c11-r1-s1 ≤ hi) :
    |c00+c11-c01-c10| ≤ 2*(hi-lo) := by
  rw [abs_le]
  constructor <;> linarith

/-- In the sixth-root weight regime, even a step-two block cannot be
flattened using one correction interval of width at most B. This does
not rule out a sublinear algorithm for a longer interval or a different
root-preserving nonlinear completion. -/
theorem sixth_regime_correction_gt_budget {N a b B r0 r1 s0 s1 lo hi : ℝ}
    (hB : 4 ≤ B) (hN : (B-1)^6 ≤ N) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haB : a+2 ≤ B) (hbB : b+2 ≤ B)
    (h00 : lo ≤ (roundedCentre N a b : ℝ)-r0-s0)
    (h00' : (roundedCentre N a b : ℝ)-r0-s0 ≤ hi)
    (h01 : lo ≤ (roundedCentre N a (b+2) : ℝ)-r0-s1)
    (h01' : (roundedCentre N a (b+2) : ℝ)-r0-s1 ≤ hi)
    (h10 : lo ≤ (roundedCentre N (a+2) b : ℝ)-r1-s0)
    (h10' : (roundedCentre N (a+2) b : ℝ)-r1-s0 ≤ hi)
    (h11 : lo ≤ (roundedCentre N (a+2) (b+2) : ℝ)-r1-s1)
    (h11' : (roundedCentre N (a+2) (b+2) : ℝ)-r1-s1 ≤ hi) :
    B < hi-lo := by
  have hBp : 0 < B := by linarith
  have hs : (B-1)^3 ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hN]
  have hp : B+1 < (B-1)^3/B := by
    apply (lt_div_iff₀ hBp).mpr
    have hpos : 0 ≤ B^2*(B-4) := mul_nonneg (sq_nonneg B) (by linarith)
    nlinarith
  have hr : (B-1)^3/B ≤ Real.sqrt N/B :=
    div_le_div_of_nonneg_right hs hBp.le
  have hd := roundedCentre_mixed_lower (N := N) ha hb (by norm_num : (0:ℝ) ≤ 2)
    hBp haB hbB
  have he : Real.sqrt N*2^2/(2*B)-2=2*(Real.sqrt N/B-1) := by field_simp
  rw [he] at hd
  have hw := separated_correction_width h00 h00' h01 h01' h10 h10' h11 h11'
  have habs := le_abs_self ((roundedCentre N a b : ℝ)+
    (roundedCentre N (a+2) (b+2) : ℝ)-(roundedCentre N a (b+2) : ℝ)-
    (roundedCentre N (a+2) b : ℝ))
  linarith

set_option exponentiation.threshold 600 in
/-- Three exact edge centres do not license flattening the last centre.
All four weight pairs are primitive and in the balanced cone. Even the
two-unit omitted curvature can erase the proper original factor hit. -/
theorem flattening_can_erase_hit :
    Nat.Coprime 8 11 ∧ Nat.Coprime 8 13 ∧
      Nat.Coprime 10 11 ∧ Nat.Coprime 10 13 ∧
      164^2 < 4*77*8*11 ∧ 4*77*8*11 ≤ 165^2 ∧
      178^2 < 4*77*8*13 ∧ 4*77*8*13 ≤ 179^2 ∧
      184^2 < 4*77*10*11 ∧ 4*77*10*11 ≤ 185^2 ∧
      200^2 < 4*77*10*13 ∧ 4*77*10*13 ≤ 201^2 ∧
      179+185-165=199 ∧
      (2:ℕ)^(10*77+13-201)%77=15 ∧ (2:ℕ)^(10*77+13-199)%77=60 ∧
      Nat.gcd 77 (15-1)=7 ∧ Nat.gcd 77 (60-1)=1 := by
  norm_num [Nat.Coprime]

end RiemannGaussian.SemiprimeCartesianCompletion

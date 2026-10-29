/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1InverseIntegral

/-! # Original acquired D.5 linear-weight precision
The bound is derived from original grid integrality, the actual cached inverse,
actual taper/ceiling and proved D.10. No desired weight/precision cap is input.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1WeightPrecision
open scoped BigOperators
open Polynomial SemiprimeD1DyadicBounds SemiprimeD1InverseIntegral
  SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid
  SemiprimeD1JetRecoveryWeights SemiprimeD1HermiteNodes SemiprimeD1GridLevelSum
  SemiprimeJetArray

/-- Actual upper multiplicity bound h*u<=4M from the ORIGINAL ceiling expression. -/
theorem height_mul_le (M u : ℕ) (hM : u≤M) : height M u*u≤4*M := by
  have hd := Nat.div_mul_le_self (3*M+u-1) u
  change height M u*u≤3*M+u-1 at hd
  have hs : 3*M+u-1≤3*M+u := Nat.sub_le _ _
  omega

/-- Original q_t<=4M is derived for every original node, with no multiplicity advice. -/
theorem nodeMultiplicity_le (a M u t : ℕ) (hM : u≤M) : nodeMultiplicity a (height M u) u t≤4*M := by
  exact (Nat.mul_le_mul_left (height M u) (Nat.sub_le _ _)).trans (height_mul_le M u hM)

/-- Actual D.9 scalar evaluation argument -t/alpha. -/
def argument (a t : ℕ) : ℚ := -(point a t:ℚ)/((2:ℤ)^(a+1):ℚ)

/-- Scalar evaluation loses at most a+1 powers per retained degree, with zero handled explicitly. -/
theorem argument_bound (a t : ℕ) : AtLeast (-(a+1:ℤ)) (argument a t) := by
  by_cases ht : point a t=0
  · exact Or.inl (by simp [argument,ht])
  have htn : (point a t:ℚ)≠0 := by exact_mod_cast ht
  have hα : (((2:ℤ)^(a+1)):ℚ)≠0 := by positivity
  apply Or.inr
  rw [argument,padicValRat.div (neg_ne_zero.mpr htn) hα,padicValRat.neg,
    SemiprimeD1JetRecoveryGrid.int_valuation]
  have hn : padicValRat 2 ((((2:ℤ)^(a+1)):ℚ))=(a+1:ℤ) := by
    have htwo : padicValRat 2 (2:ℚ)=1 := padicValRat.self (p:=2) (by decide)
    simp only [Int.cast_ofNat,padicValRat.pow,htwo,mul_one,Nat.cast_add,Nat.cast_one]
  rw [hn]
  omega

/-- Every actually retained monomial has loss at most4M(a+1). -/
theorem retained_power (a M u t k : ℕ) (hM : u≤M)
    (hk : k<nodeMultiplicity a (height M u) u t) :
    AtLeast (-((4*M*(a+1):ℕ):ℤ)) ((argument a t)^k) := by
  have hq := nodeMultiplicity_le a M u t hM
  apply mono (SemiprimeD1DyadicBounds.pow (argument_bound a t) k)
  have ha : (0:ℤ)≤(a+1:ℤ) := by positivity
  have hk' : (k:ℤ)≤(4*M:ℕ) := by exact_mod_cast (show k≤4*M by omega)
  push_cast at hk' ⊢
  nlinarith

/-- Original scalar E_t0 loss plus evaluation loss; this is a computed numeric schedule. -/
def loss (a M u t : ℕ) : ℕ :=
  6*2^(a-padicValInt 2 (point a t))*height M u+4*M*(a+1)

/-- EXACT paper working precision, acquired from original data. -/
def precision (a M u p t : ℕ) : ℕ :=
  p+8*height M u*2^(a-padicValInt 2 (point a t))+8*M*(a+1)

/-- Every ACTUAL acquired weight has the required original lower valuation,
including zero weights. No inverse/output/weight bound is supplied. -/
theorem acquire_weight_bound (a M u : ℕ) (t : Fin (size a)) (hM : u≤M)
    (ht : point a t.val≠0) (hq : 0<nodeMultiplicity a (height M u) u t.val)
    (j : ℕ) (hj : j<nodeMultiplicity a (height M u) u t.val) :
    AtLeast (-(loss a M u t.val:ℤ)) (coefficient (acquire a (height M u) u t.val).weights j) := by
  rw [acquire_weight a (height M u) u t.val j hj]
  unfold localWeight
  have hi := acquire_inverse_integral a (height M u) u t hq
  have hs : AtLeast (-((4*M*(a+1):ℕ):ℤ))
      (∑k∈Finset.range (nodeMultiplicity a (height M u) u t.val),
        if j≤k then coefficient (acquire a (height M u) u t.val).inverse.coefficients (k-j)*
          (argument a t.val)^k else 0) := by
    apply SemiprimeD1DyadicBounds.sum
    intro k hk
    by_cases hjk : j≤k
    · simp only [hjk,ite_true]
      simpa only [zero_add] using mul (hi (k-j))
        (retained_power a M u t.val k hM (Finset.mem_range.mp hk))
    · simp only [hjk,ite_false]
      exact zero _
  have he : AtLeast (-(6:ℤ)*(2:ℤ)^(a-padicValInt 2 (point a t.val))*(height M u:ℤ))
      (Ezero a (height M u) u t.val) := Or.inr (original_D10_lower a M u t ht)
  have hm := mul he hs
  simpa only [loss,argument,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,neg_add_rev,
    mul_neg,neg_mul,add_comm] using hm

/-- The actual precision has more than the derived loss, uniformly for every original node. -/
theorem precision_covers (a M u p t : ℕ) : p+loss a M u t≤precision a M u p t := by
  have h1 : 6*2^(a-padicValInt 2 (point a t))*height M u≤
      8*height M u*2^(a-padicValInt 2 (point a t)) := by
    nlinarith [Nat.zero_le (height M u*2^(a-padicValInt 2 (point a t)))]
  have h2 : 4*M*(a+1)≤8*M*(a+1) := by nlinarith [Nat.zero_le (M*(a+1))]
  unfold loss precision
  omega

/-- Any permitted representative error, multiplied by its ACTUAL acquired weight,
retains the requested parent precision. -/
theorem weighted_error (a M u p : ℕ) (t : Fin (size a)) (hM : u≤M)
    (ht : point a t.val≠0) (hq : 0<nodeMultiplicity a (height M u) u t.val)
    (j : ℕ) (hj : j<nodeMultiplicity a (height M u) u t.val) (e : ℚ)
    (he : AtLeast (precision a M u p t.val:ℤ) e) :
    AtLeast (p:ℤ) (coefficient (acquire a (height M u) u t.val).weights j*e) := by
  apply mono (mul (acquire_weight_bound a M u t hM ht hq j hj) he)
  have hc : (p:ℤ)+(loss a M u t.val:ℤ)≤(precision a M u p t.val:ℤ) := by
    exact_mod_cast precision_covers a M u p t.val
  omega

end RiemannGaussian.SemiprimeD1WeightPrecision

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceInterpolationHeight
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Original polynomial binary heights of ALL source interpolation frames
The exponential magnitude envelopes remain proof-only. Their binary exponents
are explicit fixed polynomials in original dimensions, not new resources.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeSourceInterpolationBits
open scoped BigOperators
open SemiprimeReportPolynomialGrowth
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes SubexpRowInterpolation
open SemiprimeSourceInterpolationHeight SemiprimeSourceCodeArrayHeight
open SemiprimeJetArray SemiprimeJetArrayHeight SemiprimeSourceCodeArrays

/-- Binary exponent of the original shared constant denominator. -/
def leafDenominatorBits (Q R : ℕ) : ℕ := R+Nat.clog 2 Q*Q
/-- Binary exponent of all original source constants, including executed parity prescriptions. -/
def leafBits (A Q R : ℕ) : ℕ :=
  leafDenominatorBits Q R+Q+SemiprimeSourceUniversalHeight.entryExponent A Q R+2
/-- Tree size times original leaf height covers all recursively cached state. -/
def stateBits (A Q R : ℕ) : ℕ := (leafBits A Q R+R+7)*nodeCap Q
/-- Explicit fixed polynomial majorant, with logarithms bounded by ORIGINAL dimensions. -/
def polynomial (A Q R : ℕ) : ℕ :=
  (R+Q*Q+Q+(R*(A+(R+1)+1)+2*R+2*Q)+2+R+7)*(6*Q^2+8*Q+3)

/-- The denominator bound uses Q!, not an unjustified common multiple from mere height. -/
theorem leaf_denominator_dyadic (Q R : ℕ) :
    leafDenominator Q R ≤ 2^leafDenominatorBits Q R := by
  calc
    _ ≤ 2^R*2^(Nat.clog 2 Q*Q) := Nat.mul_le_mul
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le R 1)) (SemiprimeHermiteArrayHeight.factorial_dyadic Q)
    _ = _ := by rw [← pow_add];rfl

/-- Acquired prescription and integer sample bounds give the original leaf exponent. -/
theorem leaf_numerator_dyadic (A Q R : ℕ) : leafNumerator A Q R ≤ 2^leafBits A Q R := by
  let E := SemiprimeSourceUniversalHeight.entryExponent A Q R
  have hQ : Q ≤ 2^(Q+E) := (Nat.lt_two_pow_self (n:=Q)).le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have hE : 2^E ≤ 2^(Q+E) := Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
  have hone : 1 ≤ 2^(Q+E) := Nat.one_le_two_pow
  have hs : Q+2^E+1 ≤ 2^(Q+E+2) := by
    rw [show Q+E+2=(Q+E)+1+1 by omega,pow_succ,pow_succ]
    omega
  calc
    leafNumerator A Q R ≤ 2^leafDenominatorBits Q R*2^(Q+E+2) :=
      Nat.mul_le_mul (leaf_denominator_dyadic Q R) hs
    _ = _ := by rw [← pow_add];congr 1;unfold leafBits;omega

/-- A generic original-data compiler base has a linear binary exponent. -/
theorem base_dyadic (J d B b : ℕ) (hd : d ≤ 2^b) (hB : B ≤ 2^b) :
    base J d B ≤ 2^(b+J+6) := by
  have hJ : J+2 ≤ 2^(J+2) := (Nat.lt_two_pow_self (n:=J+2)).le
  have hone : 1 ≤ 2^b := Nat.one_le_two_pow
  have hs : 2*d+2*B+4 ≤ 2^(b+3) := by
    rw [show b+3=b+1+1+1 by omega,pow_succ,pow_succ,pow_succ]
    omega
  calc
    base J d B ≤ 2^(J+2)*2^(b+3) := Nat.mul_le_mul hJ hs
    _ = 2^((J+2)+(b+3))  := by rw [← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- Both shared full-tree magnitudes have an ORIGINAL polynomial-bit bound. -/
theorem common_caps_dyadic (A Q R : ℕ) :
    denominator Q R ≤ 2^stateBits A Q R ∧ numerator A Q R ≤ 2^stateBits A Q R := by
  have hd : leafDenominator Q R ≤ 2^leafBits A Q R :=
    (leaf_denominator_dyadic Q R).trans (Nat.pow_le_pow_right (by decide) (by unfold leafBits;omega))
  have hb := base_dyadic (R+1) (leafDenominator Q R) (leafNumerator A Q R)
    (leafBits A Q R) hd (leaf_numerator_dyadic A Q R)
  constructor
  · calc
      _ ≤ (2^leafBits A Q R)^nodeCap Q := Nat.pow_le_pow_left hd _
      _ = 2^(leafBits A Q R*nodeCap Q) := by rw [pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold stateBits; nlinarith)
  · calc
      _ ≤ (2^(leafBits A Q R+(R+1)+6))^nodeCap Q := Nat.pow_le_pow_left hb _
      _ = _ := by simp only [← pow_mul,stateBits,Nat.add_assoc]

/-- Any already-proved actual source frame representation gives reduced binary bounds. -/
theorem representation_binary_bounds {q : ℚ} (A Q R : ℕ)
    (hq : Representation q (denominator Q R) (numerator A Q R)) :
    q.den ≤ 2^stateBits A Q R ∧ q.num.natAbs ≤ 2^stateBits A Q R := by
  have hr := representation_reduced_bound (denominator_positive Q R) hq
  have hc := common_caps_dyadic A Q R
  exact ⟨hr.1.trans hc.1,hr.2.trans hc.2⟩

/-- Binary lengths follow at every actual subtree, not just the completed row. -/
theorem subtree_binary_bounds {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1)
    (p : PolynomialCode ℚ) (hp : Subcode p
      (SemiprimeSourceInterpolationExecution.code (SemiprimeBinomialExecution.parity A R) a 0 y))
    (i : ℕ) (hi : i<R+1) :
    (coefficient (compile (R+1) p).coefficients i).den ≤ 2^stateBits A Q R ∧
    (coefficient (compile (R+1) p).coefficients i).num.natAbs ≤ 2^stateBits A Q R :=
  representation_binary_bounds A Q R (code_subtree_bound A R a y p hp i hi)

/-- Every actual cached convolution dot-prefix has the original reduced binary cap. -/
theorem dotPrefix_binary_bounds {r Q : ℕ} (A R : ℕ) (a y : UniversalType r Q 1)
    (p q : PolynomialCode ℚ) (hpq : Subcode (.mul p q)
      (SemiprimeSourceInterpolationExecution.code (SemiprimeBinomialExecution.parity A R) a 0 y))
    (n len : ℕ) (hn : n<R+1) (hlen : len ≤ n) :
    (dotPrefix (compile (R+1) p).coefficients (compile (R+1) q).coefficients (n-1) len).value.den ≤ 2^stateBits A Q R ∧
    (dotPrefix (compile (R+1) p).coefficients (compile (R+1) q).coefficients (n-1) len).value.num.natAbs ≤ 2^stateBits A Q R :=
  representation_binary_bounds A Q R (code_dotPrefix_bound A R a y p q hpq n len hn hlen)

/-- Requested binary lengths are bounded directly from the shared original representation. -/
theorem representation_bit_lengths {q : ℚ} (A Q R : ℕ)
    (hq : Representation q (denominator Q R) (numerator A Q R)) :
    Nat.clog 2 (q.den+1) ≤ stateBits A Q R+1 ∧
    Nat.clog 2 (q.num.natAbs+1) ≤ stateBits A Q R+1 := by
  have h := representation_binary_bounds A Q R hq
  exact ⟨SemiprimeHermiteArrayHeight.clog_two_succ_of_dyadic h.1,
    SemiprimeHermiteArrayHeight.clog_two_succ_of_dyadic h.2⟩

/-- The explicit bit exponent is a fixed polynomial of original A,Q,R dimensions. -/
theorem stateBits_le_polynomial (A Q R : ℕ) : stateBits A Q R ≤ polynomial A Q R := by
  have hQ := SemiprimeHermiteArrayHeight.clog_two_le_self Q
  have hR := SemiprimeHermiteArrayHeight.clog_two_le_self (R+1)
  unfold stateBits leafBits leafDenominatorBits nodeCap SemiprimeSourceUniversalHeight.entryExponent SemiprimeSourceUniversalHeight.coefficientExponent polynomial
  gcongr

/-- Original dimension bounds preserve the fixed polynomial majorant. -/
theorem polynomial_mono {A Q R A' Q' R' : ℕ} (hA : A ≤ A') (hQ : Q ≤ Q') (hR : R ≤ R') :
    polynomial A Q R ≤ polynomial A' Q' R' := by unfold polynomial;gcongr

/-- Input-independent monomial witnesses describe the original binary-height polynomial. -/
theorem polynomial_monomial : SemiprimeReportPolynomialGrowth.Bound (fun S => polynomial S S S) := by
  unfold polynomial
  boundArithmetic

end RiemannGaussian.SemiprimeSourceInterpolationBits

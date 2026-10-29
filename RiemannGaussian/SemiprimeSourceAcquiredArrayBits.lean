/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceAcquiredArrayState
import RiemannGaussian.SemiprimeSourceInterpolationBits

/-! # Original-source array bit heights after every pullback sum
The source interpolation magnitudes can be exponential. Their bit lengths and
all original-coordinate accumulator bit lengths have fixed polynomial bounds.
No magnitude is silently treated as a polynomial resource.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeSourceAcquiredArrayBits
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes
open SemiprimeJetArray SemiprimeJetArrayHeight SemiprimeLocalExecutionHeight
open SemiprimeMaterializedSourcePullback SemiprimeSourceAcquiredArrayState
open SemiprimeSourceInterpolationHeight SemiprimeSourceInterpolationBits
open SemiprimeReportPolynomialGrowth

/-- The original row count contributes only an additional bounded bit exponent. -/
def bitExponent (M A Q R : ℕ) : ℕ := M+1+stateBits A Q R

/-- Even the envelope of every callback and returned pullback frame fits this dyadic cap. -/
theorem multiplied_caps (M A Q R : ℕ) :
    denominator Q R≤2^bitExponent M A Q R ∧
      (M+1)*numerator A Q R≤2^bitExponent M A Q R := by
  have hd := (common_caps_dyadic A Q R).1
  have hB := (common_caps_dyadic A Q R).2
  have hM : M+1≤2^(M+1) := Nat.le_of_lt (Nat.lt_two_pow_self)
  constructor
  · exact hd.trans (Nat.pow_le_pow_right (by decide : 0<2) (by unfold bitExponent; omega))
  · calc
      _ ≤ 2^(M+1)*2^stateBits A Q R := Nat.mul_le_mul hM hB
      _ = _ := by rw [← pow_add]; rfl

/-- All arrays at an original pullback frame have bounded reduced scalar fields. -/
theorem array_reduced_bounds (a : Array ℚ) (M A Q R : ℕ)
    (ha : ArrayBound a (R+1) (denominator Q R) ((M+1)*numerator A Q R))
    (k : ℕ) (hk : k<R+1) :
    (coefficient a k).den≤2^bitExponent M A Q R ∧
      (coefficient a k).num.natAbs≤2^bitExponent M A Q R := by
  have h := representation_reduced_bound (denominator_positive Q R) (ha k hk)
  have hc := multiplied_caps M A Q R
  exact ⟨h.1.trans hc.1,h.2.trans hc.2⟩

/-- Every actual source-row recursion suffix inherits the original polynomial exponent. -/
theorem original_suffix_binary {I : Type} [DecidableEq I] {n r Q : ℕ}
    (R : ℕ) (is : List I) (owner : I → Fin n) (as : Addresses I r Q)
    (keys : List (UniversalType r Q 1)) (i : I) (v : Fin n) (s k : ℕ) (hk : k<R+1) :
    let a := (sourceRow R (is.drop s) owner as keys
      (SemiprimeMaterializedSourceRows.acquire (centered r Q R) R keys).value i v).value
    (coefficient a k).den≤2^bitExponent is.length (centered r Q R) Q R ∧
      (coefficient a k).num.natAbs≤2^bitExponent is.length (centered r Q R) Q R := by
  apply array_reduced_bounds _ is.length (centered r Q R) Q R _ k hk
  exact arrayBound_mono (original_suffix_bound R is owner as keys i v s)
    (Nat.mul_le_mul_right _ (Nat.le_succ _))

/-- Literal original-input coefficient reads have the same bound, with no scale or array advice. -/
theorem original_read_binary {I E : Type} [Fintype I] [DecidableEq I] [DecidableEq E]
    {n r Q : ℕ} (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ)
    (i : I) (v : Fin n) (k : ℕ) (hk : k<R+1) :
    let q := coefficient (SemiprimeSourceArrayAcquisition.read en.incidences
      (SemiprimeMaterializedOriginalSource.acquire owner factor en eps R).value i v) k
    q.den≤2^bitExponent en.incidences.values.length (centered r Q R) Q R ∧
      q.num.natAbs≤2^bitExponent en.incidences.values.length (centered r Q R) Q R := by
  apply array_reduced_bounds _ en.incidences.values.length (centered r Q R) Q R _ k hk
  exact arrayBound_mono (original_read_bound owner factor en eps R i v)
    (Nat.mul_le_mul_right _ (Nat.le_succ _))

/-- Actual coefficient binary lengths, after original acquisition and immutable reads. -/
theorem original_read_bit_lengths {I E : Type} [Fintype I] [DecidableEq I] [DecidableEq E]
    {n r Q : ℕ} (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (eps : ℚ) (R : ℕ)
    (i : I) (v : Fin n) (k : ℕ) (hk : k<R+1) :
    let q := coefficient (SemiprimeSourceArrayAcquisition.read en.incidences
      (SemiprimeMaterializedOriginalSource.acquire owner factor en eps R).value i v) k
    Nat.clog 2 (q.den+1)≤bitExponent en.incidences.values.length (centered r Q R) Q R+1 ∧
      Nat.clog 2 (q.num.natAbs+1)≤bitExponent en.incidences.values.length (centered r Q R) Q R+1 := by
  have h := original_read_binary owner factor en eps R i v k hk
  exact ⟨SemiprimeHermiteArrayHeight.clog_two_succ_of_dyadic h.1,
    SemiprimeHermiteArrayHeight.clog_two_succ_of_dyadic h.2⟩

/-- Only original dimensions enter the fixed polynomial majorant of this bit exponent. -/
theorem bitExponent_le_polynomial (M A Q R : ℕ) :
    bitExponent M A Q R≤M+1+polynomial A Q R :=
  Nat.add_le_add_left (stateBits_le_polynomial A Q R) (M+1)

/-- A single original resource cap gives fixed monomial constants independent of the input. -/
theorem bitExponent_resource_bound :
    ∃ C k : ℕ, ∀ M A Q R S, M≤S → A≤S → Q≤S → R≤S →
      bitExponent M A Q R≤C*(S+1)^k := by
  have hp : SemiprimeReportPolynomialGrowth.Bound (fun S => S+1+polynomial S S S) := by
    unfold polynomial
    boundArithmetic
  obtain ⟨C,k,h⟩ := hp
  refine ⟨C,k,?_⟩
  intro M A Q R S hM hA hQ hR
  exact (bitExponent_le_polynomial M A Q R).trans
    ((Nat.add_le_add (Nat.add_le_add_right hM 1) (polynomial_mono hA hQ hR)).trans (h S))

end RiemannGaussian.SemiprimeSourceAcquiredArrayBits

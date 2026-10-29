/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HermiteDenominatorHeight

/-! # Original-derived polynomial dyadic envelopes for acquired cardinal/inverse arrays
The bounds are attached to actual canonical coefficients and inverse prefix
accumulators. They are bit-length/height results, not a complete primitive clock.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1HermiteDenominatorBits
open SemiprimeD1HermiteDenominatorHeight SemiprimeD1WireKernelOriginal
  SemiprimeD1JetRecoveryGrid SemiprimeD1JetRecoveryWeights SemiprimeD1TaperedLoss
  SemiprimeD1WeightPrecision SemiprimeJetArray SemiprimeJetArrayHeight

/-- Logarithmic denominator cap from actual original factor-list length. -/
def denominatorExponent (a h u t : ℕ) : ℕ := (a+1)*(slopes a h u t).length

/-- Logarithmic numerator cap of the actual retained original cardinal array. -/
def numeratorExponent (a h u t : ℕ) : ℕ :=
  (nodeMultiplicity a h u t+a+1)*(slopes a h u t).length

/-- Shared logarithmic cap for the ACTUAL inverse outputs and scalar-prefix accumulators. -/
def inverseExponent (a h u t : ℕ) : ℕ :=
  nodeMultiplicity a h u t*(nodeMultiplicity a h u t+denominatorExponent a h u t+
    numeratorExponent a h u t+3)

/-- Elementary native size bound used only to turn polynomial magnitudes into logarithms. -/
theorem self_le_two_power (n : ℕ) : n≤2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp : 1≤2^n := Nat.one_le_two_pow
    omega

/-- Actual product common denominator fits the original-derived dyadic envelope. -/
theorem denominator_bound (a h u : ℕ) (t : Fin (size a)) :
    sourceDenominator a h u t.val≤2^denominatorExponent a h u t.val := by
  have h := commonDenominator_le (size a) (slopes a h u t.val)
    (fun c hc => (original_slope_bounds a h u t c hc).1)
  simpa only [sourceDenominator,denominatorExponent,SemiprimeD1WireKernelOriginal.size,← pow_mul] using h

/-- Actual cardinal numerator bound has polynomial logarithm, not a recurrence tower. -/
theorem numerator_bound (a h u t : ℕ) : sourceNumerator a h u t≤2^numeratorExponent a h u t := by
  let q := nodeMultiplicity a h u t
  have hq : q≤2^q := self_le_two_power q
  have hb : q*size a≤2^(q+a+1) := by
    calc
      _ ≤ 2^q*size a := Nat.mul_le_mul_right _ hq
      _ = _ := by rw [SemiprimeD1WireKernelOriginal.size,← pow_add,Nat.add_assoc]
  have hp := Nat.pow_le_pow_left hb (slopes a h u t).length
  simpa only [sourceNumerator,numeratorExponent,q,← pow_mul] using hp

/-- Pure finite inverse-base arithmetic: polynomial logarithmic growth only. -/
theorem inverseBase_bound (J d B e f : ℕ) (hd : d≤2^e) (hB : B≤2^f) :
    inverseBase J d B≤2^(J+e+f+3) := by
  have he : 2^e≤2^(e+f) := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.le_add_right e f)
  have hf : 2^f≤2^(e+f) := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.le_add_left f e)
  have hp : 1≤2^(e+f) := Nat.one_le_two_pow
  have hJ : J≤2^J := self_le_two_power J
  have hs : d+B+1≤3*2^(e+f) := by omega
  have hm := Nat.mul_le_mul hJ hs
  have hone : 1≤2^J*2^(e+f) := by nlinarith [Nat.one_le_two_pow (n:=J),Nat.one_le_two_pow (n:=e+f)]
  unfold inverseBase
  rw [show J+e+f+3=J+(e+f)+3 by omega,pow_add,pow_add]
  norm_num
  nlinarith

/-- One shared original exponent covers both actual inverse common-denominator
and actual inverse common-numerator power bounds. -/
theorem inverse_power_bounds (a h u : ℕ) (t : Fin (size a)) :
    (sourceDenominator a h u t.val)^nodeMultiplicity a h u t.val≤2^inverseExponent a h u t.val ∧
    (inverseBase (nodeMultiplicity a h u t.val) (sourceDenominator a h u t.val)
      (sourceNumerator a h u t.val))^nodeMultiplicity a h u t.val≤2^inverseExponent a h u t.val := by
  have hd := denominator_bound a h u t
  have hB := numerator_bound a h u t.val
  have hb := inverseBase_bound (nodeMultiplicity a h u t.val) _ _ _ _ hd hB
  constructor
  · have hp := Nat.pow_le_pow_left hd (nodeMultiplicity a h u t.val)
    rw [← pow_mul] at hp
    exact hp.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by unfold inverseExponent;nlinarith))
  · have hp := Nat.pow_le_pow_left hb (nodeMultiplicity a h u t.val)
    simpa only [← pow_mul,inverseExponent,Nat.mul_comm] using hp

/-- ACTUAL normalized inverse output numerators/denominators have an explicit
polynomial-logarithm dyadic height, without an output-fit oracle. -/
theorem original_inverse_bits (a h u : ℕ) (t : Fin (size a))
    (hq : 0<nodeMultiplicity a h u t.val) (k : ℕ) (hk : k<nodeMultiplicity a h u t.val) :
    (coefficient (acquire a h u t.val).inverse.coefficients k).den≤2^inverseExponent a h u t.val ∧
    (coefficient (acquire a h u t.val).inverse.coefficients k).num.natAbs≤2^inverseExponent a h u t.val := by
  have hr := representation_reduced_bound (pow_pos (sourceDenominator_pos _ _ _ _) _)
    (original_inverse_representation a h u t hq k hk)
  have hb := inverse_power_bounds a h u t
  exact ⟨hr.1.trans hb.1,hr.2.trans hb.2⟩

/-- EVERY actual inverse partial scalar accumulator has the same dyadic cap. -/
theorem original_inverse_prefix_bits (a h u : ℕ) (t : Fin (size a)) (n len : ℕ)
    (hn : n+1<nodeMultiplicity a h u t.val) (hlen : len≤n+1) :
    (dotPrefix (acquire a h u t.val).denominator.coefficients
      (SemiprimeJetArray.inverse (acquire a h u t.val).denominator.coefficients (n+1)).coefficients n len).value.den≤
        2^inverseExponent a h u t.val ∧
    (dotPrefix (acquire a h u t.val).denominator.coefficients
      (SemiprimeJetArray.inverse (acquire a h u t.val).denominator.coefficients (n+1)).coefficients n len).value.num.natAbs≤
        2^inverseExponent a h u t.val := by
  have hh := original_inverse_dot_heights a h u t n len hn hlen
  have hp := inverse_power_bounds a h u t
  have hd : 0<sourceDenominator a h u t.val := sourceDenominator_pos _ _ _ _
  have hb : 0< inverseBase (nodeMultiplicity a h u t.val) (sourceDenominator a h u t.val)
      (sourceNumerator a h u t.val) := by unfold inverseBase;positivity
  exact ⟨hh.1.trans ((Nat.pow_le_pow_right hd (Nat.le_of_lt hn)).trans hp.1),
    hh.2.trans ((Nat.pow_le_pow_right hb (Nat.le_of_lt hn)).trans hp.2)⟩

/-- Fixed ORIGINAL-dimension polynomial envelope; size=2L is an acquired grid dimension. -/
def inverseEnvelope (a M : ℕ) : ℕ :=
  4*M*(4*M+4*(a+1)*size a*M+4*(4*M+a+1)*size a*M+3)

/-- Original schedule substitution proves the shared exponent is a FIXED polynomial
in a,M,2L, not an unproved polynomial-cost premise. -/
theorem original_inverseExponent_le (a M u t : ℕ) (hM : u≤M) :
    inverseExponent a (height M u) u t≤ inverseEnvelope a M := by
  have hq := nodeMultiplicity_le a M u t hM
  have hT := original_slopes_length a (height M u) u t
  have hhu := height_mul_le M u hM
  have hT' : (slopes a (height M u) u t).length≤4*size a*M := by
    nlinarith [Nat.mul_le_mul_left (size a) hhu]
  unfold inverseExponent denominatorExponent numeratorExponent inverseEnvelope
  calc
    _ ≤ 4*M*(4*M+(a+1)*(4*size a*M)+(4*M+a+1)*(4*size a*M)+3) := by gcongr
    _ = _ := by ring

end RiemannGaussian.SemiprimeD1HermiteDenominatorBits

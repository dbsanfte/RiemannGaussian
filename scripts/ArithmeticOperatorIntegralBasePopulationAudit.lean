/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorTotalTraceSourceAudit
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Actual fixed signed cyclotomic products have finite integral-base populations

The numerator and denominator are literal disjoint cyclotomic products over
the integers. Their actual resultant is nonzero. A negative order exponent
forces every integral base b>=2 to satisfy b<=abs(resultant). Nothing here
is uniform in moving exponent arrays, order bands or resultants; no source
or prime-power phase transport is asserted.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace OpenAIReview.IntegralBasePopulation
open TotalTraceSource

/-- Actual numerator polynomial after splitting the signed exponents. -/
def numerator (M : ℕ) (beta : ℕ → ℤ) : Polynomial ℤ :=
  ∏ e ∈ Finset.Icc 2 M, Polynomial.cyclotomic e ℤ ^ (beta e).toNat

/-- Actual denominator polynomial after splitting the signed exponents. -/
def denominator (M : ℕ) (beta : ℕ → ℤ) : Polynomial ℤ :=
  ∏ e ∈ Finset.Icc 2 M, Polynomial.cyclotomic e ℤ ^ (-beta e).toNat

/-- The actual integer resultant at the actual polynomial degrees. -/
def obstruction (M : ℕ) (beta : ℕ → ℤ) : ℤ :=
  Polynomial.resultant (numerator M beta) (denominator M beta)

/-- The actual denominator is monic, including an empty product. -/
theorem denominator_monic (M : ℕ) (beta : ℕ → ℤ) : (denominator M beta).Monic := by
  exact Polynomial.monic_prod_of_monic _ _ fun e _ => (Polynomial.cyclotomic.monic e ℤ).pow _

/-- Positive evaluated numerator at each permitted common base. -/
theorem numerator_eval_pos (M b : ℕ) (beta : ℕ → ℤ) (hb : 2 ≤ b) :
    0 < (numerator M beta).eval (b : ℤ) := by
  simp only [numerator, Polynomial.eval_prod, Polynomial.eval_pow]
  exact Finset.prod_pos fun e _ => pow_pos (value_pos b e hb) _

/-- Positive evaluated denominator at each permitted common base. -/
theorem denominator_eval_pos (M b : ℕ) (beta : ℕ → ℤ) (hb : 2 ≤ b) :
    0 < (denominator M beta).eval (b : ℤ) := by
  simp only [denominator, Polynomial.eval_prod, Polynomial.eval_pow]
  exact Finset.prod_pos fun e _ => pow_pos (value_pos b e hb) _

/-- Actual signed cyclotomic powers equal this evaluated rational quotient. -/
theorem signedProduct_eq_quotient (M b : ℕ) (beta : ℕ → ℤ) (hb : 2 ≤ b) :
    signedProduct b M beta =
      (((numerator M beta).eval (b : ℤ) : ℤ) : ℚ) /
        (((denominator M beta).eval (b : ℤ) : ℤ) : ℚ) := by
  simp only [signedProduct, numerator, denominator, Polynomial.eval_prod,
    Polynomial.eval_pow, Int.cast_prod, Int.cast_pow]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro e _
  have hn : (value b e : ℚ) ≠ 0 := by exact_mod_cast (value_pos b e hb).ne'
  change (value b e : ℚ) ^ beta e =
    (value b e : ℚ) ^ (beta e).toNat / (value b e : ℚ) ^ (-beta e).toNat
  conv_lhs => rw [← (beta e).toNat_sub_toNat_neg]
  rw [zpow_sub₀ hn, zpow_natCast, zpow_natCast]

/-- Rational integrality is precisely actual integer denominator divisibility. -/
theorem integral_iff_denominator_dvd (M b : ℕ) (beta : ℕ → ℤ) (hb : 2 ≤ b) :
    (∃ z : ℤ, signedProduct b M beta = (z : ℚ)) ↔
      (denominator M beta).eval (b : ℤ) ∣ (numerator M beta).eval (b : ℤ) := by
  rw [signedProduct_eq_quotient M b beta hb]
  have hn : (((denominator M beta).eval (b : ℤ) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (denominator_eval_pos M b beta hb).ne'
  constructor
  · rintro ⟨z, hz⟩
    have he := (div_eq_iff hn).mp hz
    have hi : (numerator M beta).eval (b : ℤ) = z * (denominator M beta).eval (b : ℤ) :=
      by exact_mod_cast he
    exact ⟨z, by simpa [mul_comm] using hi⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, (div_eq_iff hn).mpr ?_⟩
    exact_mod_cast (by simpa [mul_comm] using hz :
      (numerator M beta).eval (b : ℤ) = z * (denominator M beta).eval (b : ℤ))

/-- The two actual integer polynomials are coprime over Q, not necessarily over Z. -/
theorem rational_coprime (M : ℕ) (beta : ℕ → ℤ) :
    IsCoprime ((numerator M beta).map (Int.castRingHom ℚ))
      ((denominator M beta).map (Int.castRingHom ℚ)) := by
  simp only [numerator, denominator, Polynomial.map_prod, Polynomial.map_pow,
    Polynomial.map_cyclotomic]
  apply IsCoprime.prod_left
  intro e _
  apply IsCoprime.prod_right
  intro f _
  by_cases hef : e = f
  · subst f
    by_cases he : 0 ≤ beta e
    · have hh : (-beta e).toNat = 0 := by omega
      simpa only [hh, pow_zero] using
        (isCoprime_one_right : IsCoprime (Polynomial.cyclotomic e ℚ ^ (beta e).toNat) 1)
    · have hh : (beta e).toNat = 0 := by omega
      simpa only [hh, pow_zero] using
        (isCoprime_one_left : IsCoprime 1 (Polynomial.cyclotomic e ℚ ^ (-beta e).toNat))
  · exact (Polynomial.cyclotomic.isCoprime_rat hef).pow

/-- The fixed actual resultant is nonzero, with no assumed Bezout certificate. -/
theorem obstruction_ne_zero (M : ℕ) (beta : ℕ → ℤ) : obstruction M beta ≠ 0 := by
  have h := Polynomial.resultant_ne_zero _ _ (rational_coprime M beta)
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  rw [Polynomial.natDegree_map_eq_of_injective hi,
    Polynomial.natDegree_map_eq_of_injective hi,
    Polynomial.resultant_map_map] at h
  intro hz
  apply h
  simpa [obstruction, hz]

/-- A negative exponent supplies an actual cyclotomic divisor of the denominator. -/
theorem negative_factor_dvd (M d : ℕ) (beta : ℕ → ℤ)
    (hd : d ∈ Finset.Icc 2 M) (hneg : beta d < 0) :
    Polynomial.cyclotomic d ℤ ∣ denominator M beta := by
  have hp : 0 < (-beta d).toNat := by omega
  exact (dvd_pow_self _ hp.ne').trans (Finset.dvd_prod_of_mem _ hd)

/-- A negative exponent makes the actual denominator nonconstant. -/
theorem denominator_degree_pos (M d : ℕ) (beta : ℕ → ℤ)
    (hd : d ∈ Finset.Icc 2 M) (hneg : beta d < 0) :
    0 < (denominator M beta).natDegree := by
  have h := Polynomial.natDegree_le_of_dvd (negative_factor_dvd M d beta hd hneg)
    (denominator_monic M beta).ne_zero
  rw [Polynomial.natDegree_cyclotomic] at h
  have hp : 0 < d.totient := Nat.totient_pos.mpr (by have := (Finset.mem_Icc.mp hd).1; omega)
  omega

/-- Evaluation of the actual resultant Bezout identity bounds every integral denominator. -/
theorem denominator_dvd_obstruction (M b d : ℕ) (beta : ℕ → ℤ)
    (hb : 2 ≤ b) (hd : d ∈ Finset.Icc 2 M) (hneg : beta d < 0)
    (hint : ∃ z : ℤ, signedProduct b M beta = (z : ℚ)) :
    (denominator M beta).eval (b : ℤ) ∣ obstruction M beta := by
  have hBA := (integral_iff_denominator_dvd M b beta hb).mp hint
  obtain ⟨u, v, _, _, huv⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    (numerator M beta) (denominator M beta) le_rfl le_rfl
      (Or.inr (denominator_degree_pos M d beta hd hneg).ne')
  have he := congrArg (Polynomial.eval (b : ℤ)) huv
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at he
  unfold obstruction
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_left hBA _) (dvd_mul_right _ _)

/-- A literal cyclotomic value at order>=2 is at least the integer base. -/
theorem base_le_value (b d : ℕ) (hb : 2 ≤ b) (hd : 2 ≤ d) : (b : ℤ) ≤ value b d := by
  have hbr : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hphi : d.totient ≠ 0 := (Nat.totient_pos.mpr (show 0 < d by omega)).ne'
  have hp : (b : ℝ) - 1 ≤ ((b : ℝ) - 1) ^ d.totient :=
    le_self_pow₀ (by exact_mod_cast (show (1 : ℤ) ≤ (b : ℤ) - 1 by omega)) hphi
  have hc := Polynomial.sub_one_pow_totient_lt_cyclotomic_eval hd hbr
  have he : ((value b d : ℤ) : ℝ) = (Polynomial.cyclotomic d ℝ).eval (b : ℝ) := by
    simpa [value] using (Polynomial.cyclotomic.eval_apply (b : ℤ) d
      (Int.castRingHom ℝ)).symm
  rw [← he] at hc
  have hh : (b : ℝ) - 1 < (value b d : ℝ) := hp.trans_lt hc
  have hi : (b : ℤ) - 1 < value b d := by exact_mod_cast hh
  omega

/-- Every integral base is bounded by the absolute value of ONE fixed nonzero
actual resultant. This is uniform in b only while M and beta stay fixed. -/
theorem integral_base_bound (M b d : ℕ) (beta : ℕ → ℤ)
    (hb : 2 ≤ b) (hd : d ∈ Finset.Icc 2 M) (hneg : beta d < 0)
    (hint : ∃ z : ℤ, signedProduct b M beta = (z : ℚ)) :
    b ≤ (obstruction M beta).natAbs := by
  have hB := denominator_eval_pos M b beta hb
  have hv : value b d ∣ (denominator M beta).eval (b : ℤ) :=
    Polynomial.eval_dvd (negative_factor_dvd M d beta hd hneg)
  have hle : (b : ℤ) ≤ (denominator M beta).eval (b : ℤ) :=
    (base_le_value b d hb (Finset.mem_Icc.mp hd).1).trans (Int.le_of_dvd hB hv)
  have hR := Int.natAbs_le_of_dvd_ne_zero
    (denominator_dvd_obstruction M b d beta hb hd hneg hint) (obstruction_ne_zero M beta)
  have hle' : b ≤ ((denominator M beta).eval (b : ℤ)).natAbs := by
    exact_mod_cast (hle.trans Int.le_natAbs)
  exact hle'.trans hR

/-- A fixed finite signed exponent array with a negative entry is integral at only
finitely many actual integer bases b>=2. -/
theorem finite_integral_bases (M : ℕ) (beta : ℕ → ℤ)
    (hneg : ∃ d ∈ Finset.Icc 2 M, beta d < 0) :
    {b : ℕ | 2 ≤ b ∧ ∃ z : ℤ, signedProduct b M beta = (z : ℚ)}.Finite := by
  obtain ⟨d, hd, hn⟩ := hneg
  apply (Finset.finite_toSet (Finset.Icc 2 (obstruction M beta).natAbs)).subset
  intro b hb
  exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr
    ⟨hb.1, integral_base_bound M b d beta hb.1 hd hn hb.2⟩)

/-- Unbounded integral-base populations force every supported exponent nonnegative. -/
theorem nonnegative_of_unbounded_integral_bases (M : ℕ) (beta : ℕ → ℤ)
    (hpop : ∀ R : ℕ, ∃ b : ℕ, R < b ∧ 2 ≤ b ∧
      ∃ z : ℤ, signedProduct b M beta = (z : ℚ)) :
    ∀ d ∈ Finset.Icc 2 M, 0 ≤ beta d := by
  intro d hd
  by_contra hn
  have hneg : beta d < 0 := by omega
  obtain ⟨b, hbR, hb, hint⟩ := hpop (obstruction M beta).natAbs
  have := integral_base_bound M b d beta hb hd hneg hint
  omega

/-- Nonnegative supported exponents make the actual denominator identically one. -/
theorem denominator_eq_one (M : ℕ) (beta : ℕ → ℤ)
    (hbeta : ∀ d ∈ Finset.Icc 2 M, 0 ≤ beta d) : denominator M beta = 1 := by
  unfold denominator
  apply Finset.prod_eq_one
  intro d hd
  have h := hbeta d hd
  have hh : (-beta d).toNat = 0 := by omega
  simp [hh]

/-- The converse retains the literal rational product and its integer evaluation. -/
theorem integral_at_every_base (M b : ℕ) (beta : ℕ → ℤ) (hb : 2 ≤ b)
    (hbeta : ∀ d ∈ Finset.Icc 2 M, 0 ≤ beta d) :
    ∃ z : ℤ, signedProduct b M beta = (z : ℚ) := by
  refine ⟨(numerator M beta).eval (b : ℤ), ?_⟩
  rw [signedProduct_eq_quotient M b beta hb, denominator_eq_one M beta hbeta]
  simp

/-- Exact fixed-array classification of unbounded integral-base populations.
The quantifier order keeps the exponent array fixed before the bases vary. -/
theorem unbounded_integral_bases_iff (M : ℕ) (beta : ℕ → ℤ) :
    (∀ R : ℕ, ∃ b : ℕ, R < b ∧ 2 ≤ b ∧
      ∃ z : ℤ, signedProduct b M beta = (z : ℚ)) ↔
      ∀ d ∈ Finset.Icc 2 M, 0 ≤ beta d := by
  constructor
  · exact nonnegative_of_unbounded_integral_bases M beta
  · intro hbeta R
    refine ⟨R + 2, by omega, by omega, ?_⟩
    exact integral_at_every_base M (R + 2) beta (by omega) hbeta

end OpenAIReview.IntegralBasePopulation

#lint+ in OpenAIReview.IntegralBasePopulation

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    details := details.push (Json.mkObj [("declaration", toJson n.toString),
      ("isTheorem", toJson ci.isTheorem), ("axioms", toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty actual integral-base audit."
  logInfo m!"Integral-base audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-integral-base-population-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-integral-base-population-gate/axioms.json"
    (Json.mkObj [("scope", toJson "actual fixed finite signed cyclotomic product: fixed nonzero resultant, explicit base bound and finite integral-base population; moving coefficients and source excluded"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty

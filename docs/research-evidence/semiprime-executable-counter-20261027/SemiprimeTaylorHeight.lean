/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceRowHeight
import RiemannGaussian.SemiprimeJetArrayHeight

/-!
# Actual row Taylor coefficients with a fixed denominator

Integer shifts preserve the native rows' common denominator. Their numerator
growth is bounded in terms of the row degree and node magnitude, rather than
the number of terms used to construct a row.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeTaylorHeight
open Polynomial
open scoped BigOperators
open RiemannGaussian.SemiprimeJetArrayHeight
open RiemannGaussian.SemiprimeSourceRowHeight
open RiemannGaussian.SemiprimeSourceLayout

/-- A deliberately generous coefficient envelope for an integer shift. -/
def shiftBound (R B T : ℕ) : ℕ := (R+1) * B * (2*(T+1))^R

theorem integer_taylor_formula (p : Polynomial ℤ) (R : ℕ) (hp : p.natDegree ≤ R)
    (t : ℤ) (k : ℕ) :
    (taylor t p).coeff k = ∑ i ∈ Finset.range (R+1),
      (i.choose k : ℤ) * p.coeff i * t^(i-k) := by
  rw [taylor_coeff]
  conv_lhs => rw [p.as_sum_range' (R+1) (by omega)]
  simp only [map_sum, hasseDeriv_monomial, eval_finsetSum, eval_monomial]

/-- Every coefficient of the actual integer Taylor polynomial is bounded. -/
theorem integer_taylor_bound (p : Polynomial ℤ) (R B T : ℕ)
    (hp : p.natDegree ≤ R) (hb : ∀ k, |p.coeff k| ≤ (B : ℤ))
    (t : ℤ) (ht : |t| ≤ (T : ℤ)) (k : ℕ) :
    |(taylor t p).coeff k| ≤ (shiftBound R B T : ℤ) := by
  rw [integer_taylor_formula p R hp]
  have hterm (i : ℕ) (hi : i ∈ Finset.range (R+1)) :
      |(i.choose k : ℤ) * p.coeff i * t^(i-k)| ≤ (B * (2*(T+1))^R : ℕ) := by
    have hiR : i ≤ R := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    have hc : (i.choose k : ℤ) ≤ (2:ℤ)^R := by
      exact_mod_cast (Nat.choose_le_two_pow i k).trans (Nat.pow_le_pow_right (by decide) hiR)
    have ht' : |t|^(i-k) ≤ ((T+1 : ℕ) : ℤ)^R := by
      calc
        _ ≤ ((T+1 : ℕ) : ℤ)^(i-k) := by gcongr; omega
        _ ≤ ((T+1 : ℕ) : ℤ)^R := by
          apply pow_le_pow_right₀ (by omega)
          omega
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by positivity : (0:ℤ) ≤ i.choose k)]
    calc
      _ ≤ (2:ℤ)^R * (B:ℤ) * ((T+1 : ℕ) : ℤ)^R := by gcongr; exact hb i
      _ = _ := by push_cast; rw [mul_pow]; ring
  calc
    _ ≤ ∑ i ∈ Finset.range (R+1), |(i.choose k : ℤ) * p.coeff i * t^(i-k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (R+1), ((B * (2*(T+1))^R : ℕ) : ℤ) := Finset.sum_le_sum hterm
    _ = _ := by simp [shiftBound]; ring

/-- Taylor shift commutes with the literal denominator-clearing identity. -/
theorem map_taylor_cleared (P : Polynomial ℤ) (p : Polynomial ℚ) (d : ℕ)
    (hP : P.map (Int.castRingHom ℚ) = C (d : ℚ) * p) (t : ℤ) :
    (taylor t P).map (Int.castRingHom ℚ) = C (d : ℚ) * taylor (t : ℚ) p := by
  rw [taylor_apply, Polynomial.map_comp, hP]
  simp only [mul_comp, C_comp, Polynomial.map_add, map_X, map_C, taylor_apply]
  rfl

/-- This supplies the actual input-height premise of cached jet arithmetic. -/
theorem taylor_representation (P : Polynomial ℤ) (p : Polynomial ℚ) (d R B T : ℕ)
    (hd : 0 < d) (hP : P.map (Int.castRingHom ℚ) = C (d : ℚ) * p)
    (hp : P.natDegree ≤ R) (hb : ∀ k, |P.coeff k| ≤ (B : ℤ))
    (t : ℤ) (ht : |t| ≤ (T : ℤ)) (k : ℕ) :
    Representation ((taylor (t : ℚ) p).coeff k) d (shiftBound R B T) := by
  refine ⟨(taylor t P).coeff k, ?_, ?_⟩
  · have he := congrArg (fun q : Polynomial ℚ => q.coeff k) (map_taylor_cleared P p d hP t)
    simp only [coeff_map, coeff_C_mul] at he
    change (((taylor t P).coeff k : ℤ) : ℚ) = _ at he
    apply (eq_div_iff (by exact_mod_cast Nat.ne_of_gt hd)).mpr
    rw [he, mul_comm]
  · have h := integer_taylor_bound P R B T hp hb t ht k
    have h' : (((taylor t P).coeff k).natAbs : ℤ) ≤ (shiftBound R B T : ℤ) := by
      simpa only [Int.natCast_natAbs] using h
    exact_mod_cast h'

/-- No native row-height hypothesis: the constructor supplies the common
denominator, bounded integer numerator, and row degree used by this theorem. -/
theorem builtLayout_taylor_representation {I V E : Type} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] [DecidableEq E]
    {r Q : ℕ} (owner : I → V) (factor : I → E)
    (en : Enumerations I V E r Q) (ε : ℚ) (R B T : ℕ)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (i : I) (v : V) (t : ℤ) (ht : |t| ≤ (T : ℤ)) (k : ℕ) :
    Representation ((taylor (t : ℚ) ((builtLayout owner factor en ε R).row i v)).coeff k)
      (rowDenominator Q R) (shiftBound R (B * 2^rowNumeratorExponent Q R) T) := by
  obtain ⟨P, hP, hp, hb⟩ := builtLayout_row_representation owner factor en ε R B howner hQ hAQ i v
  exact taylor_representation P _ _ R _ T (rowDenominator_pos Q R) hP hp hb t ht k

end RiemannGaussian.SemiprimeTaylorHeight

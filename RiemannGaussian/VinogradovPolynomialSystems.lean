/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPolynomialRigidity
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Polynomial systems for classical Vinogradov differencing

The active part of a type `(d,T)` system has degrees `1,...,m`, where
the full degree is `d+m`. The omitted first `d` polynomial coordinates are
zero; this indexing convention does not discard the low-degree equations
of the separate monomial tail in the conditioning counts.

Translation and a literal finite difference preserve the required type,
including its common power of two and exact multiplier `T`. Their complete
moments and prime-power fibres inherit the existing bounds. These results
do not assume or prove the analytic conditioning/differencing inequality.
-/

namespace RiemannGaussian.VinogradovPolynomialSystems
noncomputable section
open scoped BigOperators
open Polynomial VinogradovPolynomialRigidity VinogradovMeanValue

/-- The active polynomials of Ford's type `(d,T)`, with the common binary
exponent exposed. Active index `j` is full degree `d+j+1`. -/
def HasType {m : ℕ} (F : Fin m → ℤ[X]) (d T e : ℕ) : Prop :=
  ∀ j, (F j).natDegree = j.val + 1 ∧
    (F j).leadingCoeff = ((d + j.val + 1).descFactorial d : ℤ) * 2 ^ e * T

/-- The exact polynomial finite difference, before taking any norm. -/
def difference (h : ℤ) (f : ℤ[X]) : ℤ[X] := taylor h f - f

/-- Evaluation agrees with the original shifted phase difference. -/
theorem difference_eval (h x : ℤ) (f : ℤ[X]) :
    (difference h f).eval x = f.eval (x + h) - f.eval x := by
  simp [difference, taylor_apply, Polynomial.eval_comp]

/-- The leading term cancels and the next term retains its exact
degree, leading coefficient and step. -/
theorem difference_coeff {f : ℤ[X]} {n : ℕ} (hf : f.natDegree = n + 1) (h : ℤ) :
    (difference h f).coeff n = (n + 1) * f.leadingCoeff * h := by
  have hd : (hasseDeriv n f).natDegree ≤ 1 := by
    simpa only [hf, Nat.add_sub_cancel_left] using natDegree_hasseDeriv_le f n
  rw [difference, coeff_sub, taylor_coeff,
    eq_X_add_C_of_natDegree_le_one hd]
  simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff,
    zero_add, Nat.choose_self, Nat.cast_one, one_mul]
  have hc : f.coeff (n + 1) = f.leadingCoeff := by simpa only [hf] using f.coeff_natDegree
  rw [show 1 + n = n + 1 by omega, Nat.choose_succ_self_right, hc]
  push_cast
  ring

/-- Cancelling the top coefficient lowers the actual polynomial degree. -/
theorem difference_natDegree_le {f : ℤ[X]} {n : ℕ}
    (hf : f.natDegree = n + 1) (h : ℤ) : (difference h f).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  by_cases hin : i = n + 1
  · subst i
    simp only [difference, coeff_sub, ← hf, coeff_taylor_natDegree,
      coeff_natDegree, sub_self]
  · have hfi : f.natDegree < i := by omega
    have hti : (taylor h f).natDegree < i := by simpa using hfi
    simp only [difference, coeff_sub, coeff_eq_zero_of_natDegree_lt hfi,
      coeff_eq_zero_of_natDegree_lt hti, sub_self]

/-- A nonzero integer step lowers degree by exactly one, with no loss
from a generic degree upper bound. -/
theorem difference_degree_leading {f : ℤ[X]} {n : ℕ}
    (hf : f.natDegree = n + 1) {h : ℤ} (hh : h ≠ 0) :
    (difference h f).natDegree = n ∧
      (difference h f).leadingCoeff = (n + 1) * f.leadingCoeff * h := by
  have hcoeff : (difference h f).coeff n ≠ 0 := by
    rw [difference_coeff hf]
    apply mul_ne_zero (mul_ne_zero (by omega) ?_) hh
    apply leadingCoeff_ne_zero.mpr
    intro hz
    rw [hz, natDegree_zero] at hf
    omega
  have hd := (difference_natDegree_le hf h).antisymm (le_natDegree_of_ne_zero hcoeff)
  exact ⟨hd, by rw [leadingCoeff, hd, difference_coeff hf]⟩

/-- The first linear coordinate becomes a constant, so its two-sided
moment equation cancels exactly when the next type is formed. -/
theorem difference_linear_constant {f : ℤ[X]} (hf : f.natDegree = 1) (h : ℤ) :
    difference h f = C (f.leadingCoeff * h) := by
  have hd := difference_natDegree_le (n := 0) hf h
  rw [eq_C_of_natDegree_le_zero hd, difference_coeff (n := 0) hf]
  simp

/-- A common input translation leaves the type and every leading
coefficient unchanged. -/
theorem hasType_translate {m d T e : ℕ} {F : Fin m → ℤ[X]}
    (hF : HasType F d T e) (c : ℤ) : HasType (fun j => taylor c (F j)) d T e := by
  intro j
  simpa only [natDegree_taylor, leadingCoeff_taylor] using hF j

/-- After the constant first difference is removed, all remaining
polynomials form the next type with the literal multiplier `h*T`. -/
theorem hasType_difference {m d T e h : ℕ} {F : Fin (m + 1) → ℤ[X]}
    (hF : HasType F d T e) (hh : 1 ≤ h) :
    HasType (fun j : Fin m => difference (h : ℤ) (F j.succ)) (d + 1) (h * T) e := by
  intro j
  have he := difference_degree_leading (n := j.val + 1) (h := (h : ℤ)) (hF j.succ).1
    (by exact_mod_cast (show h ≠ 0 by omega))
  refine ⟨he.1, ?_⟩
  rw [he.2, (hF j.succ).2]
  simp only [Fin.val_succ, Nat.descFactorial_succ, Nat.cast_mul]
  have hd : d + 1 + j.val + 1 - d = j.val + 2 := by omega
  have hi : d + (j.val + 1) + 1 = d + 1 + j.val + 1 := by omega
  rw [hd, hi]
  push_cast
  ring

/-- The new type parameter stays within the exact interval used by
the differencing step; it is not an unspecified coefficient cost. -/
theorem difference_type_parameter {h P T : ℕ} (hh : 1 ≤ h) (hP : h ≤ P) :
    T ≤ h * T ∧ h * T ≤ P * T := by
  constructor
  · simpa using Nat.mul_le_mul_right T hh
  · exact Nat.mul_le_mul_right T hP

/-- Every positive-parameter type is a regular triangular integer
system, including arbitrarily large lower coefficients. -/
theorem regularTriangular_of_hasType {m d T e : ℕ} {F : Fin m → ℤ[X]}
    (hF : HasType F d T e) (hT : 1 ≤ T) : RegularTriangular F := by
  intro j
  refine ⟨(hF j).1.le, ?_⟩
  have hc : (F j).coeff (j.val + 1) =
      ((d + j.val + 1).descFactorial d : ℤ) * 2 ^ e * T := by
    rw [← (hF j).1, coeff_natDegree, (hF j).2]
  rw [hc]
  apply (IsRegular.of_ne_zero ?_).left
  have hfac : (0 : ℤ) < (d + j.val + 1).descFactorial d := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : d ≤ d + j.val + 1))
  have hTZ : (0 : ℤ) < T := by exact_mod_cast (show 0 < T by omega)
  positivity

/-- The active polynomial torus integral is exactly the literal
Vinogradov moment of degree `m`, uniformly in every type parameter. -/
theorem type_interval_moment_eq {m d T e : ℕ} {F : Fin m → ℤ[X]}
    (hF : HasType F d T e) (hT : 1 ≤ T) (s X : ℕ) :
    moment s (fun i : Fin X => polynomialFrequency F (i.val + 1)) =
      meanValue s m X := by
  rw [moment_eq_monomial F (regularTriangular_of_hasType hF hT)]
  rfl

/-- The diagonal integer moment bound has no loss from the degree,
size, translation or preceding differences of a type system. -/
theorem type_interval_moment_le {m d T e : ℕ} {F : Fin m → ℤ[X]}
    (hF : HasType F d T e) (hT : 1 ≤ T) (s X : ℕ) :
    moment s (fun i : Fin X => polynomialFrequency F (i.val + 1)) ≤
      (X : ℝ) ^ (2 * s - min s m) * (min s m).factorial := by
  rw [type_interval_moment_eq hF hT]
  exact VinogradovPowerSumRigidity.meanValue_le_all s m X

/-- The excluded primes are exactly the possible prime divisors of the
type's leading factors. Primes larger than the full degree only need the
additional check `p ∤ T`. -/
theorem type_leading_unit {p m d T e : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (n : ℕ) (j : Fin m) :
    IsUnit (((F j).leadingCoeff : ℤ) : ZMod (p ^ n)) := by
  have hp : p.Prime := Fact.out
  have hfac : ¬p ∣ (d + j.val + 1).descFactorial d := by
    intro h
    have hfull : p ∣ (d + j.val + 1).factorial := by
      rw [← Nat.factorial_mul_descFactorial (by omega : d ≤ d + j.val + 1)]
      exact dvd_mul_of_dvd_right h _
    have := hp.dvd_factorial.mp hfull
    omega
  have htwo : ¬p ∣ 2 := by
    intro h
    have := Nat.le_of_dvd (by omega : 0 < 2) h
    omega
  have hprod : ¬p ∣ (d + j.val + 1).descFactorial d * 2 ^ e * T := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · exact hfac h
      · exact htwo (hp.dvd_of_dvd_pow h)
    · exact hpT h
  have hcop : ((d + j.val + 1).descFactorial d * 2 ^ e * T).Coprime p :=
    (hp.coprime_iff_not_dvd.mpr hprod).symm
  have hu := (ZMod.isUnit_iff_coprime _ (p ^ n)).mpr (hcop.pow_right n)
  simpa only [(hF j).2, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    Int.cast_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hu

/-- Every eligible prime keeps the full type triangular at every
precision, including after arbitrary preceding translations. -/
theorem type_modular_regular {p m d T e : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (n : ℕ) :
    RegularTriangular (fun j => (F j).map (Int.castRingHom (ZMod (p ^ n)))) := by
  apply regularTriangular_map F (Int.castRingHom (ZMod (p ^ n)))
    (fun j => (hF j).1.le)
  intro j
  change IsUnit (((F j).coeff (j.val + 1) : ℤ) : ZMod (p ^ n))
  rw [← (hF j).1, coeff_natDegree]
  exact type_leading_unit hpdeg hp2 hpT hF n j

/-- The actual complete nonsingular fibre for a Ford-type system costs
at most the factorial of its active degree. All type and prime hypotheses
are discharged explicitly; no generic fibre bound is assumed. -/
theorem type_nonsingular_fibre_le {p m d T e : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (n : ℕ)
    (target : Fin m → ZMod (p ^ n)) :
    (Finset.univ.filter (fun u : Fin m → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      (∑ j, polynomialFrequency
        (fun l => (F l).map (Int.castRingHom (ZMod (p ^ n))))
        ((u j).val : ZMod (p ^ n))) = target)).card ≤ m.factorial := by
  apply nonsingular_polynomial_fibre_le (by omega)
  exact type_modular_regular hpdeg hp2 hpT hF n

/-- The precise loss from completing the type's degree moduli to
precision `r` is the triangular number `(r-d)*(r-d-1)/2`. -/
theorem type_precision_cost {m d r : ℕ} (hr : r ≤ d + m) :
    (∑ i : Fin m, (r - min (d + i.val + 1) r)) =
      (r - d) * (r - d - 1) / 2 := by
  have hterm (i : ℕ) : r - min (d + i + 1) r = (r - d) - (i + 1) := by omega
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun i => (r - d) - (i + 1)) m]
  have hmr : r - d ≤ m := by omega
  have hs : (∑ i ∈ Finset.range m, ((r - d) - (i + 1))) =
      ∑ i ∈ Finset.range (r - d), ((r - d) - (i + 1)) := by
    conv_lhs => rw [← Nat.add_sub_of_le hmr, Finset.sum_range_add]
    have hz : (∑ i ∈ Finset.range (m - (r - d)),
        ((r - d) - (r - d + i + 1))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      omega
    rw [hz, add_zero]
  rw [hs]
  simp_rw [Nat.add_comm _ 1, Nat.sub_add_eq]
  rw [Finset.sum_range_reflect (fun i => i) (r - d), Finset.sum_range_id]

/-- The type system satisfies the degree-specific congruence count
used in classical conditioning, with its full explicit factorial and
triangular prime power. This is a proved count of the actual polynomial
congruences, not an assumed fibre estimate. -/
theorem type_degree_moduli_card_le {p m d T e r : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T) (hr : r ≤ d + m)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (a : Fin m → ℕ) :
    (Finset.univ.filter (fun u : Fin m → Fin (p ^ r) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      ∀ i, (∑ j, ((F i).map (Int.castRingHom (ZMod (p ^ r)))).eval
        ((u j).val : ZMod (p ^ r))).val % p ^ min (d + i.val + 1) r = a i)).card ≤
      p ^ ((r - d) * (r - d - 1) / 2) * m.factorial := by
  have h := polynomial_anisotropic_card_le (by omega : m < p)
    (fun i => (F i).map (Int.castRingHom (ZMod (p ^ r))))
    (type_modular_regular hpdeg hp2 hpT hF r)
    (fun i => min (d + i.val + 1) r) (fun _ => Nat.min_le_right _ _) a
  simpa only [type_precision_cost hr] using h

/-- The completed count applies directly to the literal integer
polynomial congruences, with the original degree-specific moduli. -/
theorem type_integer_congruence_card_le {p m d T e r : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T) (hr : r ≤ d + m)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (a : Fin m → ℤ) :
    (Finset.univ.filter (fun u : Fin m → Fin (p ^ r) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      ∀ i, (p : ℤ) ^ min (d + i.val + 1) r ∣
        (∑ j, (F i).eval ((u j).val : ℤ)) - a i)).card ≤
      p ^ ((r - d) * (r - d - 1) / 2) * m.factorial := by
  classical
  have hp := (Fact.out : p.Prime).pos
  have : NeZero (p ^ r) := ⟨ne_of_gt (pow_pos hp r)⟩
  apply le_trans (Finset.card_le_card ?_)
    (type_degree_moduli_card_le hpdeg hp2 hpT hr hF
      (fun i => (a i : ZMod (p ^ min (d + i.val + 1) r)).val))
  intro u hu
  obtain ⟨huprime, hueq⟩ := (Finset.mem_filter.mp hu).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, huprime, ?_⟩
  intro i
  have hmap : (∑ j, ((F i).map (Int.castRingHom (ZMod (p ^ r)))).eval
      ((u j).val : ZMod (p ^ r))) =
      ((∑ j, (F i).eval ((u j).val : ℤ) : ℤ) : ZMod (p ^ r)) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using
      (Polynomial.eval_map_apply (p := F i) (Int.castRingHom (ZMod (p ^ r))) ((u j).val : ℤ))
  rw [hmap, VinogradovCoarseCongruence.intCast_reduction_val
    (pow_dvd_pow p (Nat.min_le_right _ _))]
  apply congrArg ZMod.val
  symm
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
  simpa only [Nat.cast_pow] using hueq i

/-- Ordinary monomials provide the actual starting type. -/
theorem monomial_hasType (m : ℕ) :
    HasType (fun j : Fin m => (X : ℤ[X]) ^ (j.val + 1)) 0 1 0 := by
  intro j
  simp

end
end RiemannGaussian.VinogradovPolynomialSystems

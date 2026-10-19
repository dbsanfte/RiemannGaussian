/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Moments.AmplificationLocal
import OAI.NumberTheory.DirichletL.Detector.PhysicalCRT
import OAI.NumberTheory.DirichletL.CubicSieve.Gcd
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
Actual finite sextic Gauss support at a unit times a squarefree-root square.
The local surviving cube is a quadratic Gauss lift. No theta, residue, source,
or physical-energy estimate is asserted.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.FiniteSquareGauss
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss
open OAI.SevenEighths OAI.SevenEighths.ProbePhysical
open OAI.SevenEighths.ProbePrimePower OAI.CanonicalQuadraticSieve
open OAI.SevenEighths.CenteredMomentUnequal
open OAI.SevenEighths.CenteredMomentAmplification
open OAI.SevenEighths.CenteredMomentAmplificationLocal
open OAI.ConcretePrimeRowBridge OAI.CanonicalRowCompletion
local notation "O" => OAI.ActualEisensteinCubic.O

/-- Actual sextic prime-power table at numerator valuation two. -/
theorem gauss_prime_power_square (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n : ℕ) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (p^2) =
      if n=2 then (Ideal.absNorm (Ideal.span {p}) : ℂ)^2 *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ 3) 1 else 0 := by
  rw [sexticGauss_prime_power p hp hg, actualSextic_primePowerGauss_at_pow p hp hg hc]
  by_cases hn : n=2
  · subst n
    norm_num
  · rw [ite_eq_right hn]
    by_cases hd : 6 ∣ n+1
    · have hlarge : 2<n := by omega
      simp only [hd, ite_true, show ¬ n+1≤2 by omega, show ¬ n≤2 by omega,
        ite_false, sub_self]
    · simp only [hd, ite_false, show ¬ 2=n from Ne.symm hn]

/-- A unit multiplier does not alter the zero/nonzero local Gauss support. -/
theorem gauss_prime_power_unit_nonzero_iff (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (n : ℕ) (u h : O) (hup : ¬ p ∣ u) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (u*h) ≠ 0 ↔
      sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) h ≠ 0 := by
  have hn := gauss_unit_scale_norm (p^(n+1)) (supported_power p hs (n+1)) u h
    ((hp.irreducible.coprime_iff_not_dvd.mpr hup).symm.pow_right)
  exact (norm_ne_zero_iff.symm.trans (hn ▸ norm_ne_zero_iff))

/-- A prime dividing a squarefree root occurs once, with coprime cofactor. -/
theorem squarefree_prime_factor (p a : O) (hp : Prime p) (ha : Squarefree a)
    (hpa : p ∣ a) : ∃ u, a=p*u ∧ ¬p∣u := by
  obtain ⟨u, rfl⟩ := hpa
  refine ⟨u, rfl, ?_⟩
  intro hpu
  apply hp.not_isUnit
  apply ha p
  exact mul_dvd_mul_left p hpu

/-- Exact actual local support: for sf root a, only physical exponent one or
three survives, according as the physical prime does not or does divide a. -/
theorem squarefree_root_local_support (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (a ζ : O) (ha : Squarefree a) (hζ : IsUnit ζ) (n : ℕ)
    (hG : sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (ζ*a^2) ≠ 0) :
    n = if p∣a then 2 else 0 := by
  have hpζ : ¬p∣ζ := fun h => hp.not_isUnit (isUnit_of_dvd_unit h hζ)
  by_cases hpa : p∣a
  · rw [ite_eq_left hpa]
    obtain ⟨u, hu, hpu⟩ := squarefree_prime_factor p a hp ha hpa
    have hmul : ζ*a^2=(ζ*u^2)*(p^2) := by rw [hu]; ring
    have hunit : ¬p∣ζ*u^2 := by
      intro h
      rcases hp.dvd_mul.mp h with h | h
      · exact hpζ h
      · exact hpu (hp.dvd_of_dvd_pow h)
    rw [hmul] at hG
    have hbase := (gauss_prime_power_unit_nonzero_iff p hp hs n (ζ*u^2) (p^2) hunit).mp hG
    rw [gauss_prime_power_square p hp hg hc] at hbase
    by_contra hn
    exact hbase (ite_eq_right hn)
  · rw [ite_eq_right hpa]
    have hunit : ¬p∣ζ*a^2 := by
      intro h
      rcases hp.dvd_mul.mp h with h | h
      · exact hpζ h
      · exact hpa (hp.dvd_of_dvd_pow h)
    have hbase := (gauss_prime_power_unit_nonzero_iff p hp hs n (ζ*a^2) 1 hunit).mp
      (by simpa only [mul_one] using hG)
    rw [gauss_prime_power_one p hp hg hc] at hbase
    by_contra hn
    exact hbase (ite_eq_right hn)

/-- The actual full prime-power table after any coprime multiplier. This
retains every numerator valuation and the exponent-six principal branch. -/
theorem gauss_prime_power_unit_at_pow (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n j : ℕ) (u : O) (hup : ¬ p ∣ u) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (u*p^j) =
      (idealRowHom u (Ideal.span {p^(n+1)}))⁻¹ *
        (if 6∣n+1 then
          (if n+1≤j then (Ideal.absNorm (Ideal.span {p}) : ℂ)^(n+1) else 0) -
          (if n≤j then (Ideal.absNorm (Ideal.span {p}) : ℂ)^n else 0)
        else if j=n then (Ideal.absNorm (Ideal.span {p}) : ℂ)^n *
          primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^(n+1)) 1 else 0) := by
  rw [sexticGauss_unit_scale _ (supported_power p hs (n+1)) u (p^j)
    ((hp.irreducible.coprime_iff_not_dvd.mpr hup).symm.pow_right),
    sexticGauss_prime_power p hp hg, actualSextic_primePowerGauss_at_pow p hp hg hc]

/-- Necessary support for arbitrary numerator valuation; imprimitive
principal sixth-power physical rows require only n≤j, not equality. -/
theorem gauss_prime_power_unit_support (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n j : ℕ) (u : O) (hup : ¬ p ∣ u)
    (hG : sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (u*p^j) ≠ 0) :
    if 6∣n+1 then n≤j else j=n := by
  have hb := (gauss_prime_power_unit_nonzero_iff p hp hs n u (p^j) hup).mp hG
  rw [sexticGauss_prime_power p hp hg, actualSextic_primePowerGauss_at_pow p hp hg hc] at hb
  by_cases hd : 6∣n+1
  · rw [ite_eq_left hd]
    by_contra hn
    have hn' : ¬ n+1≤j := by omega
    simp only [hd, ite_true, hn, hn', ite_false, sub_self, ne_eq, not_true_eq_false] at hb
  · rw [ite_eq_right hd]
    by_contra hn
    simp only [hd, ite_false, hn, ne_eq, not_true_eq_false] at hb

/-- Squaring a unit modulo d does not change the ACTUAL Gauss sum at d³.
No squarefree condition on d and no coprimality with another column is used. -/
theorem gauss_cube_square_invariant (d : O) (hd : Supported (Ideal.span {d}))
    (u h : O) (hcop : IsCoprime u d) :
    sexticGauss (d^3) (pow_ne_zero _ (supportedElement_ne_zero d hd)) (h*u^2) =
      sexticGauss (d^3) (pow_ne_zero _ (supportedElement_ne_zero d hd)) h := by
  have hv : idealRowHom (u^2) (Ideal.span {d^3})=1 := by
    rw [← Ideal.span_singleton_pow, map_pow, idealRowHom_argument_pow u 2 _ hd, ← pow_mul]
    norm_num only [show (2:ℕ)*3=6 by decide]
    rw [← idealRowHom_argument_pow u 6 _ hd, supported_sixth_value d u hd hcop.symm]
  rw [show h*u^2=u^2*h by ring,
    sexticGauss_unit_scale _ (supported_power d hd 3) (u^2) h hcop.pow_left.pow_right,
    hv, inv_one, one_mul]

end OpenAIReview.FiniteSquareGauss
#lint+ in OpenAIReview.FiniteSquareGauss

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
  unless declarations > 0 do throwError "Empty finite square Gauss audit."
  logInfo m!"Finite square Gauss audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-finite-square-gauss"
  IO.FS.writeFile ".lake/arithmetic-operator-finite-square-gauss/axioms.json"
    (Json.mkObj [("scope", toJson "actual finite sextic Gauss squarefree-root local support; no theta/source/energy estimate"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true), ("declarations", toJson declarations),
      ("theoremsIncludingHelpers", toJson theorems), ("details", Json.arr details)]).pretty

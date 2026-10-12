/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGrowingRamanujan
import RiemannGaussian.ArithmeticOperatorGammaTwistAudit

/-!
# Full-scale growing prime-modulus codes reconstruct the original source

For a prime modulus p, (c_p(n)+1)/p is exactly the divisor indicator.
The complete finite code including the unit modulus has zero common
coprime coefficient. Nevertheless, when its moduli include every prime
through the physical cutoff, its actual Mangoldt observation is exactly
the original one, with every phase, mask and proper power retained.

Thus large-modulus principal centering alone has NOT separated the
density pole: the growing exceptional population restores both pole and
zero source. This freezes this normalized prime-modulus prototype, not
nonprincipal characters, other residue codes, or all intermediate scales.
-/

namespace RiemannGaussian.ArithmeticOperatorFullRamanujanAudit
noncomputable section
open Complex ArithmeticOperatorRamanujanAudit SuzukiCarryCorrelation
open Filter ArithmeticOperatorGammaTwistAudit
open scoped BigOperators Topology

/-- A finite normalized prime-modulus correction, before any prime
measure or physical test kernel is applied. -/
def normalizedCode (Q : Finset ℕ) (n : ℕ) : ℂ :=
  ∑ p ∈ Q, ((ramanujanDivisor p n : ℂ)+1)/(p : ℂ)

/-- Unit-modulus coefficient is retained rather than silently discarded. -/
def coefficients (Q : Finset ℕ) (q : ℕ) : ℂ :=
  if q = 1 then ∑ p ∈ Q, (p : ℂ)⁻¹ else (q : ℂ)⁻¹

theorem ramanujanDivisor_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ramanujanDivisor p n = if p ∣ n then (p : ℤ)-1 else -1 := by
  by_cases hd : p ∣ n
  · rw [ite_eq_left hd, ramanujanDivisor, Nat.gcd_eq_left_iff_dvd.mpr hd, hp.divisors]
    simp [hp.ne_one.symm, Nat.div_self hp.pos, ArithmeticFunction.moebius_apply_prime hp]
    ring
  · rw [ite_eq_right hd, ramanujanDivisor_of_coprime (hp.coprime_iff_not_dvd.mpr hd),
      ArithmeticFunction.moebius_apply_prime hp]

/-- The full integer indicator, at every endpoint and every label. -/
theorem normalizedCode_eq_indicators {Q : Finset ℕ}
    (hQ : ∀ p ∈ Q, p.Prime) (n : ℕ) :
    normalizedCode Q n = ∑ p ∈ Q, if p ∣ n then (1 : ℂ) else 0 := by
  unfold normalizedCode
  apply Finset.sum_congr rfl
  intro p hp
  rw [ramanujanDivisor_prime (hQ p hp)]
  split_ifs <;> push_cast <;> simp [(hQ p hp).ne_zero]

/-- This is an actual code in the earlier divisor-form convention;
the unit modulus supplies exactly its finite centering coefficient. -/
theorem code_eq_normalized {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) (n : ℕ) :
    code (insert 1 Q) (coefficients Q) n = normalizedCode Q n := by
  have h1 : 1 ∉ Q := fun hh => (hQ 1 hh).ne_one rfl
  unfold code
  rw [Finset.sum_insert h1]
  simp only [coefficients, ite_true]
  have hr : ramanujanDivisor 1 n = 1 := by simp [ramanujanDivisor]
  rw [hr]
  simp only [Int.cast_one, mul_one]
  have he : (∑ p ∈ Q, (if p = 1 then ∑ p ∈ Q, (p : ℂ)⁻¹ else (p : ℂ)⁻¹)*
      (ramanujanDivisor p n : ℂ)) = ∑ p ∈ Q, (p : ℂ)⁻¹*(ramanujanDivisor p n : ℂ) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [ite_eq_right (hQ p hp).ne_one]
  rw [he, ← Finset.sum_add_distrib]
  unfold normalizedCode
  apply Finset.sum_congr rfl
  intro p _
  rw [div_eq_mul_inv]
  ring

/-- Common coprime coefficient vanishes exactly, despite the full-scale
observation below still retaining the entire ordinary density. -/
theorem principalCoefficient_eq_zero {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) :
    principalCoefficient (insert 1 Q) (coefficients Q) = 0 := by
  have h1 : 1 ∉ Q := fun hh => (hQ 1 hh).ne_one rfl
  unfold principalCoefficient
  rw [Finset.sum_insert h1]
  simp only [coefficients, ite_true, ArithmeticFunction.moebius_apply_one,
    Int.cast_one, mul_one]
  have he : (∑ p ∈ Q, (if p = 1 then ∑ p ∈ Q, (p : ℂ)⁻¹ else (p : ℂ)⁻¹)*
      (ArithmeticFunction.moebius p : ℂ)) = -∑ p ∈ Q, (p : ℂ)⁻¹ := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [ite_eq_right (hQ p hp).ne_one, ArithmeticFunction.moebius_apply_prime (hQ p hp)]
    simp
  rw [he, add_neg_cancel]

/-- Proper powers share precisely their one base-prime channel. -/
theorem normalizedCode_prime_pow {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime)
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    normalizedCode Q (p^k) = if p ∈ Q then 1 else 0 := by
  rw [normalizedCode_eq_indicators hQ]
  have hd {q : ℕ} (hq : q ∈ Q) : q ∣ p^k ↔ q = p := by
    constructor
    · intro hh
      have he := (Nat.dvd_prime hp).mp ((hQ q hq).dvd_of_dvd_pow hh)
      exact he.resolve_left (hQ q hq).ne_one
    · intro he
      rw [he]
      exact dvd_pow_self p hk.ne'
  have he : (∑ q ∈ Q, if q ∣ p^k then (1 : ℂ) else 0) =
      ∑ q ∈ Q, if q = p then (1 : ℂ) else 0 := by
    exact Finset.sum_congr rfl (fun q hq => by simp only [hd hq])
  rw [he, Finset.sum_ite_eq']

/-- The literal increasing ordinary-prime modulus set. -/
def primesThrough (X : ℕ) : Finset ℕ := (Finset.Icc 1 X).filter Nat.Prime

/-- Native finite code observation with ANY physical mask, phase and
factorial kernel w retained. Every proper prime power is included. -/
def nativeObservation (Q : Finset ℕ) (X : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*w n*normalizedCode Q n

/-- Every actual prime power below the cutoff is restored exactly. -/
theorem mangoldt_mul_normalizedCode_eq {X n : ℕ} (hn : n ≤ X) :
    (ArithmeticFunction.vonMangoldt n : ℂ)*normalizedCode (primesThrough X) n =
      (ArithmeticFunction.vonMangoldt n : ℂ) := by
  by_cases hz : ArithmeticFunction.vonMangoldt n = 0
  · simp [hz]
  · obtain ⟨p,k,hp,hk,he⟩ := (isPrimePow_nat_iff n).mp
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hz)
    have hpN : p ≤ n := by rw [← he]; exact Nat.le_self_pow hk.ne' p
    have hpQ : p ∈ primesThrough X := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp.one_le, hpN.trans hn⟩,hp⟩
    have hc := normalizedCode_prime_pow (Q := primesThrough X)
      (fun _ hq => (Finset.mem_filter.mp hq).2) hp hk
    rw [he, ite_eq_left hpQ] at hc
    rw [hc, mul_one]

/-- At full scale centering has merely relabeled the original literal
prime sum. It cancels neither its density nor its zero-mode source. -/
theorem native_full_eq_original (X : ℕ) (w : ℕ → ℂ) :
    nativeObservation (primesThrough X) X w =
      ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*w n := by
  unfold nativeObservation
  apply Finset.sum_congr rfl
  intro n hn
  calc
    _ = w n*((ArithmeticFunction.vonMangoldt n : ℂ)*normalizedCode (primesThrough X) n) := by ring
    _ = w n*(ArithmeticFunction.vonMangoldt n : ℂ) := by
      rw [mangoldt_mul_normalizedCode_eq (Finset.mem_Icc.mp hn).2]
    _ = _ := mul_comm _ _

/-- The explicitly principal-centered original code has exactly the
same full-scale prime response; centering is not density cancellation. -/
theorem full_centered_code_eq_original (X : ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*w n*
      code (insert 1 (primesThrough X)) (coefficients (primesThrough X)) n) =
        ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*w n := by
  have hQ : ∀ p ∈ primesThrough X, p.Prime := fun _ hp => (Finset.mem_filter.mp hp).2
  simp_rw [code_eq_normalized hQ]
  exact native_full_eq_original X w

/-- Coefficient of the complete increasing code; no infinite Ramanujan
expansion or exchange of growing-modulus limits is assumed. -/
def fullCoefficient (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ)*normalizedCode (primesThrough n) n

theorem fullCoefficient_eq_mangoldt (n : ℕ) :
    fullCoefficient n = (ArithmeticFunction.vonMangoldt n : ℂ) :=
  mangoldt_mul_normalizedCode_eq le_rfl

/-- Genuine Euler identity: both the original zeta pole and all zero
sources remain. Common coprime centering did not cancel this density. -/
theorem full_euler_response {s : ℂ} (hs : 1 < s.re) (y : ℝ) :
    LSeries (fun n => fullCoefficient n*primePhase y n) s =
      -logDeriv riemannZeta (s+I*y) := by
  simp_rw [fullCoefficient_eq_mangoldt]
  rw [LSeries_primePhase,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs)]
  rw [logDeriv_apply, neg_div]

/-- The restored matched zero response has its original nonzero
multiplicity. This is the SAME source, not independent arithmetic input. -/
theorem tendsto_restored_zero_source (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*(-logDeriv riemannZeta s))
      (𝓝[≠] rho.1) (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have ht := (AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)).neg
  simp only [analyticZetaZeroMultiplicity]
  convert ht using 1
  funext s
  ring

theorem restored_source_ne_zero (rho : NontrivialZetaZero) :
    -(analyticZetaZeroMultiplicity rho : ℂ) ≠ 0 := by
  exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr
    (Nat.ne_of_gt (analyticZetaZeroMultiplicity_positive rho)))

end
end RiemannGaussian.ArithmeticOperatorFullRamanujanAudit
